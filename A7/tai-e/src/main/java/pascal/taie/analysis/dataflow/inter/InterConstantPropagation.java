/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InvokeDynamic;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;

import java.util.List;


/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private MultiMap<StoreField, LoadField> fieldStoreToLoads;
    private MultiMap<StoreArray, LoadArray> arrayStoreToLoads;
    private MultiMap<LoadArray, StoreArray> arrayLoadToStores;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        fieldStoreToLoads = Maps.newMultiMap();

        // collect static loads and stores
        MultiMap<JField, StoreField> staticStores = Maps.newMultiMap();
        MultiMap<JField, LoadField> staticLoads = Maps.newMultiMap();
        for (Stmt s : icfg) {
            if (s instanceof StoreField store) {
                if (store.isStatic() && holdsInt(store.getRValue())) {
                    staticStores.put(store.getFieldRef().resolve(), store);
                }
            }
            if (s instanceof LoadField load) {
                if (load.isStatic() && holdsInt(load.getLValue())) {
                    staticLoads.put(load.getFieldRef().resolve(), load);
                }
            }
        }
        staticStores.forEach((field, store) -> {
            staticLoads.get(field).forEach(load -> {
                fieldStoreToLoads.put(store, load);
            });
        });

        // collect instance loads and stores
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);
        MultiMap<Obj, Var> pointBy = Maps.newMultiMap();

        pta.getVars()
                .stream()
                .filter(v -> !isEmpty(v))
                .forEach(v -> pta.getPointsToSet(v).forEach(p -> pointBy.put(p, v)));

        arrayLoadToStores = Maps.newMultiMap();
        arrayStoreToLoads = Maps.newMultiMap();
        pointBy.forEachSet((__, aliases) -> {
            aliases.forEach(v -> {
                // for each instance field store, find all loads and store in fieldStoreToLoads
                for (StoreField store : v.getStoreFields()) {
                    if (!store.isStatic() && holdsInt(store.getRValue())) {
                        JField storeField = store.getFieldRef().resolve();
                        aliases.forEach(alias -> {
                            for (LoadField load : alias.getLoadFields()) {
                                JField loadField = load.getFieldRef().resolve();
                                if (loadField.equals(storeField)) {
                                    fieldStoreToLoads.put(store, load);
                                }
                            }
                        });
                    }
                }
                // for each instance array store, find all loads and store as Bidirectional Mapping
                for (StoreArray store : v.getStoreArrays()) {
                    if (holdsInt(store.getRValue())) {
                        aliases.forEach(alias -> {
                            alias.getLoadArrays().forEach(load -> {
                                arrayStoreToLoads.put(store, load);
                                arrayLoadToStores.put(load, store);
                            });
                        });
                    }
                }
            });
        });
    }

    boolean isEmpty(Var v) {
        return v.getStoreFields().isEmpty()
                && v.getLoadFields().isEmpty()
                && v.getStoreArrays().isEmpty()
                && v.getLoadArrays().isEmpty();
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        return out.copyFrom(in);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        return transferAliasAware(stmt, in, out);
    }

    protected boolean transferAliasAware(Stmt stmt, CPFact in, CPFact out) {
        return stmt.accept(new StmtVisitor<>() {
            @Override
            public Boolean visit(LoadField load) {
                var changed = false;
                var lhs = load.getLValue();
                for (var inVar : in.keySet()) {
                    if (!inVar.equals(lhs)) {
                        changed |= out.update(inVar, in.get(inVar));
                    }
                }
                return changed;
            }

            @Override
            public Boolean visit(StoreField store) {
                // for every instance store if value changed propagate to all loads
                var var = store.getRValue();
                var value = in.get(var);
                fieldStoreToLoads.get(store).forEach(load -> {
                    var lhs = load.getLValue();
                    var loadOut = solver.getOutFact(load);
                    var oldValue = loadOut.get(lhs);
                    var newValue = cp.meetValue(oldValue, value);
                    if (loadOut.update(lhs, newValue)) {
                        solver.propagate(load);
                    }
                });

                return cp.transferNode(store, in, out);
            }

            private Boolean transferLoadArray(StoreArray store, LoadArray load) {
                // store a[i] = x
                // load y = a[j]
                // get i j a[i] a[j] meet then with array rule
                var i = store.getArrayAccess().getIndex();
                var j = load.getArrayAccess().getIndex();
                CPFact storeOut = solver.getOutFact(store);
                CPFact loadOut = solver.getOutFact(load);
                var vi = storeOut.get(i);
                var vj = loadOut.get(j);
                if (!vi.isUndef() && !vj.isUndef()) {
                    if ((vi.isConstant() && vj.isConstant() && vi.equals(vj)) || vi.isNAC() || vj.isNAC()) {
                        var x = store.getRValue();
                        var vx = storeOut.get(x);
                        var y = load.getLValue();
                        var oldVy = loadOut.get(y);
                        var newVy = cp.meetValue(oldVy, vx);
                        return loadOut.update(y, newVy);
                    }
                }
                return false;
            }

            @Override
            public Boolean visit(LoadArray load) {
                boolean changed = false;
                // x = a[i]
                var lhs = load.getLValue();
                for (var inVar : in.keySet()) {
                    if (!inVar.equals(lhs)) {
                        changed |= out.update(inVar, in.get(inVar));
                    }
                }
                for (var store : arrayLoadToStores.get(load)) {
                    changed |= transferLoadArray(store, load);
                }
                return changed;
            }

            @Override
            public Boolean visit(StoreArray store) {
                arrayStoreToLoads.get(store).forEach(load->{
                    if(transferLoadArray(store, load)) {
                        solver.propagate(load);
                    }
                });
                return  cp.transferNode(store, in, out);
            }

            @Override
            public Boolean visitDefault(Stmt stmt) {
                return cp.transferNode(stmt, in, out);
            }
        });

    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        var cpOut = out.copy();
        var call = edge.getSource();
        var def = call.getDef();
        if (def.isPresent() && def.get() instanceof Var defVar && holdsInt(defVar)) {
            cpOut.remove(defVar);
        }
        return cpOut;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // Passing arguments at call site to parameters of the callee
        InvokeExp invokeExp = ((Invoke) edge.getSource()).getInvokeExp();
        JMethod callee = edge.getCallee();
        CPFact result = newInitialFact();
        if (!(invokeExp instanceof InvokeDynamic) &&
                invokeExp.getMethodRef().getSubsignature()
                        .equals(callee.getSubsignature())) {
            List<Var> args = invokeExp.getArgs();
            List<Var> params = callee.getIR().getParams();
            for (int i = 0; i < args.size(); ++i) {
                Var arg = args.get(i);
                Var param = params.get(i);
                if (holdsInt(param)) {
                    Value argValue = callSiteOut.get(arg);
                    result.update(param, argValue);
                }
            }
        }
        return result;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        var cpFact = new CPFact();
        var invoke = (Invoke) edge.getCallSite();
        var defVar = invoke.getLValue();
        if (defVar != null && holdsInt(defVar)) {
            var returnVars = edge.getReturnVars();
            Value returnValue = Value.getUndef();
            for (var returnVar : returnVars) {
                var value = returnOut.get(returnVar);
                returnValue = cp.meetValue(returnValue, value);
            }
            cpFact.update(defVar, returnValue);
        }
        return cpFact;
    }

    boolean holdsInt(Var var) {
        return ConstantPropagation.canHoldInt(var);
    }
}
