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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if (callGraph.addReachableMethod(method)) {
            method.getIR().getStmts().forEach(stmt -> stmt.accept(stmtProcessor));
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(New stmt) {
            var varPtr = pointerFlowGraph.getVarPtr(stmt.getLValue());
            var pts = new PointsToSet(heapModel.getObj(stmt));
            workList.addEntry(varPtr, pts);
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            // x = y
            // add pfg add x <- y
            addPFGEdge(
                    pointerFlowGraph.getVarPtr(stmt.getRValue()),
                    pointerFlowGraph.getVarPtr(stmt.getLValue())
            );
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                // y = T.f
                // add pfg edge y <- T.f
                addPFGEdge(
                        pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve()),// T.f
                        pointerFlowGraph.getVarPtr(stmt.getLValue())
                );
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                // T.f = y
                // add pfg edge T.f -> y
                addPFGEdge(
                        pointerFlowGraph.getVarPtr(stmt.getRValue()),
                        pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve())
                );
            }
            return null;
        }

        @Override
        public Void visit(Invoke callSite) {
            if (callSite.isStatic()) {
                var callee = resolveCallee(null, callSite);
                processCallMethod(callSite, callee);
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source, target)) {
            var pts = source.getPointsToSet();
            if (!pts.isEmpty()) {
                workList.addEntry(target, pts);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()) {
            var entry = workList.pollEntry();
            var delta = propagate(entry.pointer(), entry.pointsToSet());
            System.out.println("point: " + entry.pointer() + " delta: " + delta);
            var pointer = entry.pointer();
            if (pointer instanceof VarPtr varPtr) {
                for (var obj : delta) {
                    var curVar = varPtr.getVar();
                    // x.f = y storeField
                    curVar.getStoreFields().forEach(storeField -> {
                        var ptr = pointerFlowGraph.getVarPtr(storeField.getRValue());
                        var field = storeField.getFieldAccess().getFieldRef().resolve();
                        var instanceField = pointerFlowGraph.getInstanceField(obj, field);
                        addPFGEdge(ptr, instanceField);
                    });
                    // y = x.f loadField
                    curVar.getLoadFields().forEach(loadField -> {
                        var ptr = pointerFlowGraph.getVarPtr(loadField.getLValue());
                        var field = loadField.getFieldAccess().getFieldRef().resolve();
                        var instanceField = pointerFlowGraph.getInstanceField(obj, field);
                        addPFGEdge(instanceField, ptr);
                    });
                    // x[i] = y storeArray
                    curVar.getStoreArrays().forEach(storeArray -> {
                        var ptr = pointerFlowGraph.getVarPtr(storeArray.getRValue());
                        var arrayIndex = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(ptr, arrayIndex);
                    });
                    // y = x[i] loadArray
                    curVar.getLoadArrays().forEach(loadArray -> {
                        var ptr = pointerFlowGraph.getVarPtr(loadArray.getLValue());
                        var arrayIndex = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(arrayIndex, ptr);
                    });
                    // x.m(...)
                    processCall(curVar, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // 计算差集 delta = pts - pt(n)
        // 把 delta 加到 pt(n) 里
        // 把 delta 加到 pt(n) 的所有后继里
        // 返回 delta
        PointsToSet delta = new PointsToSet();
        pointsToSet.objects().forEach(obj -> {
            if (pointer.getPointsToSet().addObject(obj)) {
                delta.addObject(obj);
            }
        });
        if (!delta.isEmpty()) {
            pointerFlowGraph.getSuccsOf(pointer).forEach(s -> workList.addEntry(s, delta));
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var  the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // l: r = x.k(a1, ..., an)
        var invokes = var.getInvokes();
        for (var invoke : invokes) {
            var m = resolveCallee(recv, invoke);
            var mThis = m.getIR().getThis();
            // pass receiver object to this variable
            workList.addEntry(pointerFlowGraph.getVarPtr(mThis), new PointsToSet(recv));
            // call graph on the fly
            var callKind = CallGraphs.getCallKind(invoke);
            // l -> m
            if (callGraph.addEdge(new Edge<>(callKind, invoke, m))) {
                processCallMethod(invoke, m);
            }
        }
    }

    private void processCallMethod(Invoke invoke, JMethod m) {
        addReachable(m);
        passCallArgs(invoke, m);
        passCallReturn(invoke, m);
    }


    /**
     * Processes arguments for method calls.
     */
    private void passCallArgs(Invoke invoke, JMethod m) {
        var args = invoke.getInvokeExp().getArgs();
        for (var i = 0; i < args.size(); i++) {
            var arg = args.get(i);
            var param = m.getIR().getParam(i);
            // a[i] -> p[i]
            addPFGEdge(pointerFlowGraph.getVarPtr(arg), pointerFlowGraph.getVarPtr(param));
        }

    }

    /**
     * Processes return values for method calls.
     */
    private void passCallReturn(Invoke invoke, JMethod m) {
        if (invoke.getLValue() != null) {
            var r = invoke.getLValue();
            m.getIR().getReturnVars().forEach(ret -> addPFGEdge(
                    pointerFlowGraph.getVarPtr(ret),
                    pointerFlowGraph.getVarPtr(r)
            ));
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
