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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        if (callGraph.addReachableMethod(csMethod)) {
            csMethod.getMethod()
                    .getIR()
                    .getStmts()
                    .forEach(stmt -> stmt.accept(new StmtProcessor(csMethod)));
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(New stmt) {
            var ptr = csManager.getCSVar(context, stmt.getLValue());

            var obj = heapModel.getObj(stmt);
            var objCtx = contextSelector.selectHeapContext(csMethod, obj);
            var csObj = csManager.getCSObj(objCtx, obj);
            var pts = PointsToSetFactory.make(csObj);

            workList.addEntry(ptr, pts);
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            var left = csManager.getCSVar(context, stmt.getLValue());
            var right = csManager.getCSVar(context, stmt.getRValue());
            addPFGEdge(right, left);
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            // y = T.f
            if (stmt.isStatic()) {
                var ptr = csManager.getCSVar(context, stmt.getLValue());
                var field = stmt.getFieldAccess().getFieldRef().resolve();
                var staticField = csManager.getStaticField(field);
                addPFGEdge(staticField, ptr);
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            // T.f = y
            if (stmt.isStatic()) {
                var ptr = csManager.getCSVar(context, stmt.getRValue());
                var field = stmt.getFieldAccess().getFieldRef().resolve();
                var staticField = csManager.getStaticField(field);
                addPFGEdge(ptr, staticField);
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                // y = T.m(...)
                var callee = resolveCallee(null, stmt);
                var callSite = csManager.getCSCallSite(context, stmt);
                var calleeCtx = contextSelector.selectContext(callSite, callee);
                var csMethod = csManager.getCSMethod(calleeCtx, callee);

                processCallMethod(stmt, csMethod, calleeCtx, context);
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
            var pointer = entry.pointer();
            var pointsToSet = entry.pointsToSet();
            var delta = propagate(pointer, pointsToSet);
            if (pointer instanceof CSVar csVar) {
                for (var csObj : delta) {
                    var curVar = csVar.getVar();
                    var varCs = csVar.getContext();
                    // x.f = y
                    curVar.getStoreFields().forEach(storeField -> {
                        var ptr = csManager.getCSVar(varCs, storeField.getRValue());
                        var field = storeField.getFieldAccess().getFieldRef().resolve();
                        var instanceField = csManager.getInstanceField(csObj, field);
                        addPFGEdge(ptr, instanceField);
                    });
                    // y = x.f
                    curVar.getLoadFields().forEach(loadField -> {
                        var ptr = csManager.getCSVar(varCs, loadField.getLValue());
                        var field = loadField.getFieldAccess().getFieldRef().resolve();
                        var instanceField = csManager.getInstanceField(csObj, field);
                        addPFGEdge(instanceField, ptr);
                    });

                    // 常规的指针分析不区别对针对同一数组不同位置的 store 和 load
                    // x[i] = y
                    curVar.getStoreArrays().forEach(storeArray -> {
                        var ptr = csManager.getCSVar(varCs, storeArray.getRValue());
                        var arrayIndex = csManager.getArrayIndex(csObj);
                        addPFGEdge(ptr, arrayIndex);
                    });
                    // y = x[i]
                    curVar.getLoadArrays().forEach(loadArray -> {
                        var ptr = csManager.getCSVar(varCs, loadArray.getLValue());
                        var arrayIndex = csManager.getArrayIndex(csObj);
                        addPFGEdge(arrayIndex, ptr);
                    });
                    // x = m(...)
                    processCall(csVar, csObj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        var delta = PointsToSetFactory.make();
        pointsToSet.objects().forEach(obj -> {
            if (pointer.getPointsToSet().addObject(obj)) {
                delta.addObject(obj);
            }
        });
        if (!delta.isEmpty()) {
            pointerFlowGraph
                    .getSuccsOf(pointer)
                    .forEach(s -> workList.addEntry(s, delta));
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        // l: r = x.k(a1, ..., an)
        var invokes = recv.getVar().getInvokes();
        for (var invoke : invokes) {
            var m = resolveCallee(recvObj, invoke);
            var callerCtx = recv.getContext();
            var calleeCtx = contextSelector.selectContext(
                    csManager.getCSCallSite(callerCtx, invoke),
                    recvObj,
                    m
            );
            var mThis = m.getIR().getThis();
            // pass receiver object to this variable
            workList.addEntry(
                    csManager.getCSVar(calleeCtx, mThis),
                    PointsToSetFactory.make(recvObj)
            );
            var callKind = CallGraphs.getCallKind(invoke);
            var csMethod = csManager.getCSMethod(calleeCtx, m);
            var csCallSite = csManager.getCSCallSite(callerCtx, invoke);
            var edge = new Edge<>(callKind, csCallSite, csMethod);
            if (callGraph.addEdge(edge)) {
                processCallMethod(invoke, csMethod, calleeCtx, callerCtx);
            }
        }
    }

    private void processCallMethod(Invoke invoke, CSMethod csMethod, Context calleeCtx, Context callerCtx) {
        addReachable(csMethod);
        passCallArgs(invoke, csMethod, calleeCtx, callerCtx);
        passCallReturn(invoke, csMethod, calleeCtx, callerCtx);
    }

    private void passCallArgs(Invoke invoke, CSMethod csMethod, Context calleeCtx, Context callerCtx) {
        var args = invoke.getInvokeExp().getArgs();
        for (var i = 0; i < args.size(); i++) {
            var arg = args.get(i);
            var param = csMethod.getMethod().getIR().getParam(i);
            addPFGEdge(
                    csManager.getCSVar(callerCtx, arg),
                    csManager.getCSVar(calleeCtx, param)
            );
        }
    }

    private void passCallReturn(Invoke invoke, CSMethod csMethod, Context calleeCtx, Context callerCtx) {
        if (invoke.getLValue() != null) {
            var r = invoke.getLValue();
            csMethod.getMethod().getIR().getReturnVars().forEach(ret -> addPFGEdge(
                    csManager.getCSVar(calleeCtx, ret),
                    csManager.getCSVar(callerCtx, r)
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
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
