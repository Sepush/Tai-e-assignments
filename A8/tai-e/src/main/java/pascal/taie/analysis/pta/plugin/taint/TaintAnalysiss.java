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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Pair;

import java.util.*;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    // TODO - finish me
    public boolean isTaint(Obj obj) {
        return manager.isTaint(obj);
    }

    public Obj handleSource(Invoke invoke, JMethod callee) {
        Type type = callee.getReturnType();
        Source source = new Source(callee, type);
        if (config.getSources().contains(source)) {
            return manager.makeTaint(invoke, type);
        }
        return null;
    }

    public Set<Pair<Var, Obj>> handleTaintTransfer(CSCallSite csCallSite, JMethod callee, CSVar base) {
        PointerAnalysisResult ptaResult = solver.getResult();
        Set<Pair<Var, Obj>> result = new HashSet<>();

        if (base != null) {
            handleBaseToResult(csCallSite,callee,base, ptaResult, result);
            handleArgsToBase(csCallSite,callee,base, ptaResult, result);
        }

        handleArgsToResult(csCallSite, callee, ptaResult, result);

        return result;
    }

    private void handleBaseToResult(
            CSCallSite csCallSite,
            JMethod callee,
            CSVar base,
            PointerAnalysisResult ptaResult,
            Set<Pair<Var, Obj>> result
    ){
        Invoke callSite = csCallSite.getCallSite();
        var lhs = callSite.getLValue();
        Type returnType = callee.getReturnType();
        var taintTransfer = new TaintTransfer(callee, TaintTransfer.BASE, TaintTransfer.RESULT, returnType);
        if (config.getTransfers().contains(taintTransfer) && lhs != null) {
            Set<CSObj> basePts = ptaResult.getPointsToSet(base);
            basePts.forEach(csObj -> {
                if (isTaint(csObj.getObject())) {
                    var source = manager.getSourceCall(csObj.getObject());
                    var taintSource = manager.makeTaint(source, returnType);
                    result.add(new Pair<Var, Obj>(lhs, taintSource));
                }
            });
        }
    }

    private void handleArgsToBase(
            CSCallSite csCallSite,
            JMethod callee,
            CSVar base,
            PointerAnalysisResult ptaResult,
            Set<Pair<Var, Obj>> result
    ) {
        Invoke callSite = csCallSite.getCallSite();
        Type baseType = base.getType();
        List<Var> args = callSite.getInvokeExp().getArgs();
        for (int i = 0; i < args.size(); i++) {
            var arg = args.get(i);
            var csVar = csManager.getCSVar(csCallSite.getContext(), arg);
            Set<CSObj> argPts = ptaResult.getPointsToSet(csVar);
            var taintTransfer = new TaintTransfer(callee, i, TaintTransfer.BASE, baseType);
            if (config.getTransfers().contains(taintTransfer)) {
                argPts.forEach(csObj -> {
                    if (isTaint(csObj.getObject())) {
                        var source = manager.getSourceCall(csObj.getObject());
                        var taintSource = manager.makeTaint(source, baseType);
                        result.add(new Pair<>(base.getVar(), taintSource));
                    }
                });
            }
        }
    }

    private void handleArgsToResult(
            CSCallSite csCallSite,
            JMethod callee,
            PointerAnalysisResult ptaResult,
            Set<Pair<Var, Obj>> result
    ){
        Invoke callSite = csCallSite.getCallSite();
        var lhs = callSite.getLValue();
        Type returnType = callee.getReturnType();
        List<Var> args = callSite.getInvokeExp().getArgs();
        for (int i = 0; i < args.size(); i++) {
            var arg = args.get(i);
            var csVar = csManager.getCSVar(csCallSite.getContext(), arg);
            var argPts = ptaResult.getPointsToSet(csVar);
            var taintTransfer = new TaintTransfer(callee, i, TaintTransfer.RESULT, returnType);
            if (config.getTransfers().contains(taintTransfer)) {
                argPts.forEach(csObj -> {
                    if (isTaint(csObj.getObject())) {
                        var source = manager.getSourceCall(csObj.getObject());
                        var taintSource = manager.makeTaint(source, returnType);
                        result.add(new Pair<>(lhs, taintSource));
                    }
                });
            }
        }
    }


    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.
        var callGraph = result.getCSCallGraph();
        callGraph.reachableMethods().forEach(csMethod->{
            callGraph.getCallersOf(csMethod).forEach(csCallSite->{
                Invoke callSite = csCallSite.getCallSite();
                JMethod callee = csMethod.getMethod();
                List<Var> args = callSite.getInvokeExp().getArgs();
                for (int i = 0; i < args.size(); i++) {
                    var arg = args.get(i);
                    var sink = new Sink(callee,i);
                    if(config.getSinks().contains(sink)){
                        var index = i;
                        result.getPointsToSet(arg).forEach(obj->{
                            if(isTaint(obj)){
                                var source = manager.getSourceCall(obj);
                                taintFlows.add(new TaintFlow(source,callSite,index));
                            }
                        });
                    }
                }
            });
        });
        return taintFlows;
    }
}
