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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.CastExp;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.NewExp;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;
import pascal.taie.util.collection.Pair;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode
        // 不可达代码
        // 1.控制流不可达
        // eg.: 程序出口后的代码 如 return 语句后的
        // 检测方法： 从入口遍历 cfg 标记可达 遍历结束后未标记的即为不可达 加入 deadcode
        // 2. 分支不可达 if 和 switch
        // eg.1：if(condition) condition 是一个常量 那么另一个分支就不可达
        // eg.2: switch(var) var 是一个常量 那么除了对应的 case 其他分支都不可达
        // 检测方法： 先进行常量传播分析，通过它来告诉我们条件值是否为常量，然后在遍历 CFG 时，我们不进入相应的不可达分支。
        // 无用赋值
        // 一个局部变量在一条语句中被赋值，但再也没有被该语句后面的语句读取
        // 检测方法：预先活跃变量分析 对于一个赋值语句 如果 LHS value 是无用变量 not live 标记为无用赋值 x = expr 除外

        Set<Stmt> liveCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        Queue<Stmt> queue = new LinkedList<>();
        queue.add(cfg.getEntry());
        while (!queue.isEmpty()) {
            Stmt curStmt = queue.poll();
            if (isDeadAssignment(curStmt, liveVars)) {
                queue.addAll(cfg.getSuccsOf(curStmt));
                continue;
            }
            // skip visited statement
            if (!liveCode.add(curStmt)) {
                continue;
            }
            handleControlFlowStatement(curStmt, cfg, constants, queue);
        }
        deadCode.addAll(cfg.getNodes());
        deadCode.removeAll(liveCode);
        deadCode.remove(cfg.getExit());

        return deadCode;
    }

    /**
     * if the given statement left hand side variable is not live
     * and the right hand side expression has no side effect
     * then the assignment is a dead assignment.
     *
     * @return true if given statement is a dead assignment, otherwise false.
     */
    private static boolean isDeadAssignment(Stmt curStmt, DataflowResult<Stmt, SetFact<Var>> liveVars) {
        if (curStmt instanceof AssignStmt<?, ?> s && s.getLValue() instanceof Var lhv) {
            return !liveVars.getResult(curStmt).contains(lhv) && hasNoSideEffect(s.getRValue());
        }
        return false;
    }

    private void handleControlFlowStatement(Stmt stmt, CFG<Stmt> cfg, DataflowResult<Stmt, CPFact> constants, Queue<Stmt> queue) {
        if (stmt instanceof If ifStmt) {
            handleIfStatement(ifStmt, cfg, constants, queue);
        } else if (stmt instanceof SwitchStmt switchStmt) {
            handleSwitchStatement(switchStmt, cfg, constants, queue);
        } else {
            queue.addAll(cfg.getSuccsOf(stmt));
        }
    }

    /**
     * if statement, condition is constant
     * only one branch is reachable
     *
     */
    private void handleIfStatement(If ifStmt, CFG<Stmt> cfg, DataflowResult<Stmt, CPFact> constants, Queue<Stmt> queue) {
        Value value = ConstantPropagation.evaluate(ifStmt.getCondition(), constants.getInFact(ifStmt));
        if (value.isConstant()) {
            for (Edge<Stmt> edge : cfg.getOutEdgesOf(ifStmt)) {
                if ((value.getConstant() == 1 && edge.getKind() == Edge.Kind.IF_TRUE) ||
                        (value.getConstant() == 0 && edge.getKind() == Edge.Kind.IF_FALSE)) {
                    queue.add(edge.getTarget());
                }
            }
        } else {
            queue.addAll(cfg.getSuccsOf(ifStmt));
        }
    }

    /**
     * switch variable is constant
     * and constant variable value match the case value
     * then only add the matched case target to the iterate queue
     * if no case matched and variable is constant add the default target
     * otherwise, add all successors to the iterate queue
     *
     */
    private void handleSwitchStatement(SwitchStmt switchStmt, CFG<Stmt> cfg, DataflowResult<Stmt, CPFact> constants, Queue<Stmt> queue) {
        Value value = ConstantPropagation.evaluate(switchStmt.getVar(), constants.getInFact(switchStmt));
        if (value.isConstant()) {
            boolean matched = false;
            for (Pair<Integer, Stmt> pair : switchStmt.getCaseTargets()) {
                if (pair.first() == value.getConstant()) {
                    matched = true;
                    queue.add(pair.second());
                }
            }
            if (!matched) {
                queue.add(switchStmt.getDefaultTarget());
            }
        } else {
            queue.addAll(cfg.getSuccsOf(switchStmt));
        }
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
