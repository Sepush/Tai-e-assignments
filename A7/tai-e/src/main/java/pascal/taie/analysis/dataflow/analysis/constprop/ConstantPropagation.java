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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

public class ConstantPropagation extends AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        var fact = new CPFact();
        cfg.getIR().getParams().forEach((var) -> {
            if (canHoldInt(var)) {
                fact.update(var, Value.getNAC());
            }
        });
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        fact.forEach((var, value) -> target.update(var, meetValue(value, target.get(var))));
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // NAC dominates all other values
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }

        // UNDEF is treated as a neutral element (UNDEF ⊓ v = v)
        if (v1.isUndef()) {
            return v2;
        }
        if (v2.isUndef()) {
            return v1;
        }

        // Both values are constants
        if (v1.isConstant() && v2.isConstant()) {
            return (v1.getConstant() == v2.getConstant()) ? Value.makeConstant(v1.getConstant()) : Value.getNAC();
        }

        // Fallback to UNDEF if no other conditions match
        return Value.getUndef();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        // OUT[B = gen ∪ (IN[B] - {(x,_)}) where x = def(B)
        if (stmt.getDef().isEmpty() || !(stmt.getDef().get() instanceof Var x)) {
            return out.copyFrom(in);
        }

        if (!canHoldInt(x)) {
            return out.copyFrom(in);
        }

        Value value = evaluate(stmt.getUses().get(stmt.getUses().size() - 1), in);
        CPFact inCopy = in.copy();
        inCopy.remove(x);
        inCopy.update(x, value);

        return out.copyFrom(inCopy);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        // 运算 exp 得到最终结果 Value
        //        s: x = c; // c is a constant
        //        F: OUT[s] = gen ∪ (IN[s] – {(x, _)})
        //        gen = {(x, c)}
        //        s: x = y; gen = {(x, val(y))}
        //        s: x = y op z; gen = {(x, f(y,z))}
        //        f(y,z) =
        //                val(y) op val(z) // if val(y) and val(z) are constants
        //                NAC // if val(y) or val(z) is NAC
        //                UNDEF // otherwise
        if (exp instanceof IntLiteral i) { // constants
            return Value.makeConstant(i.getValue());
        } else if (exp instanceof Var v) { // var
            if (in.get(v).isConstant()) {
                return Value.makeConstant(in.get(v).getConstant());
            }
            return in.get(v);
        } else if (exp instanceof BinaryExp b) { // op
            Value lhv = evaluate(b.getOperand1(), in);
            Value rhv = evaluate(b.getOperand2(), in);

            if (isDivisionOrRemainderByZero(rhv, b)) {
                return Value.getUndef();
            }
            // f(y,z)
            if (lhv.isConstant() && rhv.isConstant()) {
                var l = lhv.getConstant();
                var r = rhv.getConstant();
                var expOp = b.getOperator();
                // 对不同的的 exp 进行讨论
                // ArithmeticExp
                // BitwiseExp
                // ConditionExp
                // ShiftExp
                if (expOp instanceof ArithmeticExp.Op op) {
                    switch (op) {
                        case ADD -> {
                            return Value.makeConstant(l + r);
                        }
                        case SUB -> {
                            return Value.makeConstant(l - r);
                        }

                        case MUL -> {
                            return Value.makeConstant(l * r);
                        }
                        case DIV -> {
                            return Value.makeConstant(l / r);
                        }
                        case REM -> {
                            return Value.makeConstant(l % r);
                        }
                    }
                } else if (expOp instanceof BitwiseExp.Op op) {
                    switch (op) {
                        case AND -> {
                            return Value.makeConstant(l & r);
                        }
                        case OR -> {
                            return Value.makeConstant(l | r);
                        }
                        case XOR -> {
                            return Value.makeConstant(l ^ r);
                        }
                    }
                } else if (expOp instanceof ConditionExp.Op op) {
                    switch (op) {
                        case EQ -> {
                            return l == r ? Value.makeConstant(1) : Value.makeConstant(0);
                        }
                        case NE -> {
                            return l != r ? Value.makeConstant(1) : Value.makeConstant(0);
                        }
                        case LT -> {
                            return l < r ? Value.makeConstant(1) : Value.makeConstant(0);
                        }
                        case GT -> {
                            return l > r ? Value.makeConstant(1) : Value.makeConstant(0);
                        }
                        case LE -> {
                            return l <= r ? Value.makeConstant(1) : Value.makeConstant(0);
                        }
                        case GE -> {
                            return l >= r ? Value.makeConstant(1) : Value.makeConstant(0);
                        }
                    }
                } else if (expOp instanceof ShiftExp.Op op) {
                    switch (op) {
                        case SHL -> {
                            return Value.makeConstant(l << r);
                        }
                        case SHR -> {
                            return Value.makeConstant(l >> r);
                        }
                        case USHR -> {
                            return Value.makeConstant(l >>> r);
                        }
                    }
                }
            } else if (lhv.isNAC() || rhv.isNAC()) {
                return Value.getNAC();
            } else {
                return Value.getUndef();
            }
        }
        return Value.getNAC();
    }

    private static boolean isDivisionOrRemainderByZero(Value rhv, BinaryExp b) {
        return rhv.isConstant() && rhv.getConstant() == 0 && b.getOperator() instanceof ArithmeticExp.Op op && (op == ArithmeticExp.Op.DIV || op == ArithmeticExp.Op.REM);
    }
}
