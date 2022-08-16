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
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.List;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

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
        CPFact cpFact = new CPFact();
        //将参数中的全部设为 NAC
        List<Var> params = cfg.getIR().getParams();
        for (Var param : params) {
            if (!canHoldInt(param)) continue;            //跳过不能用int表示的类型
            cpFact.update(param, Value.getNAC());
        }
        return cpFact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for (Var var : fact.keySet()) {
            target.update(var, meetValue(fact.get(var), target.get(var)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if (v1.isNAC() || v2.isNAC()) return Value.getNAC();
        if (v1.isUndef()) return v2;
        if (v2.isUndef()) return v1;

        if (v1.getConstant() == v2.getConstant()) return Value.makeConstant(v1.getConstant());

        return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        if (stmt instanceof DefinitionStmt<?, ?>) {
            LValue lv = ((DefinitionStmt<?, ?>) stmt).getLValue();
            RValue rv = ((DefinitionStmt<?, ?>) stmt).getRValue();
            if (lv instanceof Var && canHoldInt((Var) lv)) {
                CPFact tmp = in.copy();
                tmp.update((Var) lv, evaluate(rv, in));
                return out.copyFrom(tmp);
            }
        }
        return out.copyFrom(in);
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

        if (exp instanceof Var) return in.get((Var) exp);
        if (exp instanceof IntLiteral) return Value.makeConstant(((IntLiteral) exp).getValue());

        Value result = Value.getNAC();

        if (exp instanceof BinaryExp) {
            Var op1 = ((BinaryExp) exp).getOperand1();
            Var op2 = ((BinaryExp) exp).getOperand2();
            Value op1_val = in.get(op1);
            Value op2_val = in.get(op2);
            BinaryExp.Op op = ((BinaryExp) exp).getOperator();

            if (op1_val.isConstant() && op2_val.isConstant()) {
                if (exp instanceof ArithmeticExp) {
                    if (op == ArithmeticExp.Op.ADD) {
                        result = Value.makeConstant(op1_val.getConstant() + op2_val.getConstant());
                    } else if (op == ArithmeticExp.Op.DIV) {
                        if (op2_val.getConstant() == 0) result = Value.getUndef();
                        else result = Value.makeConstant(op1_val.getConstant() / op2_val.getConstant());
                    } else if (op == ArithmeticExp.Op.MUL) {
                        result = Value.makeConstant(op1_val.getConstant() * op2_val.getConstant());
                    } else if (op == ArithmeticExp.Op.SUB) {
                        result = Value.makeConstant(op1_val.getConstant() - op2_val.getConstant());
                    } else if (op == ArithmeticExp.Op.REM) {            // 求余
                        if (op2_val.getConstant() == 0) result = Value.getUndef();
                        else result = Value.makeConstant(op1_val.getConstant() % op2_val.getConstant());
                    }
                } else if (exp instanceof BitwiseExp) {
                    if (op == BitwiseExp.Op.AND) {
                        result = Value.makeConstant(op1_val.getConstant() & op2_val.getConstant());
                    } else if (op == BitwiseExp.Op.OR) {
                        result = Value.makeConstant(op1_val.getConstant() | op2_val.getConstant());
                    } else if (op == BitwiseExp.Op.XOR) {
                        result = Value.makeConstant(op1_val.getConstant() ^ op2_val.getConstant());
                    }
                } else if (exp instanceof ConditionExp) {
                    if (op == ConditionExp.Op.EQ) {
                        result = Value.makeConstant((op1_val.getConstant() == op2_val.getConstant()) ? 1 : 0);
                    } else if (op == ConditionExp.Op.GE) {
                        result = Value.makeConstant((op1_val.getConstant() >= op2_val.getConstant()) ? 1 : 0);
                    } else if (op == ConditionExp.Op.GT) {
                        result = Value.makeConstant((op1_val.getConstant() > op2_val.getConstant()) ? 1 : 0);
                    } else if (op == ConditionExp.Op.LE) {
                        result = Value.makeConstant((op1_val.getConstant() <= op2_val.getConstant()) ? 1 : 0);
                    } else if (op == ConditionExp.Op.LT) {
                        result = Value.makeConstant((op1_val.getConstant() < op2_val.getConstant()) ? 1 : 0);
                    } else if (op == ConditionExp.Op.NE) {
                        result = Value.makeConstant((op1_val.getConstant() != op2_val.getConstant()) ? 1 : 0);
                    }
                } else if (exp instanceof ShiftExp) {
                    if (op == ShiftExp.Op.SHL) {
                        result = Value.makeConstant(op1_val.getConstant() << op2_val.getConstant());
                    } else if (op == ShiftExp.Op.SHR) {
                        result = Value.makeConstant(op1_val.getConstant() >> op2_val.getConstant());
                    } else if (op == ShiftExp.Op.USHR) {
                        result = Value.makeConstant(op1_val.getConstant() >>> op2_val.getConstant());
                    }
                } else {
                    result = Value.getUndef();
                }
            } else if (op1_val.isNAC() || op2_val.isNAC()) {
                if (exp instanceof ArithmeticExp && (op == ArithmeticExp.Op.DIV || op == ArithmeticExp.Op.REM)) {
                    if (op2_val.isConstant() && op2_val.getConstant() == 0) result = Value.getUndef();
                    else result = Value.getNAC();
                } else result = Value.getNAC();
            } else {
                result = Value.getUndef();
            }
        }
        return result;
    }
}
