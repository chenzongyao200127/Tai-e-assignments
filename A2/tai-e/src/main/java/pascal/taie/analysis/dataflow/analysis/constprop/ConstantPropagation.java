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
import pascal.taie.analysis.dataflow.fact.NodeResult;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;
import soot.JastAddJ.ShiftExpr;
import soot.JastAddJ.Variable;

import java.util.Collections;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.atomic.AtomicBoolean;

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
        CPFact fact = new CPFact();
        for (Var var : cfg.getIR().getParams()) {
            if (canHoldInt(var))
                fact.update(var, Value.getNAC());
        }

        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        fact.forEach(((var, value) -> {
            target.update(var, meetValue(value, target.get(var)));
        }));
    }


    /**
     * Meets two Values.
     * 该方法对应着格上的 meet 操作（⊓），见第 6 讲课件的第 238 页。
     * 你应当在 meetInto() 方法中调用它。
     * 1. NAC ⊓ Any = NAC
     * 2. UNDEF ⊓ Any = Any
     * 3. c ⊓ c = c
     * 4. c1 ⊓ c2 = NAC
     */
    // IN[B] = ⊔ P a predecessor of B OUT[P]
    public Value meetValue(Value v1, Value v2) {
        // If either value is NAC, the result is NAC
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }

        // If both values are constants
        if (v1.isConstant() && v2.isConstant()) {
            return v1.equals(v2) ? Value.makeConstant(v1.getConstant()) : Value.getNAC();
        }

        // If one value is constant and the other is undefined, return the constant
        if (v1.isConstant() && v2.isUndef() || v2.isConstant() && v1.isUndef()) {
            return Value.makeConstant(v1.isConstant() ? v1.getConstant() : v2.getConstant());
        }

        // In all other cases, return NAC
        return Value.getNAC();
    }

    // OUT[B] = genB U (IN[B] - killB);
    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        if (stmt instanceof DefinitionStmt<?, ?> definitionStmt) {
            LValue lValue = definitionStmt.getLValue();
            RValue rValue = definitionStmt.getRValue();

            if (lValue instanceof Var lVar && canHoldInt(lVar)) {
                CPFact tf = in.copy();
                tf.update(lVar, evaluate(rValue, in));
                return out.copyFrom(tf);
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

    public static Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof IntLiteral intExp) {
            return Value.makeConstant(intExp.getValue());
        }
        if (exp instanceof Var varExp) {
            return in.get(varExp);
        }

        if (!(exp instanceof BinaryExp binaryExp)) {
            return Value.getNAC();
        }

        Var op1 = binaryExp.getOperand1(), op2 = binaryExp.getOperand2();
        Value op1Val = in.get(op1), op2Val = in.get(op2);
        BinaryExp.Op op = binaryExp.getOperator();

        if (!op1Val.isConstant() || !op2Val.isConstant()) {
            return handleNonConstantOperands(binaryExp, op2Val);
        }

        return computeBinaryOperation(binaryExp, op1Val, op2Val, op);
    }

    // case: !op1Val.isConstant() || !op2Val.isConstant()
    private static Value handleNonConstantOperands(BinaryExp binaryExp, Value op2Val) {
        BinaryExp.Op op = binaryExp.getOperator();
        if (binaryExp instanceof ArithmeticExp && (op == ArithmeticExp.Op.DIV || op == ArithmeticExp.Op.REM)) {
            // 0 / 0 => UNDEF
            if (op2Val.isConstant() && op2Val.getConstant() == 0) {
                return Value.getUndef();
            }
        }
        return Value.getNAC();
    }

    private static Value computeBinaryOperation(BinaryExp binaryExp, Value op1Val, Value op2Val, BinaryExp.Op op) {
        String opStr = op.toString();
        int val1 = op1Val.getConstant();
        int val2 = op2Val.getConstant();

        switch (opStr) {
            case "+" -> {
                return Value.makeConstant(val1 + val2);
            }
            case "-" -> {
                return Value.makeConstant(val1 - val2);
            }
            case "*" -> {
                return Value.makeConstant(val1 * val2);
            }
            case "/" -> {
                return val1 == 0 ? Value.getUndef() :
                        Value.makeConstant(val1 / val2);
            }
            case "%" -> {
                return val1 == 0 ? Value.getUndef() :
                        Value.makeConstant(val1 % val2);
            }

            case "<=" -> {
                return val1 <= val2 ? Value.makeConstant(1) : Value.makeConstant(0);
            }
            case "<" -> {
                return val1 < val2 ? Value.makeConstant(1) : Value.makeConstant(0);
            }
            case ">" -> {
                return val1 > val2 ? Value.makeConstant(1) : Value.makeConstant(0);
            }
            case ">=" -> {
                return val1 >= val2 ? Value.makeConstant(1) : Value.makeConstant(0);
            }
            case "==" -> {
                return val1 == val2 ? Value.makeConstant(1) : Value.makeConstant(0);
            }
            case "!=" -> {
                return val1 != val2 ? Value.makeConstant(1) : Value.makeConstant(0);
            }


            case "|" -> {
                return Value.makeConstant(val1 | val2);
            }
            case "^" -> {
                return Value.makeConstant(val1 ^ val2);
            }
            case "&" -> {
                return Value.makeConstant(val1 & val2);
            }


            case "<<" -> {
                return Value.makeConstant(val1 << val2);
            }
            case ">>" -> {
                return Value.makeConstant(val1 >> val2);
            }
            case ">>>" -> {
                return Value.makeConstant(val1 >>> val2);
            }

            default -> {
                return Value.getUndef();
            }
        }
    }

}
