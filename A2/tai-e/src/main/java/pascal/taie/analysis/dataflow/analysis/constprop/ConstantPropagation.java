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

    // 需要注意的是：在实现 newBoundaryFact() 的时候，
    // 你要小心地处理每个会被分析的方法的参数。
    // 具体来说，你要将它们的值初始化为 NAC (请思考：为什么要这么做？)。
//    @Override
//    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
//        CPFact cpFact = new CPFact();
//        for (Stmt exp : cfg) {
//            if (exp instanceof DefinitionStmt<?, ?>) {
//                LValue v = ((DefinitionStmt<?, ?>) exp).getLValue();
//
//                assert v != null;
//                if (!ConstantPropagation.canHoldInt((Var) v)) {
//                    continue;
//                }
//
//                cpFact.update((Var) v, Value.getNAC());
//            }
//        }
//
//        return cpFact;
//    }
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

//    @Override
//    public void meetInto(CPFact fact, CPFact target) {
//        Set<Var> varsToMerge = fact.keySet();
//        Set<Var> varsInTarget = target.keySet();
//
//        for (Var v: varsToMerge) {
//            if (!varsInTarget.contains(v)) {
//                target.update(v, fact.get(v));
//            } else {
//                target.update(v, meetValue(fact.get(v), target.get(v)));
//            }
//        }
//    }

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


//    @Override
//    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
//        AtomicBoolean changed = new AtomicBoolean(false);
//
//        // Update out with values from in, set changed if any updates were made
//        in.forEach((var, value) -> {
//            if (out.update(var, value)) {
//                changed.set(true);
//            }
//        });
//
//        // Handle DefinitionStmt
//        if (stmt instanceof DefinitionStmt<?, ?> s && s.getLValue() instanceof Var var && canHoldInt(var)) {
//            Value originalVal = out.get(var);           // Get the original value of var in out
//            Value newVal = evaluate(s.getRValue(), in); // Evaluate the right-hand side of the statement
//            out.update(var, newVal);                    // Update out with the new value
//
//            // Check if newVal is different from the original value of var in out
//            if (originalVal == null || !originalVal.equals(newVal)) {
//                changed.set(true);
//            }
//        }
//
//        return changed.get();
//    }

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

    /**
     * Evaluates the {@link Value} of given expression.
     * 这个方法会计算表达式（Exp）的值（Value）。当然，此处的值是格上的抽象值。
     * 你需要参考第 6 讲课件的第 247 页上的内容来实现它的三种情况。
     * 对于其它情况，该方法会像我们在第 2.1 节提到的那样返回 NAC。
     * 你应该在 transferNode() 方法中调用它来进行表达式的求值。
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    // 还是有BUG
    public static Value evaluate(Exp exp, CPFact in) {
        // x = c (c is constant)
        if (exp instanceof IntLiteral c) {
            return Value.makeConstant(c.getValue());

            // x = y op z
        } else if (exp instanceof BinaryExp binaryExp) {
            Var v1 = binaryExp.getOperand1();
            Var v2 = binaryExp.getOperand2();
            Value v1Value = in.get(v1);
            Value v2Value = in.get(v2);

            // Check for null or NAC values
            if (v1Value == null || v2Value == null || v1Value.isNAC() || v2Value.isNAC()) {
                return Value.getNAC();
            }

            // Check if both values are constants
            if (!v1Value.isConstant() || !v2Value.isConstant()) {
                return Value.getNAC();
            }

            int val1 = v1Value.getConstant();
            int val2 = v2Value.getConstant();

            // Handle different types of binary expressions
            if (binaryExp instanceof ArithmeticExp) {
                ArithmeticExp.Op op = ((ArithmeticExp) binaryExp).getOperator();
                String opStr = op.toString();

                // Division or modulo by zero results in UNDEF
                if (("/".equals(opStr) || "%".equals(opStr)) && val2 == 0) {
                    return Value.getUndef();
                }

                return switch (opStr) {
                    case "+" -> Value.makeConstant(val1 + val2);
                    case "-" -> Value.makeConstant(val1 - val2);
                    case "*" -> Value.makeConstant(val1 * val2);
                    case "/" -> Value.makeConstant(val1 / val2);
                    case "%" -> Value.makeConstant(val1 % val2);
                    default -> throw new IllegalStateException("Unsupported arithmetic operator: " + opStr);
                };

            } else if (binaryExp instanceof ConditionExp) {
                ConditionExp.Op op = ((ConditionExp) binaryExp).getOperator();
                String opStr = op.toString();

                return switch (opStr) {
                    case "<=" -> val1 <= val2 ? Value.makeConstant(1) : Value.makeConstant(0);
                    case "<" -> val1 < val2 ? Value.makeConstant(1) : Value.makeConstant(0);
                    case ">" -> val1 > val2 ? Value.makeConstant(1) : Value.makeConstant(0);
                    case ">=" -> val1 >= val2 ? Value.makeConstant(1) : Value.makeConstant(0);
                    case "==" -> val1 == val2 ? Value.makeConstant(1) : Value.makeConstant(0);
                    case "!=" -> val1 != val2 ? Value.makeConstant(1) : Value.makeConstant(0);
                    default -> throw new IllegalStateException("Unsupported conditional operator: " + opStr);
                };

            } else if (binaryExp instanceof ShiftExp) {
                ShiftExp.Op op = ((ShiftExp) binaryExp).getOperator();
                String opStr = op.toString();

                return switch (opStr) {
                    case "<<" -> Value.makeConstant(val1 << val2);
                    case ">>" -> Value.makeConstant(val1 >> val2);
                    case ">>>" -> Value.makeConstant(val1 >>> val2);
                    default -> throw new IllegalStateException("Unsupported shift operator: " + opStr);
                };

            } else if (binaryExp instanceof BitwiseExp) {
                BitwiseExp.Op op = ((BitwiseExp) binaryExp).getOperator();
                String opStr = op.toString();

                return switch (opStr) {
                    case "|" -> Value.makeConstant(val1 | val2);
                    case "^" -> Value.makeConstant(val1 ^ val2);
                    case "&" -> Value.makeConstant(val1 & val2);
                    default -> throw new IllegalStateException("Unsupported bitwise operator: " + opStr);
                };
            } else {
                return Value.getNAC();
            }

        } else if (exp instanceof Var v) {
            return in.get(v);

        } else {
            return Value.getNAC();
        }
    }
}
