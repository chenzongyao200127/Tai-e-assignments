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
        // Initialize a new CPFact object
        CPFact fact = new CPFact();

        // Iterate over the parameters of the control flow graph's intermediate representation
        for (Var var : cfg.getIR().getParams()) {
            // Check if the variable can hold an integer
            if (canHoldInt(var))
                // Update the fact with a non-assignable constant (NAC) value for the variable
                fact.update(var, Value.getNAC());
        }

        // Return the updated fact
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        // Return a new, empty CPFact object
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // Iterate over each variable-value pair in the fact
        fact.forEach(((var, value) -> {
            // Update the target fact with the meet of the existing value and the new value
            target.update(var, meetValue(value, target.get(var)));
        }));
    }

    /**
     * Meets two Values.
     */
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


    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // Check if the statement is an instance of DefinitionStmt
        if (stmt instanceof DefinitionStmt<?, ?> definitionStmt) {
            // Retrieve the left-hand side (LValue) and right-hand side (RValue) of the definition statement
            LValue lValue = definitionStmt.getLValue();
            RValue rValue = definitionStmt.getRValue();

            // Check if the LValue is a variable that can hold an integer
            if (lValue instanceof Var lVar && canHoldInt(lVar)) {
                // Create a copy of the input CPFact
                CPFact tf = in.copy();
                // Update the copied CPFact with the evaluated RValue
                tf.update(lVar, evaluate(rValue, in));
                // Copy the updated CPFact to the output CPFact and return true
                return out.copyFrom(tf);
            }
        }
        // If the statement is not a DefinitionStmt or the conditions are not met,
        // copy the input CPFact to the output CPFact and return false
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
        // Handle the case where 'exp' is an integer literal
        if (exp instanceof IntLiteral intExp) {
            // Return a constant value corresponding to the integer literal
            return Value.makeConstant(intExp.getValue());
        }
        // Handle the case where 'exp' is a variable
        if (exp instanceof Var varExp) {
            // Return the value associated with the variable from 'in'
            return in.get(varExp);
        }

        // Handle binary expressions
        if (!(exp instanceof BinaryExp binaryExp)) {
            // Return a non-assignable constant (NAC) value if 'exp' is not a binary expression
            return Value.getNAC();
        }

        // Retrieve the operands and the operator of the binary expression
        Var op1 = binaryExp.getOperand1(), op2 = binaryExp.getOperand2();
        Value op1Val = in.get(op1), op2Val = in.get(op2);
        BinaryExp.Op op = binaryExp.getOperator();

        // Check if either operand is not a constant
        if (!op1Val.isConstant() || !op2Val.isConstant()) {
            // Handle binary expressions with non-constant operands
            return handleNonConstantOperands(binaryExp, op2Val);
        }

        // Compute and return the result of the binary operation for constant operands
        return computeBinaryOperation(binaryExp, op1Val, op2Val, op);
    }

    // Handles binary expressions with non-constant operands
    private static Value handleNonConstantOperands(BinaryExp binaryExp, Value op2Val) {
        BinaryExp.Op op = binaryExp.getOperator();
        // Check for division or remainder operations with arithmetic expressions
        if (binaryExp instanceof ArithmeticExp && (op == ArithmeticExp.Op.DIV || op == ArithmeticExp.Op.REM)) {
            // Handle the case of division or remainder by zero
            if (op2Val.isConstant() && op2Val.getConstant() == 0) {
                // Return an undefined value for division or remainder by zero
                return Value.getUndef();
            }
        }
        // Return a non-assignable constant (NAC) value for other cases
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
