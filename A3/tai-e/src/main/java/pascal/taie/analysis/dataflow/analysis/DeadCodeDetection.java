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
        // Obtain the Control Flow Graph (CFG) from the IR.
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);

        // Retrieve results of constant propagation and live variable analysis.
        DataflowResult<Stmt, CPFact> constants = ir.getResult(ConstantPropagation.ID);
        DataflowResult<Stmt, SetFact<Var>> liveVars = ir.getResult(LiveVariableAnalysis.ID);

        // Prepare sets for dead code and live code, sorted by statement indices.
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        Set<Stmt> liveCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));

        // Initialize queue with the entry point of the CFG.
        Queue<Stmt> queue = new LinkedList<>();
        queue.add(cfg.getEntry());

        // Process the statements in the queue.
        while (!queue.isEmpty()) {
            Stmt stmt = queue.poll();

            // Handle assignment statements and check for dead code.
            if (stmt instanceof AssignStmt<?, ?> s && s.getLValue() instanceof Var var) {
                if (!liveVars.getResult(stmt).contains(var) && hasNoSideEffect(s.getRValue())) {
                    queue.addAll(cfg.getSuccsOf(stmt));
                    continue;
                }
            }

            // Skip already processed live code.
            if (!liveCode.add(stmt)) {
                continue;
            }

            // Handle conditional statements with constant propagation.
            if (stmt instanceof If s) {
                Value cond = ConstantPropagation.evaluate(s.getCondition(), constants.getInFact(stmt));
                addConditionalSuccessorsToQueue(cond, cfg, stmt, queue);
            } else if (stmt instanceof SwitchStmt s) {
                Value val = ConstantPropagation.evaluate(s.getVar(), constants.getInFact(stmt));
                addSwitchSuccessorsToQueue(val, cfg, stmt, s, queue);
            } else {
                queue.addAll(cfg.getSuccsOf(stmt));
            }
        }

        // Compute dead code by subtracting live code from all nodes, excluding the exit point.
        deadCode.addAll(cfg.getNodes());
        deadCode.removeAll(liveCode);
        deadCode.remove(cfg.getExit());

        return deadCode;
    }

    /**
     * Adds successors of a given statement to a queue based on the value of a conditional expression.
     * @param cond The conditional expression's value.
     * @param cfg The control flow graph.
     * @param stmt The statement being evaluated.
     * @param queue The queue to which the successors are added.
     */
    private void addConditionalSuccessorsToQueue(Value cond, CFG<Stmt> cfg, Stmt stmt, Queue<Stmt> queue) {
        // Check if the condition is a constant value.
        if (cond.isConstant()) {
            // Iterate over the outgoing edges from the current statement in the CFG.
            for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                // Determine if the current edge corresponds to the true branch of the condition.
                boolean isTrueBranch = cond.getConstant() == 1 && edge.getKind() == Edge.Kind.IF_TRUE;
                // Determine if the current edge corresponds to the false branch of the condition.
                boolean isFalseBranch = cond.getConstant() == 0 && edge.getKind() == Edge.Kind.IF_FALSE;
                // If the edge matches the branch indicated by the condition, add its target to the queue.
                if (isTrueBranch || isFalseBranch) {
                    queue.add(edge.getTarget());
                }
            }
        } else {
            // If the condition is not a constant, add all successor statements of the current statement to the queue.
            queue.addAll(cfg.getSuccsOf(stmt));
        }
    }

    /**
     * Adds successors of a switch statement to a queue based on the value of the switch expression.
     * @param val The value of the switch expression.
     * @param cfg The control flow graph.
     * @param stmt The current statement in the CFG.
     * @param s The switch statement.
     * @param queue The queue to which the successors are added.
     */
    private void addSwitchSuccessorsToQueue(Value val, CFG<Stmt> cfg, Stmt stmt, SwitchStmt s, Queue<Stmt> queue) {
        // Check if the switch value is a constant.
        if (val.isConstant()) {
            boolean hit = false;
            // Iterate over the switch statement's case targets.
            for (Pair<Integer, Stmt> pair : s.getCaseTargets()) {
                // Check if the switch value matches the current case value.
                if (pair.first() == val.getConstant()) {
                    hit = true;
                    // If a match is found, add the corresponding statement to the queue.
                    queue.add(pair.second());
                }
            }
            // If no matching case is found, add the default case's target to the queue.
            if (!hit) {
                queue.add(s.getDefaultTarget());
            }
        } else {
            // If the switch value is not a constant, add all successor statements of the current statement to the queue.
            queue.addAll(cfg.getSuccsOf(stmt));
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
