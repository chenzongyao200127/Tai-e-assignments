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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.util.collection.SetQueue;

import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        // Iterate over all entry methods in the interprocedural control flow graph (ICFG)
        icfg.entryMethods().forEach((method -> {
            // Set the out-fact of the entry point of each method to a new boundary fact
            // This initializes the data-flow facts at the entry points of the methods
            result.setOutFact(icfg.getEntryOf(method), analysis.newBoundaryFact(icfg.getEntryOf(method)));
        }));

        // Iterate over all nodes in the ICFG
        for (Node node : icfg) {
            // Set the out-fact of each node to a new initial fact
            // This step initializes the data-flow facts for all nodes
            result.setOutFact(node, analysis.newInitialFact());
        }
    }

    private void doSolve() {
        // Initialize a work list as a queue of nodes
        Queue<Node> workList = new LinkedList<>();

        // Add all nodes (basic blocks) in the ICFG to the work list
        for (Node node: icfg) {
            workList.add(node);
        }

        // Process nodes in the work list until it's empty
        while (!workList.isEmpty()) {
            // Poll (remove and retrieve) a node from the work list
            Node curNode = workList.poll();
            // Initialize a new 'in' fact for the current node
            Fact in = analysis.newInitialFact();

            // Iterate over incoming edges of the current node
            icfg.getInEdgesOf(curNode).forEach(nodeICFGEdge -> {
                // Merge the out-fact of the source node of each incoming edge into 'in'
                analysis.meetInto(analysis.transferEdge(nodeICFGEdge, result.getOutFact(nodeICFGEdge.getSource())), in);
            });

            // handle Store Field

            // handle Array Access

            // Apply the transfer function to the current node
            if (analysis.transferNode(curNode, in, result.getOutFact(curNode))) {
                // If the out-fact of the current node changes, add all its successors to the work list
                workList.addAll(icfg.getSuccsOf(curNode));
            }
        }
    }
}
