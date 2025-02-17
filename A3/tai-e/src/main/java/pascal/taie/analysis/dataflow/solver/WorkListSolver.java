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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;
import java.util.Queue;
import java.util.LinkedList;
import java.util.Set;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        Queue<Node> workList = new LinkedList<>();
        // WorkList ← all basic blocks
        for (Node node: cfg) {
            workList.add(node);
        }

        while (!workList.isEmpty()) {
            Node curNode = workList.poll();
            Set<Node> predecessors = cfg.getPredsOf(curNode);
            for (Node pre: predecessors) {
                analysis.meetInto(result.getOutFact(pre), result.getInFact(curNode));
            }
            if (analysis.transferNode(curNode, result.getInFact(curNode), result.getOutFact(curNode))) {
                workList.addAll(cfg.getSuccsOf(curNode));
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        boolean changed = true;
        while (changed) {
            changed = false;
            for (Node node : cfg) {
                if (cfg.isExit(node)) continue;

                Fact outFact = result.getOutFact(node);
                for (Node successorNode : cfg.getSuccsOf(node)) {
                    analysis.meetInto(result.getInFact(successorNode), outFact);
                }

                Fact inFact = result.getInFact(node);
                changed = changed || analysis.transferNode(node, inFact, outFact);
            }
        }
    }
}
