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

import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Stmt;

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Optional;

/**
 * Implementation of classic live variable analysis.
 */
public class LiveVariableAnalysis<e> extends
        AbstractDataflowAnalysis<Stmt, SetFact<Var>> {

    public static final String ID = "livevar";

    public LiveVariableAnalysis(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return false;
    }

    // IN[exit] = Ø
    @Override
    public SetFact<Var> newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        var entryNode = cfg.getExit();

        return new SetFact<Var>(Collections.emptySet());
    }

    // IN[B] = Ø
    @Override
    public SetFact<Var> newInitialFact() {
        // TODO - finish me

        return new SetFact<Var>(Collections.emptySet());
    }

    // OUT[B] = U(S a successor of B) IN[S]
    // 用 meetInto(IN[S], OUT[B]) 把 B 的每个后继 S 的 IN fact 直接并入到 OUT[B] 中
    // 它接受 fact 和 target 两个参数并把 fact 集合并入 target 集合。W
    @Override
    public void meetInto(SetFact<Var> fact, SetFact<Var> target) {
        // TODO - finish me

        target.union(fact);
    }

    // IN[B] = useB U (OUT[B] - defB)
    @Override
    public boolean transferNode(Stmt stmt, SetFact<Var> in, SetFact<Var> out) {
        // TODO - finish me

        List<RValue> useB = stmt.getUses();
        Optional<LValue> defB = stmt.getDef();

        SetFact<Var> tmp = in.copy();

        in.union(out);

        for (RValue e: useB) {
            in.union(new SetFact<>(e));
        }

        defB.ifPresent(lValue -> in.remove((Var) lValue));

        return tmp.equals(in);
    }
}
