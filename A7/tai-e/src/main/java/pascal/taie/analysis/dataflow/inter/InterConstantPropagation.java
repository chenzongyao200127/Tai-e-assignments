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

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.StaticFieldAccess;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;

import java.util.*;

import pascal.taie.util.collection.Pair;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    // Maps an object to a set of variables that are aliases of it
    public static final Map<Obj, Set<Var>> aliasMap = new HashMap<>();

    // Map a pair of objects to their associated value
    public static final Map<Pair<?, ?>, Value> valMap = new HashMap<>();

    // Map a pair of class and field references to a set of LoadField operations
    public static final Map<Pair<JClass, FieldRef>, Set<LoadField>> staticLoadFields = new HashMap<>();

    private final ConstantPropagation cp;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        // Retrieve the ID for the pointer analysis from the configuration options
        String ptaId = getOptions().getString("pta");

        // Fetch the pointer analysis result using the retrieved ID
        PointerAnalysisResult pta = World.get().getResult(ptaId);

        // Iterate over all variables in the pointer analysis result
        for (Var var : pta.getVars()) {
            // For each variable, iterate over the set of objects it points to
            for (Obj obj : pta.getPointsToSet(var)) {
                // Get the current set of variables aliasing 'obj', or initialize a new set if none exist
                Set<Var> s = aliasMap.getOrDefault(obj, new HashSet<>());

                // Add the current variable to the set of aliases for 'obj'
                s.add(var);

                // Update the alias map with the new set of aliases for 'obj'
                aliasMap.put(obj, s);
            }
        }

        // Iterate over all nodes in the interprocedural control flow graph (ICFG)
        icfg.getNodes().forEach(stmt -> {
            // Check if the statement is a field load operation
            if (stmt instanceof LoadField s && s.getFieldAccess() instanceof StaticFieldAccess access) {
                // Construct a pair of the declaring class and the field reference
                Pair<JClass, FieldRef> accessPair = new Pair<>(access.getFieldRef().getDeclaringClass(), access.getFieldRef());

                // Get the current set of load field operations for this access, or initialize a new set if none exist
                Set<LoadField> set = staticLoadFields.getOrDefault(accessPair, new HashSet<>());

                // Add the current load field operation to the set
                set.add(s);

                // Update the static load fields map with the new set for this access
                staticLoadFields.put(accessPair, set);
            }
        });
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    // OUT[B] = genB U (IN[B] - killB - killParam)
    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        if (in.equals(out)) {
            // If in and out are already equal, no change is made.
            return false;
        } else {
            // If they are different, copy in to out and indicate a change has occurred.
            out.copyFrom(in);
            return true;
        }
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // Delegate the transfer function for non-call nodes to the 'cp' object
        // This method is typically used for statements other than method calls
        return cp.transferNode(stmt, in, out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // Return the input CPFact as-is for normal edges
        // This method indicates that normal edges do not modify the CPFact
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // Check if the source of the edge is an Invoke instance
        if (edge.getSource() instanceof Invoke invoke) {
            // Create a copy of the output fact
            CPFact edgeOut = out.copy();

            // Remove the result variable of the invoke from the copied fact, if present
            Optional.ofNullable(invoke.getResult()).ifPresent(edgeOut::remove);

            // Return the modified copy of the output fact
            return edgeOut;
        } else {
            // Return the input CPFact as-is if the edge source is not an Invoke instance
            return out;
        }
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // Initialize a new CPFact object for the output
        CPFact out = new CPFact();

        // Check if the source of the edge is an Invoke instance
        if (edge.getSource() instanceof Invoke invoke) {
            // Get the invoke expression and the callee method
            InvokeExp invokeExp = invoke.getInvokeExp();
            JMethod callee = edge.getCallee();

            // Iterate over the parameters of the callee
            for (int i = 0; i < callee.getParamCount(); i++) {
                // Update the output fact: map each callee parameter
                // to the corresponding argument value from the call site
                out.update(callee.getIR().getParam(i), callSiteOut.get(invokeExp.getArg(i)));
            }
        }
        // Return the output fact
        return out;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // Initialize a new CPFact object for the output
        CPFact out = new CPFact();

        // Check if the call site associated with the edge is an Invoke instance
        if (edge.getCallSite() instanceof Invoke invoke) {
            // Retrieve the variable where the result is stored
            Var result = invoke.getResult();

            // Check if the result variable is not null
            if (result != null) {
                // Compute the final value for the result variable by
                // merging the values of the return variables
                Value val = edge.getReturnVars().stream()
                        .map(returnOut::get) // Map each return variable to its corresponding value
                        .reduce(Value.getUndef(), cp::meetValue); // Merge the values using the meet operation

                // Update the output fact with the computed value for the result variable
                out.update(result, val);
            }
        }
        // Return the output fact
        return out;
    }
}
