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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Sets;

import java.util.Set;
import java.util.TreeSet;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    /**
     * Retrieves a set of taint transfer types associated with a particular method and argument positions.
     *
     * @param method The method to check for taint transfers.
     * @param from The index of the argument from which the taint originates.
     * @param to The index of the argument to which the taint is transferred.
     * @return A set of types representing the taint transfers for the given method and argument positions.
     */
    private Set<Type> getTaintTransfersType(JMethod method, int from, int to) {
        // Initialize an empty set to store the result.
        Set<Type> result = Sets.newHybridSet();

        // Iterate over the collection of taint transfers defined in the configuration.
        config.getTransfers().forEach(transfer -> {
            // Check if the current transfer's method, from index, and to index match the provided parameters.
            if (transfer.method().equals(method) && transfer.from() == from && transfer.to() == to) {
                // If there's a match, add the transfer's type to the result set.
                result.add(transfer.type());
            }
        });

        // Return the set of found taint transfer types.
        return result;
    }


    /**
     * Handles the finalization of the analysis process.
     * This method is typically called when the analysis is complete.
     */
    public void onFinish() {
        // Collect all taint flows that have been identified during the analysis.
        Set<TaintFlow> taintFlows = collectTaintFlows();

        // Store the collected taint flows in the result of the solver.
        // The class name is used as a key or identifier in the result storage.
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }



    // Method to collect taint flows in a program
    private Set<TaintFlow> collectTaintFlows() {
        // Initialize a set to store identified taint flows
        Set<TaintFlow> taintFlows = new TreeSet<>();
        // Retrieve the result of pointer analysis from the solver
        PointerAnalysisResult result = solver.getResult();
        // Comment: You could query pointer analysis results you need via variable result.

        // Process `Sink` Rules
        // Iterate through each edge in the call graph
        result.getCSCallGraph().edges().forEach(edge -> {
            // Get the call site and the method being called at this edge
            CSCallSite csCallSite = edge.getCallSite();
            JMethod method = edge.getCallee().getMethod();

            // Extract the invoke expression and context from the call site
            Invoke l = csCallSite.getCallSite();
            Context c = csCallSite.getContext();

            // For each parameter of the method, check if it is a sink
            for (int i = 0; i < method.getParamCount(); i++) {
                // Get the variable corresponding to the i-th argument of the invoke expression
                CSVar a = csManager.getCSVar(c, l.getInvokeExp().getArg(i));

                // If the method and parameter index match a defined sink
                if (config.getSinks().contains(new Sink(method, i))) {
                    // Get the points-to set for the variable
                    PointsToSet pa = a.getPointsToSet();

                    // For each object in the points-to set, check if it is tainted
                    for (CSObj csObj : pa) {
                        Obj obj = csObj.getObject();
                        // If the object is tainted, add a new TaintFlow to the set
                        if (manager.isTaint(obj)) {
                            taintFlows.add(new TaintFlow(manager.getSourceCall(obj), l, i));
                        }
                    }
                }
            }
        });

        // Return the set of identified taint flows
        return taintFlows;
    }

    /**
     * Retrieves the set of types that are marked as sources for a given method.
     *
     * @param method The method for which to find source types.
     * @return A set of types that are marked as sources for the specified method.
     */
    public Set<Type> getSources(JMethod method) {
        // Initialize an empty set to store the result.
        Set<Type> result = Sets.newHybridSet();

        // Iterate over the collection of sources defined in the configuration.
        config.getSources().forEach(source -> {
            // Check if the current source's method matches the method parameter.
            if (source.method() == method) {
                // If it matches, add the source's type to the result set.
                result.add(source.type());
            }
        });

        // Return the set of found source types.
        return result;
    }


    /**
     * Retrieves the types of taint transfers from a specific argument of a method to its result.
     *
     * @param method The method being analyzed.
     * @param index The index of the argument in the method's parameter list.
     * @return A set of types indicating the taint transfer from the specified argument to the result.
     */
    public Set<Type> getArgsToResultTransfers(JMethod method, int index) {
        return getTaintTransfersType(method, index, TaintTransfer.RESULT);
    }


    /**
     * Retrieves the types of taint transfers from a specific argument of a method to the base object of the method.
     *
     * @param method The method being analyzed.
     * @param index The index of the argument in the method's parameter list.
     * @return A set of types indicating the taint transfer from the specified argument to the base object.
     */
    public Set<Type> getArgsToBaseTransfers(JMethod method, int index) {
        return getTaintTransfersType(method, index, TaintTransfer.BASE);
    }


    /**
     * Retrieves the types of taint transfers from the base object of a method to its result.
     *
     * @param method The method being analyzed.
     * @return A set of types indicating the taint transfer from the base object to the result.
     */
    public Set<Type> getBaseToResultTransfers(JMethod method) {
        return getTaintTransfersType(method, TaintTransfer.BASE, TaintTransfer.RESULT);
    }


    /**
     * Checks whether the given context-sensitive object (CSObj) is tainted.
     *
     * @param csObj The CSObj to check for taint.
     * @return True if the object is tainted, false otherwise.
     */
    public boolean isTaint(CSObj csObj) {
        return manager.isTaint(csObj.getObject());
    }


    /**
     * Creates a new tainted context-sensitive object (CSObj) based on the provided invoke source and type.
     *
     * @param source The source of the taint, typically an invoke statement.
     * @param type The type of taint.
     * @return A new CSObj representing the tainted object.
     */
    public CSObj getTaintObj(Invoke source, Type type) {
        return csManager.getCSObj(emptyContext, manager.makeTaint(source, type));
    }


    /**
     * Retrieves the source invoke call associated with a given context-sensitive object (CSObj).
     *
     * @param csObj The CSObj for which to find the source call.
     * @return The Invoke instance representing the source of the CSObj.
     */
    public Invoke getSourceCall(CSObj csObj) {
        return manager.getSourceCall(csObj.getObject());
    }
}
