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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.*;

import java.util.Map;
import java.util.Set;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    private Map<Pointer, Set<Pair<Pointer, Type>>> taintFlowGraph;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    void solve() {
        initialize();
        analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
        // traitFlowGraph
        taintFlowGraph = Maps.newHybridMap();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Adds an edge to the Taint Flow Graph (TFG) between the given source and target pointers.
     *
     * @param source The source pointer of the edge.
     * @param target The target pointer of the edge.
     * @param type The type of the edge.
     */
    private void addTFGEdge(Pointer source, Pointer target, Type type) {
        // Adds the edge to the Taint Flow Graph if it's not already present.
        // 'computeIfAbsent' checks if 'source' is a key in 'taintFlowGraph';
        // if not, it adds 'source' with a new HybridSet and returns this new set.
        if (taintFlowGraph.computeIfAbsent(source, pointer -> Sets.newHybridSet()).add(new Pair<>(target, type))) {
            // Create a new PointsToSet instance.
            PointsToSet pointsToSet = PointsToSetFactory.make();

            // Iterate over the points-to set of 'source'.
            // If any object in this set is tainted, add a corresponding taint object to 'pointsToSet'.
            source.getPointsToSet().forEach(csObj -> {
                if (taintAnalysis.isTaint(csObj)) {
                    pointsToSet.addObject(taintAnalysis.getTaintObj(taintAnalysis.getSourceCall(csObj), type));
                }
            });

            // If 'pointsToSet' is empty after processing, add it along with 'target' to the work list.
            if (pointsToSet.isEmpty()) {
                workList.addEntry(target, pointsToSet);
            }
        }
    }


    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // Attempt to add the given context-sensitive method to the call graph.
        // If the method is successfully added (i.e., it was not already present),
        // then proceed to process its statements.
        if (callGraph.addReachableMethod(csMethod)) {
            // Iterate over each statement in the Intermediate Representation (IR)
            // of the method's body.
            for (Stmt stmt: csMethod.getMethod().getIR().getStmts()) {
                // For each statement, apply a processing routine encapsulated
                // within the StmtProcessor class. This routine likely performs
                // operations specific to each statement in the context of the
                // given method.
                stmt.accept(new StmtProcessor(csMethod));
            }
        }
    }


    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;
        private final Context context;

        // Constructor for StmtProcessor
        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        /**
         * Process 'New' statements.
         */
        @Override
        public Void visit(New stmt) {
            // Obtain an object from the heap model corresponding to the statement.
            Obj obj = heapModel.getObj(stmt);
            // Add an entry to the worklist for processing.
            // This involves creating a points-to set for the left value of the statement.
            workList.addEntry(
                    csManager.getCSVar(context, stmt.getLValue()),
                    PointsToSetFactory.make(csManager.getCSObj(contextSelector.selectHeapContext(csMethod, obj), obj))
            );
            return StmtVisitor.super.visit(stmt);
        }

        /**
         * Process 'Copy' statements.
         */
        @Override
        public Void visit(Copy stmt) {
            // Create a points-from-graph (PFG) edge between the right and left values of the statement.
            addPFGEdge(
                    csManager.getCSVar(context, stmt.getRValue()),
                    csManager.getCSVar(context, stmt.getLValue())
            );
            return StmtVisitor.super.visit(stmt);
        }

        /**
         * Process 'Static Store Field' statements.
         */
        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                // For static field assignments, create a PFG edge from the right value to the resolved static field.
                addPFGEdge(
                        csManager.getCSVar(context, stmt.getRValue()),
                        csManager.getStaticField(stmt.getFieldRef().resolve())
                );
            }
            return StmtVisitor.super.visit(stmt);
        }

        /**
         * Process 'Static Load Field' statements.
         */
        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                // For static field loads, create a PFG edge from the static field to the left value.
                addPFGEdge(
                        csManager.getStaticField(stmt.getFieldRef().resolve()),
                        csManager.getCSVar(context, stmt.getLValue())
                );
            }
            return StmtVisitor.super.visit(stmt);
        }

        /**
         * Process 'Static Method Invoke' statements.
         */
        @Override
        public Void visit(Invoke stmt) {
            // Check if the invoked statement is a static method call.
            if (stmt.isStatic()) {
                // Resolve the method being called.
                JMethod method = resolveCallee(null, stmt);

                // Select a context for the call.
                Context ct = contextSelector.selectContext(
                        csManager.getCSCallSite(context, stmt),
                        method
                );

                // Attempt to add an edge to the call graph for this invocation.
                if (callGraph.addEdge(new Edge<>(
                        CallGraphs.getCallKind(stmt),
                        csManager.getCSCallSite(context, stmt),
                        csManager.getCSMethod(ct, method)
                ))) {
                    // If the method is successfully added to the call graph,
                    // handle the method's arguments and return values.
                    addReachable(csManager.getCSMethod(ct, method));

                    // Iterate over each argument of the invoked method.
                    for (int i = 0; i < method.getParamCount(); ++i) {
                        Var a = stmt.getInvokeExp().getArg(i);
                        Var p = method.getIR().getParam(i);

                        // Create a Program Flow Graph (PFG) edge from each actual argument to the corresponding formal parameter.
                        addPFGEdge(
                                csManager.getCSVar(context, a),
                                csManager.getCSVar(ct, p)
                        );

                        // Process Source Call: Handle taint flow from arguments to the result, if the method returns a value.
                        if (stmt.getResult() != null) {
                            taintAnalysis.getArgsToResultTransfers(method, i).forEach(returnType -> {
                                addTFGEdge(
                                        csManager.getCSVar(context, a),
                                        csManager.getCSVar(context, stmt.getResult()),
                                        returnType);
                            });
                        }
                    }

                    // If the invoked method has a return value, handle the return variables.
                    if (stmt.getResult() != null) {
                        for (Var ret : method.getIR().getReturnVars()) {
                            // Create PFG edges from each return variable of the method to the invoke statement's result.
                            addPFGEdge(
                                    csManager.getCSVar(ct, ret),
                                    csManager.getCSVar(context, stmt.getResult())
                            );
                        }

                        // For each taint source type in the method, add an entry to the work list.
                        taintAnalysis.getSources(method).forEach(type -> {
                            workList.addEntry(
                                    csManager.getCSVar(context, stmt.getResult()),
                                    PointsToSetFactory.make(taintAnalysis.getTaintObj(stmt, type))
                            );
                        });
                    }
                }
            }

            // Continue with the standard visitation process for this statement.
            return StmtVisitor.super.visit(stmt);
        }


        /**
         * Default visit method for statements that do not match any specific type.
         * Delegates to the default implementation in the superclass.
         */
        @Override
        public Void visitDefault(Stmt stmt) {
            return StmtVisitor.super.visitDefault(stmt);
        }
    }

    /*
     * Adds an edge "source -> target" to the PFG (Pointer Flow Graph).
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // Attempts to add an edge from the source pointer to the target pointer in the pointer flow graph.
        // The addEdge method returns true if the edge was successfully added.
        if (pointerFlowGraph.addEdge(source, target)) {
            // Check if the points-to set of the source pointer is not empty.
            // The points-to set represents all the memory locations the pointer can point to.
            if (!source.getPointsToSet().isEmpty()) {
                // If the points-to set is not empty, add an entry to the workList.
                // This entry is for further processing, indicating that the target pointer may now point to
                // new locations as indicated by the source's points-to set.
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // Loop until the work list is empty.
        while (!workList.isEmpty()) {
            // Poll an entry from the work list.
            WorkList.Entry entry = workList.pollEntry();

            // Propagate the points-to set for the current pointer.
            PointsToSet delta = propagate(entry.pointer(), entry.pointsToSet());

            // Check if the pointer is an instance of CSVar.
            if (entry.pointer() instanceof CSVar csVar) {
                // Retrieve context and variable from csVar.
                Context c = csVar.getContext();
                Var var = csVar.getVar();

                // Process each object in the delta points-to set.
                for (CSObj csObj : delta) {
                    // Handle store field statements for the variable.
                    for (StoreField stmt : var.getStoreFields()) {
                        // Add an edge for static fields.
                        if (stmt.isStatic()) {
                            addPFGEdge(
                                    csManager.getCSVar(c, stmt.getRValue()),
                                    csManager.getStaticField(stmt.getFieldRef().resolve())
                            );
                        } else {
                            // Add an edge for instance fields.
                            addPFGEdge(
                                    csManager.getCSVar(c, stmt.getRValue()),
                                    csManager.getInstanceField(csObj, stmt.getFieldRef().resolve())
                            );
                        }
                    }

                    // Handle load field statements for the variable.
                    for (LoadField stmt : var.getLoadFields()) {
                        // Add an edge for static fields.
                        if (stmt.isStatic()) {
                            addPFGEdge(
                                    csManager.getStaticField(stmt.getFieldRef().resolve()),
                                    csManager.getCSVar(c, stmt.getLValue())
                            );
                        } else {
                            // Add an edge for instance fields.
                            addPFGEdge(
                                    csManager.getInstanceField(csObj, stmt.getFieldRef().resolve()),
                                    csManager.getCSVar(c, stmt.getLValue())
                            );
                        }
                    }

                    // Process store array statements.
                    for (StoreArray stmt : var.getStoreArrays()) {
                        addPFGEdge(
                                csManager.getCSVar(c, stmt.getRValue()),
                                csManager.getArrayIndex(csObj)
                        );
                    }

                    // Process load array statements.
                    for (LoadArray stmt : var.getLoadArrays()) {
                        addPFGEdge(
                                csManager.getArrayIndex(csObj),
                                csManager.getCSVar(c, stmt.getLValue())
                        );
                    }

                    // Process method calls.
                    processCall(csVar, csObj);
                }
            }
        }
    }


    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // Create a new, empty PointsToSet named 'delta'. This set will track the changes (new objects added) to the pointer's points-to set.
        PointsToSet delta = PointsToSetFactory.make();

        // Check if the provided pointsToSet is not empty.
        if (!pointsToSet.isEmpty()) {
            // Iterate through each CSObj (context-sensitive object) in the pointsToSet.
            for (CSObj obj : pointsToSet) {
                // Add each object to the pointer's points-to set. If the object is new to the set (i.e., addObject returns true),
                // also add it to the delta set.
                if (pointer.getPointsToSet().addObject(obj)) {
                    delta.addObject(obj);

                    // Check if the object 'obj' is tainted according to the taint analysis.
                    if (taintAnalysis.isTaint(obj)) {
                        // Retrieve the set of transfers associated with 'pointer' in the taint flow graph.
                        // 'getOrDefault' is used to handle the case where 'pointer' has no associated transfers.
                        taintFlowGraph.getOrDefault(pointer, Set.of()).forEach(transfer -> {
                            // For each transfer, add an entry to the work list.
                            // This entry includes the first element of the transfer (likely a target pointer)
                            // and a points-to set created for the taint object associated with 'obj'.
                            workList.addEntry(
                                    transfer.first(),
                                    PointsToSetFactory.make(
                                            taintAnalysis.getTaintObj(taintAnalysis.getSourceCall(obj),
                                            transfer.second())
                                    )
                            );
                        });
                    }
                }
            }

            // For each successor of the pointer in the pointer flow graph, add an entry to the worklist.
            // This entry consists of the successor and the delta set, indicating that these successors might be affected
            // by the changes in the pointer's points-to set.
            pointerFlowGraph.getSuccsOf(pointer).forEach(s -> workList.addEntry(s, delta));
        }

        // Return the delta set, which represents the changes to the pointer's points-to set as a result of this propagation.
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        Context context = recv.getContext();
        // Iterate over all method invocations associated with the receiver variable
        for (Invoke invoke : recv.getVar().getInvokes()) {
            // Resolve the method being called
            JMethod m = resolveCallee(recvObj, invoke);

            // Select the context for this method invocation
            Context ct = contextSelector.selectContext(
                    csManager.getCSCallSite(recv.getContext(), invoke), recvObj, m
            );

            // Add the context and method to the work list for further processing
            workList.addEntry(
                    csManager.getCSVar(ct, m.getIR().getThis()),
                    PointsToSetFactory.make(recvObj)
            );

            // Add an edge to the call graph representing this method call
            if (callGraph.addEdge(new Edge<>(
                    CallGraphs.getCallKind(invoke),
                    csManager.getCSCallSite(recv.getContext(), invoke),
                    csManager.getCSMethod(ct, m))))
            {

                // Mark the called method as reachable
                addReachable(csManager.getCSMethod(ct, m));

                // For each argument of the method, create a Program Flow Graph (PFG) edge
                for (int i = 0; i < m.getParamCount(); ++i) {
                    Var a = invoke.getInvokeExp().getArg(i);
                    Var p = m.getIR().getParam(i);
                    addPFGEdge(
                            csManager.getCSVar(recv.getContext(), a),
                            csManager.getCSVar(ct, p)
                    );

                    // Process Taint Transfer (Args to Base)
                    taintAnalysis.getArgsToBaseTransfers(m, i).forEach(type -> {
                        addTFGEdge(
                                csManager.getCSVar(context, a),
                                recv,
                                type
                        );
                    });

                    // Process Taint Transfer (Args to Result)
                    if (invoke.getResult() != null) {
                        taintAnalysis.getArgsToResultTransfers(m, i).forEach(type -> {
                            addTFGEdge(
                                    csManager.getCSVar(context, a),
                                    csManager.getCSVar(context, invoke.getResult()),
                                    type
                            );
                        });
                    }
                }

                // If the invoked method has a return value, create PFG edges for the return value
                if (invoke.getResult() != null) {
                    for (Var ret : m.getIR().getReturnVars()) {
                        addPFGEdge(
                                csManager.getCSVar(ct, ret),
                                csManager.getCSVar(recv.getContext(), invoke.getResult())
                        );
                    }

                    // Process Taint Transfer (Base to Result)
                    taintAnalysis.getBaseToResultTransfers(m).forEach(type -> {
                        addTFGEdge(
                                recv,
                                csManager.getCSVar(context, invoke.getResult()),
                                type
                        );
                    });

                    // Add new TaintObj to workList
                    taintAnalysis.getSources(m).forEach(type -> {
                        workList.addEntry(
                                csManager.getCSVar(context, invoke.getResult()),
                                PointsToSetFactory.make(taintAnalysis.getTaintObj(invoke, type))
                        );
                    });
                }
            }
        }
    }


    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
