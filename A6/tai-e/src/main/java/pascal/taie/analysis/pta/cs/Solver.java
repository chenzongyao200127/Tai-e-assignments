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
import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.HashSet;
import java.util.Set;
import java.util.stream.Stream;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     * Including Static Field and Method
     * CSMethod：表示一个带上下文（Context）的方法（JMethod）
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        // add c:m to RM
        if (callGraph.addReachableMethod(csMethod)) {
            for (Stmt stmt: csMethod.getMethod().getIR().getStmts()) {
                // visitor pattern
                // 访问者模式的具体访问者（内部类 StmtProcessor）的 visit() 方法
                // 需要能够访问到正在被处理的 CSMethod 和 Context
                // 因此我们为 StmtProcessor 的构造方法添加了一个 CSMethod 参数
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


        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        private Set<Stmt> stmtSet;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
            this.stmtSet = new HashSet<>();
        }

        // Constructor for StmtProcessor. Initializes the set of statements.

        // checks if statements is already in the set
        public boolean contains(Stmt stmt) {
            return stmtSet.contains(stmt);
        }

        // Process `New`
        @Override
        public Void visit(New stmt) {
            workList.addEntry(
                    csManager.getCSVar(context, stmt.getLValue()),
                    PointsToSetFactory.make(csManager.getCSObj(context, heapModel.getObj(stmt)))
            );
            return StmtVisitor.super.visit(stmt);
        }

        // Process Copy()
        @Override
        public Void visit(Copy stmt) {
            addPFGEdge(
                    csManager.getCSVar(context, stmt.getRValue()),
                    csManager.getCSVar(context, stmt.getLValue())
            );
            return StmtVisitor.super.visit(stmt);
        }

        // Process Static Method Invoke
        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod method = resolveCallee(null, stmt);
                // ct = Select(c, l)
                Context ct = contextSelector.selectContext(
                        csManager.getCSCallSite(context, stmt),
                        method
                );
                if (callGraph.addEdge(new Edge<>(
                        CallGraphs.getCallKind(stmt),
                        csManager.getCSCallSite(context, stmt),
                        csManager.getCSMethod(ct, method)
                ))) {
                    // c:ai -> ct: m_pi
                    addReachable(csManager.getCSMethod(context, method));
                    for (int i = 0; i < method.getParamCount(); ++i) {
                        Var a = stmt.getInvokeExp().getArg(i);
                        Var p = method.getIR().getParam(i);
                        addPFGEdge(
                                csManager.getCSVar(context, a),
                                csManager.getCSVar(ct, p)
                        );
                    }
                    // c:r <- ct: m_ret
                    if (stmt.getResult() != null) {
                        for (Var ret: method.getIR().getReturnVars()) {
                            addPFGEdge(
                                    csManager.getCSVar(ct, ret),
                                    csManager.getCSVar(context, stmt.getResult())
                            );
                        }
                    }
                }
            }
            return StmtVisitor.super.visit(stmt);
        }


        // Process `Static Store Field`
        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                // T.f <- c:y
                addPFGEdge(
                        csManager.getCSVar(context, stmt.getRValue()),
                        csManager.getStaticField(stmt.getFieldRef().resolve())
                );
            }
            return StmtVisitor.super.visit(stmt);
        }

        // Processes 'LoadField' statements for static fields.
        // Updates the pointer flow graph.
        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                // c:y <- T.f
                addPFGEdge(
                        csManager.getStaticField(stmt.getFieldRef().resolve()),
                        csManager.getCSVar(context, stmt.getLValue())
                );
            }
            return StmtVisitor.super.visit(stmt);
        }


        // Default visit method for all other types of statements.
        // Adds the statement to the set.
        @Override
        public Void visitDefault(Stmt stmt) {
            stmtSet.add(stmt);
            return StmtVisitor.super.visitDefault(stmt);
        }
    }

    /*
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if (pointerFlowGraph.addEdge(source, target)) {
            if (!source.getPointsToSet().isEmpty()) {
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();

            // Δ = pts – pt(n)
            PointsToSet delta = propagate(entry.pointer(), entry.pointsToSet());

            if (entry.pointer() instanceof  CSVar csVar) {
                Var var = csVar.getVar();
                for (CSObj obj: delta) {

                    // Store Field
                    for (StoreField field: var.getStoreFields()) {
                        if (field.isStatic()) {
                            // add edge (y, T.f)
                            addPFGEdge(
                                    csManager.getCSVar(csVar.getContext(), var),
                                    csManager.getStaticField(field.getFieldRef().resolve())
                            );
                        } else {
                            // add edge (y, oi.f)
                            addPFGEdge(
                                    csManager.getCSVar(csVar.getContext(), var),
                                    csManager.getInstanceField(obj, field.getFieldRef().resolve())
                            );
                        }
                    }

                    // Load Field
                    for (LoadField field: var.getLoadFields()) {
                        if (field.isStatic()) {
                            // add edge (T.f, y)
                            addPFGEdge(
                                    csManager.getStaticField(field.getFieldRef().resolve()),
                                    csManager.getCSVar(csVar.getContext(), var)
                            );
                        } else {
                            // add edge (oi.f, y)
                            addPFGEdge(
                                    csManager.getInstanceField(obj, field.getFieldRef().resolve()),
                                    csManager.getCSVar(csVar.getContext(), var)
                            );
                        }
                    }

                    // Store Array
                    for (StoreArray array: var.getStoreArrays()) {
                        // add edge Ou[*] <- y
                        addPFGEdge(
                                csManager.getCSVar(csVar.getContext(), var),
                                csManager.getArrayIndex(obj)
                        );
                    }

                    // Load Array
                    for (LoadArray array: var.getLoadArrays()) {
                        // add edge y <- Ou[*]
                        addPFGEdge(
                                csManager.getArrayIndex(obj),
                                csManager.getCSVar(csVar.getContext(), var)
                        );
                    }

                    processCall(csVar, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     * Propagate(n, pts):
     *   if pts is not empty then:
     *     pt(n) U= pts
     *     foreach n -> s ∈ PFG:
     *       add {s, pts} to WL
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet delta = PointsToSetFactory.make();
        if (!pointsToSet.isEmpty()) {
            for (CSObj obj: pointsToSet) {
                if (pointer.getPointsToSet().addObject(obj)) {
                    delta.addObject(obj);
                }
            }
            pointerFlowGraph.getSuccsOf(pointer).forEach(s -> workList.addEntry(s, delta));
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        for (Invoke invoke: recv.getVar().getInvokes()) {
            // Dispatch method
            JMethod m = resolveCallee(recvObj, invoke);

            // get new Context: ct
            Context ct = contextSelector.selectContext(
                    csManager.getCSCallSite(recv.getContext(), invoke), recvObj, m
            );

            // add <ct: m_this, c: {oi}> to WL
            workList.addEntry(
                    csManager.getCSVar(ct, m.getIR().getThis()),
                    PointsToSetFactory.make(recvObj)
            );

            // c:l -> ct: m
            if (callGraph.addEdge(new Edge<>(
                    CallGraphs.getCallKind(invoke),
                    csManager.getCSCallSite(recv.getContext(), invoke),
                    csManager.getCSMethod(ct, m))))
            {
                addReachable(csManager.getCSMethod(ct, m));

                for (int i = 0; i < m.getParamCount(); ++i) {
                    Var a = invoke.getInvokeExp().getArg(i);
                    Var p = m.getIR().getParam(i);
                    addPFGEdge(
                            csManager.getCSVar(recv.getContext(), a),
                            csManager.getCSVar(ct, p)
                    );
                }
                // c:r <- ct: m_ret
                if (invoke.getResult() != null) {
                    for (Var ret: m.getIR().getReturnVars()) {
                        addPFGEdge(
                                csManager.getCSVar(ct, ret),
                                csManager.getCSVar(recv.getContext(), invoke.getResult())
                        );
                    }
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

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
