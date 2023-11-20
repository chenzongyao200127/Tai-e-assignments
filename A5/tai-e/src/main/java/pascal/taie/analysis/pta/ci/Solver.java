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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     * WL = {}, PFG = {}, CG = {},
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     * 提示:
     * 1. 不要忘记在该方法中处理静态字段 loads/stores 和静态方法调用。
     * 2. 你可以通过如下方法获得 LoadField/StoreField 语句要 load/store 的字段:
     *      LoadField stmt = ...;
     *      JField field = stmt.getFieldRef().resolve();
     * 3. 为了实时建立调用图，你需要解析方法调用的被调用者。
     *    出于方便，我们提供了 Solver.resolveCallee(Obj,Invoke)
     *    来解析 Java 中静态调用、虚调用、接口调用和特殊调用
     *    （static, virtual, interface, and special invocations）的被调用者。
     * 4. 在 addReachable() 中，对于不同种类的语句，你需要使用不同的逻辑来处理。
     *    实现这种需求的一个合理方式是访问者模式。
     *    Tai-e 的 IR 天然支持访问者模式。
     *    具体来说，Tai-e 提供了 pascal.taie.ir.stmt.StmtVisitor 类，
     *    这是所有 Stmt 访问者的通用接口，它为所有种类的语句都声明了访问操作。
     *    另外，Stmt 的非抽象子类都实现了 accept(StmtVisitor) 方法，
     *    因此它们可以回调来自具体访问者的访问操作。
     *    在 Solver 中，我们为 Stmt 访问者提供了代码框架（即内部类 StmtProcessor），
     *    并在 initialize() 中创建了它的实例，并将该实例存在字段 stmtProcessor 中。
     *    如果你选择通过访问者模式实现 addReachable() 的逻辑，
     *    那么你应该在类 stmtProcessor 中实现相关的 visit(…) 方法，
     *    并使用它来处理可达方法中的语句。在这次作业中，visit(…) 方法的返回值被忽略，
     *    因此你在实现 visit(…) 方法时只需要返回 null。
     *    如果你不熟悉访问者模式，用其他方式实现 addReachable() 也是完全可以的。
     *
     *    AddReachable(m):
     *      if m ∉ RM:
     *          add m to RM
     *          S ∪= Sm
     *          foreach i: x = new T() ∈ Sm do
     *              add (𝑥, {𝑜𝑖}) to WL
     *          foreach x = y ∈ Sm do:
     *              AddEdge(y, x)
     */
    private void addReachable(JMethod method) {
        if (callGraph.addReachableMethod(method)) {
            for (Stmt stmt : method.getIR().getStmts()) {
                stmt.accept(stmtProcessor);
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        Set<Stmt> S;

        // Constructor for StmtProcessor. Initializes the set of statements.
        StmtProcessor() {
            S = new HashSet<>();
        }

        // Checks if a statement is already in the set.
        public boolean contains(Stmt stmt) {
            return S.contains(stmt);
        }

        // Processes 'New' statements.
        // Adds an entry to the worklist based on the pointer flow graph.
        @Override
        public Void visit(New stmt) {
            workList.addEntry(
                    pointerFlowGraph.getVarPtr(stmt.getLValue()),
                    new PointsToSet(heapModel.getObj(stmt))
            );
            return StmtVisitor.super.visit(stmt);
        }

        // Processes 'Copy' statements.
        // Adds an edge to the pointer flow graph.
        @Override
        public Void visit(Copy stmt) {
            addPFGEdge(
                    pointerFlowGraph.getVarPtr(stmt.getRValue()),
                    pointerFlowGraph.getVarPtr(stmt.getLValue())
            );
            return StmtVisitor.super.visit(stmt);
        }

        // Processes 'Invoke' statements.
        // Handles static method invocations and updates the call graph.
        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod method = resolveCallee(null, stmt);
                if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(stmt), stmt, method))) {
                    addReachable(method);
                    for (int i = 0; i < method.getParamCount(); ++i) {
                        Var a = stmt.getInvokeExp().getArg(i);
                        Var p = method.getIR().getParam(i);
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(a),
                                pointerFlowGraph.getVarPtr(p)
                        );
                    }
                    if (stmt.getResult() != null) {
                        for (Var ret : method.getIR().getReturnVars()) {
                            addPFGEdge(
                                    pointerFlowGraph.getVarPtr(ret),
                                    pointerFlowGraph.getVarPtr(stmt.getResult())
                            );
                        }
                    }
                }
            }
            return StmtVisitor.super.visit(stmt);
        }

        // Processes 'StoreField' statements for static fields.
        // Updates the pointer flow graph.
        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                addPFGEdge(
                        pointerFlowGraph.getVarPtr(stmt.getRValue()),
                        pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve())
                );
            }
            return StmtVisitor.super.visit(stmt);
        }

        // Processes 'LoadField' statements for static fields.
        // Updates the pointer flow graph.
        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                addPFGEdge(
                        pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve()),
                        pointerFlowGraph.getVarPtr(stmt.getLValue())
                );
            }
            return StmtVisitor.super.visit(stmt);
        }

        // Default visit method for all other types of statements.
        // Adds the statement to the set.
        @Override
        public Void visitDefault(Stmt stmt) {
            S.add(stmt);
            return StmtVisitor.super.visitDefault(stmt);
        }
    }


    /**
     * Adds an edge "source -> target" to the PFG.
     * 这个方法实现了第 9 讲课件第 43 页中给出的 AddEdge 函数。
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
     * 这个方法实现了第 10 讲课件第 125 页中给出的 Solve 函数的主要部分，即 while 循环部分。
     */
    private void analyze() {
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();

            // Δ = pts – pt(n)
            PointsToSet delta = propagate(entry.pointer(), entry.pointsToSet());

            if (entry.pointer() instanceof  VarPtr varPtr) {
                Var var = varPtr.getVar();
                for (Obj obj: delta) {

                    // Store Field
                    for (StoreField field: var.getStoreFields()) {
                        if (field.isStatic()) {
                            // add edge (y, T.f)
                            addPFGEdge(
                                    pointerFlowGraph.getVarPtr(field.getRValue()),
                                    pointerFlowGraph.getStaticField(field.getFieldRef().resolve())
                            );
                        } else {
                            // add edge (y, oi.f)
                            addPFGEdge(
                                    pointerFlowGraph.getVarPtr(field.getRValue()),
                                    pointerFlowGraph.getInstanceField(obj, field.getFieldRef().resolve())
                            );
                        }
                    }

                    // Load Field
                    for (LoadField field: var.getLoadFields()) {
                        if (field.isStatic()) {
                            // add edge (T.f, y)
                            addPFGEdge(
                                    pointerFlowGraph.getStaticField(field.getFieldRef().resolve()),
                                    pointerFlowGraph.getVarPtr(field.getLValue())
                            );
                        } else {
                            // add edge (oi.f, y)
                            addPFGEdge(
                                    pointerFlowGraph.getInstanceField(obj, field.getFieldRef().resolve()),
                                    pointerFlowGraph.getVarPtr(field.getLValue())
                            );
                        }
                    }

                    // Store Array
                    for (StoreArray array: var.getStoreArrays()) {
                        // add edge Ou[*] <- y
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(array.getRValue()),
                                pointerFlowGraph.getArrayIndex(obj)
                        );
                    }

                    // Load Array
                    for (LoadArray array: var.getLoadArrays()) {
                        // add edge y <- Ou[*]
                        addPFGEdge(
                                pointerFlowGraph.getArrayIndex(obj),
                                pointerFlowGraph.getVarPtr(array.getLValue())
                        );
                    }

                    processCall(var, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet delta = new PointsToSet();
        if (!pointsToSet.isEmpty()) {
            for (Obj obj : pointsToSet) {
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
     * 这个方法实现了第 10 讲课件第 124 页中的 ProcessCall 函数。
     *
     * 你将在这个方法中处理所有种类的实例方法调用，即虚调用、接口调用和特殊调用。
     * 处理接口调用和特殊调用的逻辑与处理虚调用的逻辑完全相同（你在课上已经学过）。
     * 你也可以使用上面提到的 `resolveCallee()` （代替算法中的 Dispatch）来解析所有种类的实例方法调用，
     * 即虚调用、接口调用和特殊调用。
     *
     * 为了保证 soundness，你应该将一个方法中由返回变量（即返回语句中出现的变量）
     * 所指向的所有对象传播给其调用点等号左侧的变量。
     * 你可以通过相关的 IR 对象获得一个方法的所有返回变量。
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        for (Invoke invoke: var.getInvokes()) {
            // m = Dispatch(oi, k)
            JMethod m = resolveCallee(recv, invoke);

            // add <m_this, {oi}> to WL
            workList.addEntry(pointerFlowGraph.getVarPtr(m.getIR().getThis()), new PointsToSet(recv));

            if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, m))) {
                addReachable(m);

                for (int i = 0; i < m.getParamCount(); i++) {
                    Var a = invoke.getInvokeExp().getArg(i);
                    Var p = m.getIR().getParam(i);
                    addPFGEdge(
                            pointerFlowGraph.getVarPtr(a),
                            pointerFlowGraph.getVarPtr(p)
                    );
                }

                if (invoke.getResult() != null) {
                    for (Var ret: m.getIR().getReturnVars()) {
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(ret),
                                pointerFlowGraph.getVarPtr(invoke.getResult())
                        );
                    }
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
