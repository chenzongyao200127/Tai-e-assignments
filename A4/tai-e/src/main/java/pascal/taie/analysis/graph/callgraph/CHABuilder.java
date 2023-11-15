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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    // Build call graph for whole program via CHA:
    // 1. Start from entry methods (focus on main method)
    // 2. For each reachable method 𝑚, resolve target methods
    //      for each call site 𝑐 in 𝑚 via CHA (Resolve(𝑐))
    // 3. Repeat until no new method is discovered
    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me

        // Work list, containing the methods to be processed
        Queue<JMethod> wl = new ArrayDeque<>();

        wl.add(entry);

        while (!wl.isEmpty()) {
            JMethod m = wl.poll();

            if (!callGraph.contains(m)) {
                // add m to RM
                callGraph.addReachableMethod(m);
                callGraph.getCallSitesIn(m).forEach((cs) -> {
                    Set<JMethod> T = resolve(cs);
                    for (JMethod callee: T) {
                        // add 'cs -> target method' to CG
                        callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(cs), cs, callee));
                        // add target method to WL
                        wl.add(callee);
                    }
                });
            }
        }

        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     * Resolve(cs):
     * T = {}
     * 𝑚 = method signature at cs
     * if cs is a static call:
     *      T = {m}
     * if cs is a special call then:
     *      c^m = class Type of m
     *      T = {dispatch(c^m, m)}
     * if cs is a vitrual call then:
     *      c = declared type of receiver variable at cs
     *      for each c' that is a subclass of c or c itself do:
     *          add Dispatch(c', m) to T
     * return T
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me

        Set<JMethod> set = new HashSet<>();
        MethodRef methodRef = callSite.getMethodRef();

        switch (CallGraphs.getCallKind(callSite)) {
            case STATIC -> {
                set.add(methodRef.getDeclaringClass()
                        .getDeclaredMethod(methodRef.getSubsignature()));
            }

            case SPECIAL -> {
                Optional.ofNullable(dispatch(methodRef.getDeclaringClass(),
                        methodRef.getSubsignature()))
                        .ifPresent(set::add);
            }

            case VIRTUAL, INTERFACE -> {
                JClass cm = methodRef.getDeclaringClass();
                Queue<JClass> queue = new ArrayDeque<>();
                queue.add(cm);

                while (!queue.isEmpty()) {
                    // itself
                    JClass c = queue.poll();
                    Optional.ofNullable(dispatch(c, methodRef.getSubsignature()))
                            .ifPresent(set::add);

                    // each c that is a subclass of c
                    if (c.isInterface()) {
                        queue.addAll(hierarchy.getDirectImplementorsOf(c));
                    }

                    queue.addAll(hierarchy.getDirectSubclassesOf(c));
                }
            }
        }

        return set;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     * 该方法实现了第 7 讲课件的第 26 页中描述的 Dispatch 方法。
     * 特别地，如果找不到满足要求的方法，返回 null。
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me

        JMethod method = jclass.getDeclaredMethod(subsignature);
        if (method != null) {
            return method;
        }
        JClass superClass = jclass.getSuperClass();
        return (superClass == null) ? null : dispatch(superClass, subsignature);
    }
}
