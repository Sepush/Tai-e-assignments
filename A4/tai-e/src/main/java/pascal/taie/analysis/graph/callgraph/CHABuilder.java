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
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Set;

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

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        var workList = new ArrayDeque<JMethod>();
        workList.add(entry);
        while (!workList.isEmpty()) {
            var method = workList.removeFirst();
            if (callGraph.addReachableMethod(method)) {
                var steamCallSitesIn = callGraph.callSitesIn(method);
                steamCallSitesIn.forEach(cs -> {
                    var t = resolve(cs);
                    var callKind = CallGraphs.getCallKind(cs);
                    t.forEach(target -> {
                        var edge = new Edge<>(callKind, cs, target);
                        callGraph.addEdge(edge);
                        workList.add(target);
                    });
                });
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        var targetMethods = new HashSet<JMethod>();

        var methodRef = callSite.getMethodRef();
        var declaringClass = methodRef.getDeclaringClass();
        var subsignature = methodRef.getSubsignature();

        var kind = CallGraphs.getCallKind(callSite);
        if (kind == CallKind.STATIC) {
            var method = declaringClass.getDeclaredMethod(subsignature);
            if (method != null) {
                targetMethods.add(method);
            }
        } else if (kind == CallKind.SPECIAL) {
            var method = dispatch(declaringClass, subsignature);
            if (method != null) {
                targetMethods.add(method);
            }
        } else if (kind == CallKind.VIRTUAL || kind == CallKind.INTERFACE) {
            var queue = new ArrayDeque<JClass>();
            queue.add(declaringClass);
            while (!queue.isEmpty()) {
                var c = queue.removeFirst();
                var method = dispatch(c, subsignature);
                if (method != null) {
                    targetMethods.add(method);
                }
                if (c.isInterface()) {
                    queue.addAll(hierarchy.getDirectImplementorsOf(c));
                    queue.addAll(hierarchy.getDirectSubinterfacesOf(c));
                } else {
                    queue.addAll(hierarchy.getDirectSubclassesOf(c));
                }
            }

        }

        return targetMethods;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        var method = jclass.getDeclaredMethod(subsignature);
        if (method != null && !method.isAbstract()) {
            return method;
        }
        var superClass = jclass.getSuperClass();
        if (superClass != null) {
            return dispatch(superClass, subsignature);
        }
        return null;
    }
}
