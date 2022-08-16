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
import pascal.taie.language.classes.*;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

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

        Queue<JMethod> workList = new LinkedList<>();

        workList.add(entry);

        while (!workList.isEmpty()) {
            JMethod jMethod = workList.poll();
            if (!callGraph.reachableMethods.contains(jMethod)) {
                callGraph.addReachableMethod(jMethod);
                Stream<Invoke> callSites = callGraph.callSitesIn(jMethod);

                for (Invoke invoke : callSites.toList()) {
                    Set<JMethod> methods = resolve(invoke);

                    for (JMethod method : methods) {
                        callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke),invoke,method));
                        workList.add(method);
                    }
                }
            }
        }

        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me

        Set<JMethod> T = new HashSet<>();

        CallKind callKind = CallGraphs.getCallKind(callSite);

        if (callKind == CallKind.STATIC) {
            JMethod jMethod = callSite.getContainer();
            T.add(jMethod);     //TODO 不一样
        } else if (callKind == CallKind.SPECIAL) {
            JClass jClass = callSite.getMethodRef().getDeclaringClass();
            Subsignature subsignature = callSite.getMethodRef().getSubsignature();
            JMethod jMethod = dispatch(jClass, subsignature);
            if (jMethod != null)
                T.add(jMethod);

        } else if (callKind == CallKind.VIRTUAL||callKind==CallKind.INTERFACE) {
            //声明类型
            JClass jClass = callSite.getMethodRef().getDeclaringClass();
            Subsignature subsignature = callSite.getMethodRef().getSubsignature();

            Queue<JClass> classQueue = new LinkedList<>();
            classQueue.add(jClass);
            while (!classQueue.isEmpty()) {
                jClass = classQueue.poll();
                JMethod jMethod = dispatch(jClass, subsignature);
                if(jMethod!=null)
                    T.add(jMethod);

                //将子类的也加入到 T 中
                classQueue.addAll(hierarchy.getDirectSubclassesOf(jClass));
                classQueue.addAll(hierarchy.getDirectImplementorsOf(jClass));
                classQueue.addAll(hierarchy.getDirectSubinterfacesOf(jClass));
            }
        }

        return T;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me

        if (jclass == null) return null;
        JMethod declaredMethod = jclass.getDeclaredMethod(subsignature);
        if (declaredMethod == null || declaredMethod.isAbstract())
            return dispatch(jclass.getSuperClass(), subsignature);
        else
            return declaredMethod;
    }
}
