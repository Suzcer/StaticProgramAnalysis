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
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

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
     */
    private void addReachable(JMethod method) {
        // TODO - finish me

        //TODO 静态方法
        if(!callGraph.contains(method)){
            callGraph.addReachableMethod(method);

            List<Stmt> Sm = method.getIR().getStmts();
            for(Stmt stmt:Sm){
                if(stmt instanceof New newStmt){
                    Var lVar = newStmt.getLValue();
                    VarPtr varPtr=new VarPtr(lVar);
                    Obj obj = heapModel.getObj(newStmt);
                    PointsToSet pointsToSet=new PointsToSet();
                    pointsToSet.addObject(obj);
                    workList.addEntry(varPtr,pointsToSet);

                }else if(stmt instanceof Copy copyStmt){
                    Var lVar = copyStmt.getLValue();
                    Var rVal = copyStmt.getRValue();

                    VarPtr lvarPtr=new VarPtr(lVar);
                    VarPtr rvarPtr=new VarPtr(rVal);
                    addPFGEdge(rvarPtr,lvarPtr);
                }
            }

        }

    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me

        //如果PFG发生改变则 返回值为 true
        if(pointerFlowGraph.addEdge(source, target)){
            if(!source.getPointsToSet().isEmpty()){
                workList.addEntry(target,source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     *  PTA-FD P125
     */
    private void analyze() {
        // TODO - finish me

        while (!workList.isEmpty()){
            WorkList.Entry entry = workList.pollEntry();
            Pointer pointer = entry.pointer();

            PointsToSet delta = propagate(pointer, entry.pointsToSet());
            if(pointer instanceof VarPtr varPtr){
                List<StoreField> storeFields = varPtr.getVar().getStoreFields();
                List<LoadField> loadFields = varPtr.getVar().getLoadFields();

                //外层 foreach
                for(Obj obj:delta){

                    //内层 foreach
                    for(StoreField storeField:storeFields){
                        Var rValue = storeField.getRValue();
                        VarPtr ptr=new VarPtr(rValue);

                        //如何表示 oi.f ?


                    }

                    //内层 foreach
                    for(LoadField loadField:loadFields){

                    }

                    processCall(varPtr.getVar(),obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me

        //计算差集的笨方法
        PointsToSet delta=new PointsToSet();
        for(Obj obj:pointer.getPointsToSet()){
            if(!pointsToSet.contains(obj))
                delta.addObject(obj);
        }

        if(!delta.isEmpty()){
            for(Obj obj:delta){
                pointer.getPointsToSet().addObject(obj);
            }

            Set<Pointer> succs = pointerFlowGraph.getSuccsOf(pointer);
            for(Pointer ptr:succs){
                workList.addEntry(ptr,delta);
            }
        }

        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me

        PointsToSet pointsToSet=new PointsToSet();
        pointsToSet.addObject(recv);

        List<Invoke> invokes = var.getInvokes();
        for(Invoke invoke:invokes){

            JMethod jMethod = resolveCallee(recv, invoke);      //dispatch 的方法
            VarPtr varPtr=new VarPtr(jMethod.getIR().getThis());
            workList.addEntry(varPtr,pointsToSet);

            if(callGraph.addEdge(new Edge<>(CallKind.VIRTUAL, invoke, jMethod))){
                callGraph.addReachableMethod(jMethod);

                List<Var> params = jMethod.getIR().getParams();
                List<Var> args = invoke.getInvokeExp().getArgs();

                //a表示args(传递参数)，p表示param(接收参数)
                for(int i=0;i<params.size();i++){
                    VarPtr paramPtr=new VarPtr(params.get(i));
                    VarPtr argPtr=new VarPtr(args.get(i));

                    addPFGEdge(argPtr,paramPtr);
                }

                List<Var> returnVars = jMethod.getIR().getReturnVars();
                Var lValue = invoke.getLValue();
                VarPtr lPtr=new VarPtr(lValue);

                for(Var each:returnVars){
                    VarPtr tmp=new VarPtr(each);

                    addPFGEdge(tmp,lPtr);
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
