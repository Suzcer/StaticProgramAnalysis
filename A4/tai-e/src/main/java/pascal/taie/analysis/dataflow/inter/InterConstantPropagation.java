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

import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;

import java.util.Collection;
import java.util.List;
import java.util.Optional;

import static pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation.canHoldInt;
import static pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation.evaluate;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
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

    /**
     * transferNode() 会返回此次 transfer 是否改变了 OUT fact
     */
    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me

        //TODO 不太理解
        if (!out.equals(in)) {
            out.copyFrom(in);
            return true;
        }
        return false;
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        //非函数调用边可以使用之前的代码
        return cp.transferNode(stmt, in, out);
    }

    /**
     * 恒等函数，不会有任何改变
     */
    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out.copy();
    }

    /**
     * kill左值（如果存在）
     */
    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        CPFact copy = out.copy();
        Optional<LValue> lv = edge.getSource().getDef();
        if (lv.isPresent()) {
            LValue lValue = lv.get();
            if (lValue instanceof Var) {
                copy.remove((Var) lValue);
            }
        }
        return copy;
    }

    /**
     * 将 参数 传入被调用的方法中
     * 返回的是 被调用方法的 inFact
     */
    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me

        Stmt stmt = edge.getSource();
        assert (stmt instanceof Invoke);

        CPFact invokeInFact = newInitialFact();

        //params 是写死的参数， args 是传入的参数(因此需要进一步在args中取值传入 params 中)
        List<Var> args = ((Invoke) stmt).getInvokeExp().getArgs();
        List<Var> params = edge.getCallee().getIR().getParams();

        for (int i = 0; i < args.size(); i++)
            invokeInFact.update(params.get(i), callSiteOut.get(args.get(i)));

        return invokeInFact;
    }

    /**
     * returnOut 可能有多个值，需要思考一下该怎么处理
     */
    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me

        Invoke invoke = (Invoke) edge.getCallSite();
        Value val = Value.getUndef();

        //对于每个返回值均需要进行汇合
        for (Var var : edge.getReturnVars())
            val = cp.meetValue(val, returnOut.get(var));

        CPFact returnFact = new CPFact();

        if (invoke.getLValue() != null)
            returnFact.update(invoke.getLValue(), val);

        return returnFact;
    }
}
