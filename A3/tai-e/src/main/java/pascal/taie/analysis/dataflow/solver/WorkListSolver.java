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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.ArrayDeque;
import java.util.Queue;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me

        //讲义通过比较 old_OUT 和 OUT[B] 来决定后继节点是否应当加入 worklist 中;
        // Tai-e 中 transferNode() 会返回此次 transfer 是否改变了 OUT fact。

        Queue<Node> workList = new ArrayDeque<>();
        for (Node node : cfg) workList.add(node);

        while (!workList.isEmpty()) {
            Node node = workList.poll();
            Fact outFact = result.getOutFact(node);
            Fact inFact = result.getInFact(node);

            for (Node pred : cfg.getPredsOf(node)) analysis.meetInto(result.getOutFact(pred), inFact);

            if (analysis.transferNode(node, inFact, outFact)) {
                for (Node succ : cfg.getSuccsOf(node)) {
                    if (!workList.contains(succ)) workList.add(succ);
                }
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me

        boolean changed = true;

        while (changed) {
            changed = false;
            for (Node node : cfg) {
                if(cfg.isExit(node)) continue;

                //更改 OUT
                result.setOutFact(node, analysis.newInitialFact());     //去除原有的内容
                for (Node succ : cfg.getSuccsOf(node)) {
                    Fact succInFact = result.getInFact(succ);
                    analysis.meetInto(succInFact, result.getOutFact(node));
                }
                //更改 IN
                boolean change = analysis.transferNode(node, result.getInFact(node), result.getOutFact(node));
                changed = change || changed;                            //只要一个改变即视为改变
            }
        }

    }
}
