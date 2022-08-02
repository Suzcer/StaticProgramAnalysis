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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;
import pascal.taie.util.collection.Pair;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    /**
     * 本次只关注代码不可达和无用赋值
     * 代码不可达检测：（ If 和 Switch ）
     * 应用常量传播分析，如果是常量则不进入相应的不可达分支
     * <p>
     * 无用赋值检测： （ Assign ）
     * 应用活跃变量分析，如果左边的变量是一个无用变量，则标记为无用的赋值
     */
    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        Set<Stmt> liveCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode

        Queue<Stmt> stmtQueue = new LinkedList<>();
        stmtQueue.add(cfg.getEntry());
        while (!stmtQueue.isEmpty()) {
            Stmt stmt = stmtQueue.poll();
            if (cfg.isExit(stmt)) {
                liveCode.add(stmt);
                continue;
            }
            if (deadCode.contains(stmt) || liveCode.contains(stmt)) continue;

            // 注意运用的算法，可以算作 广搜
            if (stmt instanceof If) {

                liveCode.add(stmt);
                // evaluate 评估 if 语句的值
                Value condition_val = ConstantPropagation.evaluate(((If) stmt).getCondition(), constants.getInFact(stmt));
                if (condition_val.isConstant()) {
                    // 0 就要将If_False的语句存入
                    if (condition_val.getConstant() == 0) {
                        for (Edge<Stmt> e : cfg.getOutEdgesOf(stmt)) {
                            if (e.getKind() == Edge.Kind.IF_FALSE) {
                                stmtQueue.add(e.getTarget());
                                break;
                            }
                        }
                    } else {
                        for (Edge<Stmt> e : cfg.getOutEdgesOf(stmt)) {
                            if (e.getKind() == Edge.Kind.IF_TRUE) {
                                stmtQueue.add(e.getTarget());
                                break;
                            }
                        }
                    }
                } else {
                    //如果不是常量，则都有可能
                    stmtQueue.addAll(cfg.getSuccsOf(stmt));
                }

                //DefinitionStmt中只可能是这个产生死代码，因为不是程序间分析
            } else if (stmt instanceof SwitchStmt) {

                liveCode.add(stmt);
                Value condition_val = ConstantPropagation.evaluate(((SwitchStmt) stmt).getVar(), constants.getInFact(stmt));

                if (condition_val.isConstant()) {
                    if (((SwitchStmt) stmt).getCaseValues().contains(condition_val.getConstant())) {

                        for (Edge<Stmt> e : cfg.getOutEdgesOf(stmt)) {
                            if (e.isSwitchCase() && e.getCaseValue() == condition_val.getConstant()) {
                                stmtQueue.add(e.getTarget());
                            }
                        }
                    } else {
                        stmtQueue.add(((SwitchStmt) stmt).getDefaultTarget());
                    }
                } else {
                    stmtQueue.addAll(cfg.getSuccsOf(stmt));
                }

            } else if (stmt instanceof AssignStmt<?, ?> assignStmt) {
                if (hasNoSideEffect(assignStmt.getRValue()) && assignStmt.getLValue() instanceof Var lVar &&
                        !liveVars.getOutFact(assignStmt).contains(lVar)) deadCode.add(stmt);
                else liveCode.add(stmt);
                stmtQueue.addAll(cfg.getSuccsOf(stmt));
            } else {
                // 如果就是正常的语句也是顺序执行，也当作 liveCode,
                // 这样子可以实现 switch-case中，case以后没有 break 的情况；若有break，那 Succs 中也没有下一个 case 语句
                // e.g.  int a=1;
                //       int x=a+3;
                liveCode.add(stmt);
                stmtQueue.addAll(cfg.getSuccsOf(stmt));
            }
        }
        //liveCode 和 deadCode 的转换

        for (Stmt s : cfg.getIR().getStmts())
            if (!liveCode.contains(s)) deadCode.add(s);

        deadCode.remove(cfg.getEntry());
        deadCode.remove(cfg.getExit());

        return deadCode;
    }

    public void KUISC() {
        //  注意还有包的导入  import java.utils.Scanner
        //  注意输入的时候要有提示输入的内容

        Scanner input = new Scanner(System.in);
        System.out.print("Please input N:");
        int N = input.nextInt();
        System.out.println("Please input N numbers");
        int[] A = new int[N];
        for (int i = 0; i < N; i++) {
            A[i] = input.nextInt();
        }
        for (int j = 1; j <= N - 1; j++) {
            for (int i = 1; i <= N - 1; i++) {
                if (A[i] > A[i + 1]) {
                    int X = A[i];
                    A[i] = A[i + 1];
                    A[i + 1] = X;
                }
            }
        }
        System.out.println("After sorting:");
        for (int i = 0; i < N; i++)
            System.out.print(A[i]);
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
