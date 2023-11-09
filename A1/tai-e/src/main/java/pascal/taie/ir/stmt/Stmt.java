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

package pascal.taie.ir.stmt;

import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.RValue;
import pascal.taie.util.Indexable;

import java.util.List;
import java.util.Optional;

/**
 * Representation of statements in Tai-e IR.
 * 这是 Tai-e 的 IR 中的另一个关键接口，它用于表示程序中的所有语句。
 * 对于一个典型的程序设计语言来说，每个表达式都属于某条特定的语句。
 * 为了实现活跃变量分析，你需要获得某条语句中定义或使用的所有表达式中的变量。
 */
public interface Stmt extends Indexable {

    /**
     * @return the index of this Stmt in the container IR.
     */
    @Override
    int getIndex();

    void setIndex(int index);

    /**
     * @return the line number of this Stmt in the original source file.
     * If the line number is unavailable, return -1.
     */
    int getLineNumber();

    void setLineNumber(int lineNumber);

    /**
     * @return the (optional) left-value expression defined in this Stmt.
     * In Tai-e IR, each Stmt can define at most one expression.
     */
    Optional<LValue> getDef();

    /**
     * @return a list of right-value expressions used in this Stmt.
     */
    List<RValue> getUses();

    /**
     * @return true if execution after this statement could continue at
     * the following statement, otherwise false.
     */
    boolean canFallThrough();

    <T> T accept(StmtVisitor<T> visitor);
}
