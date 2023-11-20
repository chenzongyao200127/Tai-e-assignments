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

package pascal.taie.analysis.pta.core.heap;

import pascal.taie.ir.exp.ReferenceLiteral;
import pascal.taie.ir.stmt.New;

/**
 * Represents of heap models for heap objects.
 */
public interface HeapModel {

    /**
     * @return the abstract object for given new statement.
     * 这个类表示堆模型（即堆抽象），它用来对堆对象进行建模。
     * 给定一个 New 语句（即创建点 allocation site），
     * 你可以使用 HeapModel 的 getObj(New) 方法来获得与它对应的抽象对象（即 Obj）。
     * 因为我们采用了第 8 讲课件第 44 页中介绍的创建点抽象，
     * 所以该方法为每个 New 语句返回一个唯一的抽象对象。
     */
    Obj getObj(New allocSite);

    /**
     * @return the constant object for given value.
     */
    Obj getConstantObj(ReferenceLiteral value);
}
