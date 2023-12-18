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

package pascal.taie.analysis.pta.core.cs.selector;

import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.context.ListContext;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.language.classes.JMethod;

/**
 * Implementation of 2-object sensitivity.
 */
public class _2ObjSelector implements ContextSelector {

    @Override
    public Context getEmptyContext() {
        return ListContext.make();
    }

    @Override
    public Context selectContext(CSCallSite callSite, JMethod callee) {
        // Return the context associated with the call site
        // This method is used for context selection in simpler cases
        return callSite.getContext();
    }

    @Override
    public Context selectContext(CSCallSite callSite, CSObj recv, JMethod callee) {
        // Retrieve the context associated with the receiver object
        Context context = recv.getContext();

        // Create a new context based on the length of the existing context
        return switch (context.getLength()) {
            // If the length is 0, create a new context with the receiver object only
            case 0 -> ListContext.make(recv.getObject());
            // If the length is 1, create a new context with the first element and the receiver object
            case 1 -> ListContext.make(context.getElementAt(0), recv.getObject());
            // In other cases, create a new context with the second element and the receiver object
            default -> ListContext.make(context.getElementAt(1), recv.getObject());
        };
    }

    @Override
    public Context selectHeapContext(CSMethod method, Obj obj) {
        // Retrieve the context of the method
        Context context = method.getContext();

        // Handle the case where the context length is zero
        if (context.getLength() == 0) {
            // Return an empty context for methods with no existing context
            return getEmptyContext();
        }
        // Create a new context with the last element of the existing context
        return ListContext.make(context.getElementAt(context.getLength() - 1));
    }
}
