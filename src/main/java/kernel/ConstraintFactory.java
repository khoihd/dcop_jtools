/*
 * Copyright (c) 2015.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */

package kernel;

import java.util.ArrayList;

/**
 * Created by ffiorett on 7/8/15.
 */
public class ConstraintFactory {
    private static long constraintIDcount = 0;

    public static Constraint getConstraint(String name, ArrayList<Variable> scope, Integer defaultValue, String semantics) {
        Constraint constraint = null;
        if (semantics.equalsIgnoreCase("soft")) {
            if (scope.size() == 2)
                constraint = new TableBinaryConstraint(name, constraintIDcount++, scope, defaultValue);
            else
                constraint = new TableConstraint(name, constraintIDcount++, scope, defaultValue);
        }

        // Register the constraint in each of the participating variables.
        if (constraint != null) {
            for (Variable var : scope) {
                var.registerParticipatingConstraint(constraint);
            }
        }

        return constraint;
    }
}
