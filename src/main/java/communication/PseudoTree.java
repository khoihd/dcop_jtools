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

package communication;

/**
 * Created by ffiorett on 8/4/15.
 */

import java.util.ArrayList;
import java.util.List;

/**
 * Agent's address in PseudoTree Ordering.
 */
public class PseudoTree {
    protected ComAgent parent;
    protected List<ComAgent> children;
    protected List<ComAgent> pseudoParents;
    protected List<ComAgent> pseudoChildren;

    public PseudoTree() {
        parent = null;
        children = new ArrayList<>();
        pseudoParents = new ArrayList<>();
        pseudoChildren = new ArrayList<>();
    }

    public boolean isRoot() {
        return parent == null;
    }

    public boolean isLeaf() {
        return children.isEmpty() && parent != null;
    }

    public ComAgent getParent() {
        return parent;
    }

    public void setParent(ComAgent parent) {
        this.parent = parent;
    }

    public List<ComAgent> getChildren() {
        return children;
    }

    public void addChild(ComAgent agt) {
        if (!children.contains(agt)) // TODO: speed-up by removing this check
            children.add(agt);
    }

    public void removeChild(ComAgent agt) {
        if (children.contains(agt)) // TODO: speed-up by removing this check
            children.remove(agt);
    }
    public List<ComAgent> getPseudoParents() {
        return pseudoParents;
    }

    public void addPseudoParent(ComAgent agt) {
        if (!pseudoParents.contains(agt)) // TODO: speed-up by removing this check
            pseudoParents.add(agt);
    }

    public void addPseudoChild(ComAgent agt) {
        if (!pseudoChildren.contains(agt)) // TODO: speed-up by removing this check
            pseudoChildren.add(agt);
    }

    public void update(PseudoTree other) {
        this.parent = other.parent;
        this.children = other.children;
        this.pseudoParents = other.pseudoParents;
        this.pseudoChildren = other.pseudoChildren;
    }

    public void clear() {
        parent = null;
        children.clear();
        pseudoParents.clear();
    }

    @Override
    public String toString() {
        String ret = "PseudoTree: P= ";
        if(parent==null) ret += "Nil C={";
        else ret += parent.getName() + " C={";

        for (ComAgent c : children)
            ret += c.getName() + ",";
        ret += "} PP={";
        for (ComAgent pp : pseudoParents)
            ret += pp.getName() + ",";
        ret += "}";
        return ret;
    }
}

