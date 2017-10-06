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
import java.util.Comparator;

/**
 * Created by ffiorett on 7/7/15.
 * This is the agent state, i.e., all what agents owns and knows about the world.
 * It contains its own variables, the view on the constraints it controls and the neigbhors.
 */
public class AgentState {

    private ArrayList<Variable> variables;
    private ArrayList<Constraint> constraints;
    private ArrayList<AgentState> neighbors;

    private String name;
    private long ID;

    public AgentState(String name, long ID) {
        this.name = name;
        this.ID = ID;

        variables = new ArrayList<Variable>();
        constraints = new ArrayList<Constraint>();
        neighbors = new ArrayList<AgentState>();
    }

    public Variable getVariable() {
        return variables.get(0);
    }

    public Variable getVariable(int pos) {
        return variables.get(pos);
    }

    public ArrayList<Variable> getVariables() {
        return variables;
    }

    public Constraint getConstraint(int pos) {
        return constraints.get(pos);
    }

    public ArrayList<Constraint> getConstraints() {
        return constraints;
    }

    public ArrayList<AgentState> getNeighbors() {
        return neighbors;
    }

    public void registerVariable(Variable variable) {
        variables.add(variable);
        variable.registerOwnerAgent(this);
    }

    public void registerConstraint(Constraint constraint) {
        constraints.add(constraint);

        for (Variable scope : constraint.getScope()) {
            registerNeighbor(scope.getOwnerAgent());
        }
    }

    public void registerNeighbor(AgentState agentState) {
        if (this == agentState) return;
        if (!neighbors.contains(agentState)) {
            neighbors.add(agentState);
        }
        neighbors.sort(new AgentStateComparator());
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    public long getID() {
        return ID;
    }

    public void setID(long ID) {
        this.ID = ID;
    }

    @Override
    public String toString() {
        String ret = "Agent " + name + " (" + ID + ")";
        ret += " [Varsiables = ";
        for (Variable v : variables) ret += v.getName() + " ";
        ret += "] Constraints = ";
        for (Constraint c : constraints) ret += c.getName() + " ";
        ret += "] Neighbors = ";
        for (AgentState a : neighbors) ret += a.getName() + " ";
        return ret;
    }

    class AgentStateComparator implements Comparator<AgentState> {
        @Override
        public int compare(AgentState o1, AgentState o2) {
            return o1.getID() < o2.getID() ? -1 : 1;
        }
    }
}