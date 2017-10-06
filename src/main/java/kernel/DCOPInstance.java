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

import java.util.Collection;
import java.util.HashMap;

/**
 * Created by ffiorett on 7/7/15.
 */
public class DCOPInstance {
    private int optimizationType;

    // HashMaps containing the DCOp information
    private HashMap<String, Long> agentIDHashMap;
    private HashMap<Long, AgentState> agentHashMap;

    private HashMap<String, Long> constraintIDHashMap;
    private HashMap<Long, Constraint> constraintHashMap;

    private HashMap<String, Long> variableIDHashMap;
    private HashMap<Long, Variable> variableHashMap;


    public DCOPInstance() {
        agentIDHashMap = new HashMap<String, Long>();
        agentHashMap = new HashMap<Long, AgentState>();
        constraintIDHashMap = new HashMap<String, Long>();
        constraintHashMap = new HashMap<Long, Constraint>();
        variableIDHashMap = new HashMap<String, Long>();
        variableHashMap = new HashMap<Long, Variable>();
    }

    public void setOptimization(Boolean maximize) {
        if(maximize) {
            optimizationType = Constants.OPT_MAXIMIZE;
        } else {
            optimizationType = Constants.OPT_MINIMIZE;
        }
    }

    public int getOptimizationType() {
        return optimizationType;
    }

    public void addAgent(AgentState agentState) {
        agentIDHashMap.put(agentState.getName(), agentState.getID());
        agentHashMap.put(agentState.getID(), agentState);
    }

    public AgentState getAgent(long ID) {
        return agentHashMap.get(ID);
    }

    public AgentState getAgent(String name) {
        return agentHashMap.get(agentIDHashMap.get(name));
    }

    public long getAgentID(String name) {
        return agentIDHashMap.get(name);
    }

    public Collection<AgentState> getDCOPAgents() {
        return agentHashMap.values();
    }

    public void addVariable(Variable variable) {
        variableIDHashMap.put(variable.getName(), variable.getID());
        variableHashMap.put(variable.getID(), variable);
    }

    public Variable getVariable(long ID) {
        return variableHashMap.get(ID);
    }

    public Variable getVariable(String name) {
        return variableHashMap.get(variableIDHashMap.get(name));
    }

    public long getVariableID(String name) {
        return variableIDHashMap.get(name);
    }

    public Collection<Variable> getDCOPVariable() {
        return variableHashMap.values();
    }

    public void addConstraint(Constraint constraint) {
        constraintIDHashMap.put(constraint.getName(), constraint.getID());
        constraintHashMap.put(constraint.getID(), constraint);
    }

    public Constraint getConstraint(long ID) {
        return constraintHashMap.get(ID);
    }

    public Constraint getConstraint(String name) {
        return constraintHashMap.get(constraintIDHashMap.get(name));
    }

    public long getConstraintID(String name) {
        return constraintIDHashMap.get(name);
    }

    public Collection<Constraint> getDCOPConstraint() {
        return constraintHashMap.values();
    }
}
