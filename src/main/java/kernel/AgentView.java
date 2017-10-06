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

//import communication.ComAgent;
import communication.DCOPinfo;

import java.util.ArrayList;
//import java.util.Arrays;
//import java.util.Collections;
import java.util.List;

/**
 * Created by ffiorett on 7/17/15.
 * This class is used to view the agent's content: Variables values, constraints, and domains.
 */
public class AgentView {
    protected final AgentState agentState;

    public AgentView(AgentState agentState) {
        this.agentState = agentState;
    }

    public String getAgentName() {
        return agentState.getName();
    }

    public long getAgentID() {return agentState.getID();}
    /**
     * Gets the value currently held by the variable queried.
     * @param pos The position of the variable in the array agentState.variables.
     */
    public int getVariableValue(int pos) {
        return agentState.getVariable(pos).getValue();
    }

    public int getVariableValue() {
        return getVariableValue(0);
    }

    public int getDomainMin(int pos) {
        return agentState.getVariable(pos).getDomain().getMin();
    }

    public int getDomainMin() {
        return getDomainMin(0);
    }

    public int getDomainMax(int pos) {
        return agentState.getVariable(pos).getDomain().getMax();
    }

    public int getDomainMax() {
        return getDomainMax(0);
    }

    public int getDomainSize(int pos) {
        return agentState.getVariable(pos).getDomain().size();
    }

    public int getDomainSize() {
        return getDomainSize(0);
    }

    /**
     * @return The worst aggregated value, assuming this is a maximization problem.
     */
    public int getAggregatedLB() {
        int res = 0;
        for (Constraint c : agentState.getConstraints()) {
            res += c.getWorstValue();
        }
        return res;
    }

    /**
     * @return The best aggregated value, assuming this is a maximization problem.
     */
    public int getAggregatedUB() {
        int res = 0;
        for (Constraint c : agentState.getConstraints()) {
            res += c.getBestValue();
        }
        return res;
    }


    /**
     * Class used to evaluate constraints of a set of variables.
     * @note: only binary constraints.
     */
    public class Evaluator {
        protected int[] varIDToValIdx;
        protected List<Integer> constraintScope;
        protected List<Constraint> constraints;
        protected int nConstraints;
        protected Tuple pair = new Tuple(2);

        public Evaluator() {
            varIDToValIdx = new int[DCOPinfo.nbAgents];
            constraints   = new ArrayList<>();
            constraintScope = new ArrayList<>();
        }

        /**
         * Extracts the list of constraints of this agent which contain, in their scope,
         * the agents in the agtsID given in input.
         * @param agtsID The list of agents to be involved in the constraint evaluation.
         */
        public void initialize(List<Long> agtsID) {
            constraints.clear();
            constraintScope.clear();
            nConstraints = 0;

            List<Variable> variables = new ArrayList<>();

            // This agent
            Variable vSelf = agentState.getVariable();
            if (agtsID.contains(agentState.getID())) variables.add(vSelf);
            int idxSelf = agtsID.indexOf(agentState.getID()); // index of this agent in agtsID * and Tuple:values
            varIDToValIdx[(int)vSelf.getID()] = idxSelf;

            // Neighbors
            for (AgentState agtState : agentState.getNeighbors()) {
                Variable v = agtState.getVariable();
                if (agtsID.contains(agtState.getID())) {
                    variables.add(v);
                }
                int agtIdx = agtsID.indexOf(agtState.getID()); // index of this agent in agtsID * and Tuple:values
                varIDToValIdx[(int)v.getID()] = agtIdx;
            }

            // Save constraint which invovles all the variables controlled by some agent in agtsID
            for (Constraint c : agentState.getConstraints()) {
                if (c.getScope().contains(vSelf) && variables.containsAll(c.getScope())) {
                    constraintScope.add((int) c.getScope(0).getID());
                    constraintScope.add((int) c.getScope(1).getID());
                    constraints.add(c);
                    nConstraints++;
                }
            }
        }

        public int evaluate(Tuple values, boolean j_updated) {
//        	System.out.println("Called in AgentView");

            if (!values.isValid()) return Constants.worstValue();

            int aggregateValue = 0;

            for (int c = 0; c < nConstraints; c++) {
                pair.set(0, values.get(varIDToValIdx[ constraintScope.get(c*2 + 0) ] ));
                pair.set(1, values.get(varIDToValIdx[ constraintScope.get(c*2 + 1) ] ));
                int value = constraints.get(c).getValue(pair);
                if (Constraint.isUnsat(value))
                    return Constants.worstValue();
                aggregateValue += value;
            }
            return aggregateValue;
        }

        /**
         * Extracts the list of agentsID whose given the values in input, have unsatisfied
         * constraint with the current agent.
         * @param values
         * @return
         */
        public ArrayList<Long> getNogoods(Tuple values) {
            ArrayList<Long> nogoods = new ArrayList<>();

            for (int c = 0; c < nConstraints; c++) {
                pair.set(0, values.get(varIDToValIdx[ constraintScope.get(c*2 + 0) ] ));
                pair.set(1, values.get(varIDToValIdx[ constraintScope.get(c*2 + 1) ] ));
                int value = constraints.get(c).getValue(pair);
                if (Constraint.isUnsat(value)) {
                    long id0 = constraints.get(c).getScope(0).getOwnerAgent().getID();
                    long id1 = constraints.get(c).getScope(1).getOwnerAgent().getID();

                    if (getAgentID() == id0)
                        nogoods.add(id1);
                    else
                        nogoods.add(id0);
                }
            }
            return nogoods;
        }
    }

}
