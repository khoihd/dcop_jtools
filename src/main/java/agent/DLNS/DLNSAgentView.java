package agent.DLNS;

import communication.DCOPinfo;
import communication.PseudoTree;
import kernel.*;

import java.util.Arrays;
import java.util.HashMap;
import java.util.List;

/**
 * Created by ffiorett on 8/2/15.
 * todo: have only getters here. Move all setters to agentActions
 */
public class DLNSAgentView extends AgentView {
    // The variables of the agent's neighbors destroyed during current iteration.
    // It maps the agentID to its boolean value.
    protected HashMap<Long, Boolean> destroyedNeighbor;
    // The variables' values of the agent's neighbors during current iteration
    protected HashMap<Long, Integer> valueNeighborCheck;
    protected HashMap<Long, Integer> valueNeighborHat;

    // Agent Variable destroyed
    protected boolean varDestroyed;
    // The agent view of the pseudoTree at the k-th iteration
    protected PseudoTree pseudoTreeK;
    // The agent view of the pseudoTree
    protected PseudoTree pseudoTreeStar;

    // Constraint Evaluators
    protected Evaluator pCheckEvaluatorK;
    protected Evaluator pHatEvaluatorK;
    protected Evaluator pCheckEvaluatorStar;
    protected UpperBoundEvaluator pHatEvaluatorStar;
    protected UpperBoundTreeEvaluator pHatTreeEvaluatorStar;
    protected int lowerBoundK;
    protected int upperBoundK;
    protected int varCheckValueK;
    protected int varHatValueK;
    protected int currentIteration = 0;

    protected Evaluator nogoodsEvaluator;

    public DLNSAgentView(AgentState agentState) {
        super(agentState);
        destroyedNeighbor = new HashMap<>();
        valueNeighborCheck = new HashMap<>();
        valueNeighborHat   = new HashMap<>();

        pseudoTreeK    = new PseudoTree();
        pseudoTreeStar = new PseudoTree();

        pCheckEvaluatorK = new Evaluator();
        pHatEvaluatorK = new Evaluator();
        pCheckEvaluatorStar = new Evaluator();
        pHatEvaluatorStar = new UpperBoundEvaluator();
        pHatTreeEvaluatorStar = new UpperBoundTreeEvaluator();
        nogoodsEvaluator = new Evaluator();
    }

    public boolean isVarDestroyed() {
        return varDestroyed;
    }

    public PseudoTree getPseudoTreeK() {
        return pseudoTreeK;
    }

    public PseudoTree getPseudoTreeStar() {
        return pseudoTreeStar;
    }

    public void setVarValuesK(int[] values) {
        varCheckValueK = values[0];
        varHatValueK = values[1];
    }
    
    public boolean containsTrue(boolean[] arrays) {
    	for (boolean value: arrays) {
    		if (value) return true;
    	}
    	return false;
    }

    public class UpperBoundEvaluator extends Evaluator {

        // Array which mirrors super.constraints
        // it is set to true when a function has been evaluated already
        boolean[] isPrevOptConstraints;		// indicate previous optimized edge
        boolean[] isPrevSATOptConstraints;	// indicate previous SAT optimized edge 
        int[] prevOpt;		// save all the optimized values of previous iterations
        int[] prevSATOpt; 	// previous SAT iterations
        int[] j_stored;		// previous j iterations
        boolean[] isNSATConstraints;	// indicate which constraints is NOT SAT in previous iterations
        
        int[] constraintUB;
        int[] constraintLB;
        long[] scopeAgentsID;
        int[] scopeThetaIdx;  // only used to initialize Theta
        boolean prevSAT; 	// indicate previous iteration is SAT

        public UpperBoundEvaluator() {
            super();
        }

        @Override
        public void initialize(List<Long> agtsID) {
            super.initialize(agtsID);
            isPrevOptConstraints = new boolean[nConstraints];
            isPrevSATOptConstraints = new boolean[nConstraints];
            prevOpt	= new int[nConstraints];
            prevSATOpt = new int[nConstraints];
            j_stored = new int[nConstraints];
            isNSATConstraints = new boolean[nConstraints];
            constraintUB  = new int[nConstraints];
            constraintLB = new int[nConstraints];
            scopeAgentsID = new long[2*nConstraints];
            scopeThetaIdx = new int[2*nConstraints];
            prevSAT = false;
            Arrays.fill(isPrevOptConstraints, false);
            Arrays.fill(isPrevSATOptConstraints, false);
            Arrays.fill(isNSATConstraints, false);

            for (int i = 0; i < nConstraints; i++) {
                Constraint c = constraints.get(i);
                constraintUB[i] = c.getBestValue();
                prevOpt[i] = c.getBestValue();
                j_stored[i] = c.getBestValue();
                prevSATOpt[i] = c.getBestValue();
                constraintLB[i] = c.getWorstValue();
                long id0 = c.getScope(0).getOwnerAgent().getID();
                long id1 = c.getScope(1).getOwnerAgent().getID();
                scopeAgentsID[2*i] = id0 == getAgentID() ? -1 : id0;
                scopeAgentsID[2*i + 1] = id1 == getAgentID() ? -1 : id1;

                scopeThetaIdx[2*i] = (int)id0;
                scopeThetaIdx[2*i + 1] = (int)id1;
            }
        }

        public void resetRelaxedConstraints() {
            Arrays.fill(isPrevOptConstraints, false);
            for (int i = 0; i < nConstraints; i++){
                Constraint c = constraints.get(i);
                // initially set constraintUB to the best value
                // add the worst value c.getWorstValue();
                constraintUB[i] = c.getBestValue();
                constraintLB[i] = c.getWorstValue();
            }
        }

        @Override
        public int evaluate(Tuple values, boolean update_j) {
//        	System.out.println("Called in DPOP Evaluator");
            int aggregateValue = 0;
            int tempUB = 0;

            boolean x0inLN, x1inLN;
            prevSAT = containsTrue(isNSATConstraints) ? false : true;            
            Arrays.fill(isNSATConstraints, false);
            	
            for (int c = 0; c < nConstraints; c++) {
                x0inLN = scopeAgentsID[2*c + 0] == -1 ? varDestroyed
                        : destroyedNeighbor.get(scopeAgentsID[2*c + 0]);
                x1inLN = scopeAgentsID[2*c + 1] == -1 ? varDestroyed
                        : destroyedNeighbor.get(scopeAgentsID[2*c + 1]);
                
                // if the constraint is in LN k and k-1 => f(k) + f(k-1) - min_f, // update past = current
                // if the constraint is in LN k			=> f(k)					, // update past = current
                // if the constraint is in LN k-1		=> f(k-1)
                // otherwise							=> max_f
                                
                // in k
                if (x0inLN && x1inLN) {
                    pair.set(0, values.get(varIDToValIdx[constraintScope.get(c * 2 + 0)]));
                    pair.set(1, values.get(varIDToValIdx[constraintScope.get(c * 2 + 1)]));
                    int value = constraints.get(c).getValue(pair);
                    
                    if (prevSAT) {
                    	prevSATOpt[c] = prevOpt[c];
                    	isPrevSATOptConstraints[c] = isPrevOptConstraints[c];
                    }
                    
                    if (update_j) {
                    	j_stored[c] = prevSATOpt[c];
                    }
                    
                    // SAT
                    if (Constraint.isSat(value)) {
                        // in k and k-1
                    	if (isPrevSATOptConstraints[c]) {
//                        	tempUB = value + prevSATOpt[c] - constraintLB[c];
                        	tempUB = value + j_stored[c] - constraintLB[c];
                        	isPrevOptConstraints[c] = true;
                        	prevOpt[c] = value;
                        }
                    	// in k only, not in k-1
                        else {
                        	tempUB = value;
                        	isPrevOptConstraints[c] = true;
                        	prevOpt[c] = value;
                        }
                    	
                    	// KHOI: Theta indicate optimized constraints???
                        DCOPinfo.Theta[scopeThetaIdx[2*c]][scopeThetaIdx[2*c+1]] = true;
                        DCOPinfo.Theta[scopeThetaIdx[2*c+1]][scopeThetaIdx[2*c]] = true;
                    }
                    // Not SAT
                    else {
                    	//set flag that this iteration is not SAT
//                    	tempUB = constraintUB[c];
                    	tempUB = Integer.MIN_VALUE;
                    	isPrevOptConstraints[c] = false;
                    	prevOpt[c] = Integer.MIN_VALUE;
                    	isNSATConstraints[c] = true;
                    }
                }
                // in k-1
                else if (isPrevSATOptConstraints[c]) {
//                	tempUB = prevOpt[c];
//                	tempUB = prevSATOpt[c];
                	tempUB = j_stored[c];
                	isPrevOptConstraints[c] = false;
                }
                // not either in k or j
                else {
                	tempUB = constraintUB[c];
                	isPrevOptConstraints[c] = false;
                }
                aggregateValue += tempUB;
            }
                        
            return aggregateValue;
        }

    }

    public class UpperBoundTreeEvaluator extends UpperBoundEvaluator {

        // Here i don't care about frozen and not frozen variables -
        // for an edge (i,j) in order to have been optimized it must be that either
        // j = Pi or j \in C_i (i.e., i = Pj). All other edges where related to pseudo-parents or
        // frozen variables.
        @Override
        public int evaluate(Tuple values, boolean update_j) {
//        	System.out.println("Called in TREE Evaluator");
            int aggregateValue = 0;
            int tempUB = 0;

            long otherId = 0;
            long parKId = pseudoTreeK.isRoot() ? -1 : pseudoTreeK.getParent().getId();
            prevSAT = containsTrue(isNSATConstraints) ? false : true;            
            Arrays.fill(isNSATConstraints, false);
            	
            for (int c = 0; c < nConstraints; c++) {
                otherId = (scopeAgentsID[2*c + 0] == -1) ? scopeAgentsID[2*c + 1] : scopeAgentsID[2*c + 0];
                
                // if the constraint is in LN k and k-1 => f(k) + f(k-1) - min_f, // update past = current
                // if the constraint is in LN k			=> f(k)					, // update past = current
                // if the constraint is in LN k-1		=> f(k-1)
                // otherwise							=> max_f
                                
                // in k
                if ( otherId == parKId || pseudoTreeK.getChildren().contains(DCOPinfo.agentsRef[(int)otherId])) {
                    pair.set(0, values.get(varIDToValIdx[constraintScope.get(c * 2 + 0)]));
                    pair.set(1, values.get(varIDToValIdx[constraintScope.get(c * 2 + 1)]));
                    int value = constraints.get(c).getValue(pair);
                    
                    if (prevSAT) {
                    	prevSATOpt[c] = prevOpt[c];
                    	isPrevSATOptConstraints[c] = isPrevOptConstraints[c];
                    }
                    
                    if (update_j) {
                    	j_stored[c] = prevSATOpt[c];
                    }
                    
                    // SAT
                    if (Constraint.isSat(value)) {
                        // in k and k-1
                    	if (isPrevSATOptConstraints[c]) {
//                        	tempUB = value + prevSATOpt[c] - constraintLB[c];
                        	tempUB = value + j_stored[c] - constraintLB[c];
                        	isPrevOptConstraints[c] = true;
                        	prevOpt[c] = value;
                        }
                    	// in k only, not in k-1
                        else {
                        	tempUB = value;
                        	isPrevOptConstraints[c] = true;
                        	prevOpt[c] = value;
                        }
                    	
                    	// KHOI: Theta indicate optimized constraints???
                        DCOPinfo.Theta[scopeThetaIdx[2*c]][scopeThetaIdx[2*c+1]] = true;
                        DCOPinfo.Theta[scopeThetaIdx[2*c+1]][scopeThetaIdx[2*c]] = true;
                    }
                    // Not SAT
                    else {
                    	//set flag that this iteration is not SAT
//                    	tempUB = constraintUB[c];
                    	tempUB = Integer.MIN_VALUE;
                    	isPrevOptConstraints[c] = false;
                    	prevOpt[c] = Integer.MIN_VALUE;
                    	isNSATConstraints[c] = true;
                    }
                }
                // in k-1
                else if (isPrevSATOptConstraints[c]) {
//                	tempUB = prevOpt[c];
//                	tempUB = prevSATOpt[c];
                	tempUB = j_stored[c];
                	isPrevOptConstraints[c] = false;
                }
                // not either in k or j
                else {
                	tempUB = constraintUB[c];
                	isPrevOptConstraints[c] = false;
                }
                aggregateValue += tempUB;
            }
                        
            return aggregateValue;
        }

    }

}
