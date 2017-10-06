package agent.DLNS;

import communication.ComAgent;
import communication.DCOPagent;
import communication.DCOPinfo;
import communication.PseudoTree;
import kernel.AgentState;
import kernel.Constants;
import kernel.Constraint;

import java.util.Arrays;
import java.util.List;
import java.util.Stack;


/**
 * Created by ffiorett on 7/31/15.
 */
public class DLNSagent extends DCOPagent {

    private int k;
    private int lowerBound;
    private int upperBound;
    private int nbIterations;
//    private long timeoutMs;
    private DLNSAgentView agentView;
    private DLNSAgentActions agentActions;

    private DestroyPhase    destroyPhase;
    private RepairPhase     repairPhase;
    private PseudoTreeBuilder ptBuilder;
    
//    public static int 		j; 
//    private int				f_j;
//    private static int		UB_j;	
    private int currentLeastUB;

	public DLNSagent(ComAgent statsCollector, AgentState agentState, List<Object> parameters) {

        super(statsCollector, agentState.getName(), agentState.getID());

        String destroyType = (String)parameters.get(0);
        String repairType = (String)parameters.get(1);
        int nbIter = (int)parameters.get(2);
//        long timeout = (long)parameters.get(3);

        this.nbIterations = nbIter;
//        this.timeoutMs = timeout;
        this.agentView = new DLNSAgentView(agentState);
        this.agentActions = new DLNSAgentActions(agentState);

        // TODO: Factory method for repair and destroy
        if (destroyType.equals("RAND")) this.destroyPhase = new RandomDestroy(this);
        else if (destroyType.equals("MEETINGS")) this.destroyPhase = new MeetingDestroy(this);

        if (repairType.equals("GDBR")) this.repairPhase = new BoundedRepairDPOP(this);
        else if (repairType.equals("TDBR")) this.repairPhase = new TreeBoundedRepair(this);

        this.ptBuilder   = new PseudoTreeBuilder();

        k = 0;
        lowerBound = 0;//getAgentView().getAggregatedLB();
        upperBound = Constants.infinity;//getAgentView().getAggregatedUB();
        
//        j = 0;
//        f_j = 0;
//        UB_j = Constants.infinity;
        
        currentLeastUB = Integer.MAX_VALUE;
    }

    @Override
    protected void onReceive(Object message, ComAgent sender) {
        super.onReceive(message, sender);

        if (message instanceof DestroyPhase.Message) {
            destroyPhase.onReceive((DestroyPhase.Message)message, sender);
        }
        else if (message instanceof RepairPhase.Message) {
            repairPhase.onReceive((RepairPhase.Message)message, sender);
        }
        else if (message instanceof  PTStarInfoMessage) {
            PTStarInfoMessage ptInfo = (PTStarInfoMessage) message;
            getAgentView().pseudoTreeStar.update(ptInfo.getTreeAgent());
            ptBuilder.recvPTinfo = true;
        }
    }


    @Override
    protected boolean terminationCondition() {
        return (k >= nbIterations);// || getAgentStatistics().getStopWatch().getMilliTime() > timeoutMs) ;
    }

    @Override
    protected void onStart() {
        // Iteration number and bounds already set.

        // Randomly initialize the value of this variable
        getAgentActions().setVariableVariableAtRandom();
        //getAgentActions().setVariableValue(1); // todo: remove this and enable the above;

        ptBuilder.start();
        while (!ptBuilder.isTerminated()) {
            await();
        }
        destroyPhase.initialize();
        repairPhase.initialize();

        getAgentStatistics().getStopWatch().reset();
        getAgentStatistics().getStopWatch().start();

        int prevMsgSent = 0;
        while (!terminationCondition()) {
            k++;
            getAgentView().currentIteration = k;
            DLNScycle();
            getAgentStatistics().updateIterationStats();

            if (isLeader()) {
            	//KHOI: calculate j here!
            	//Initially, if k=1, update j=1
            	//Agent leader compares current UB with UB_j (stored)
            	//If UB < storedUB => update f_j = true
            	
            	//Next iterations, if update f_j = true; f_j = f_{k-1}            	           
            	
                getAgentStatistics().updateIterationBounds(lowerBound, upperBound);
                //if (timeoutMs != Constants.infinity) {
                    if (k == 1) {
                    	System.out.println("time\tLB\tUB\tIterAgtMsgs\tnAgtMsgs\tNetLoad");
//                    	setJ(1);
                    }

                    if (k == 1 || (getAgentStatistics().getBounds(k-2)[0] != lowerBound
                            || getAgentStatistics().getBounds(k-2)[1] != upperBound)) {
                        System.out.println(getAgentStatistics().getStopWatch().getMilliTime() + "\t" +
                                lowerBound + "\t" + upperBound + "\t" +
                                (getAgentStatistics().getSentMessages() - prevMsgSent) + "\t" +
                                getAgentStatistics().getSentMessages() + "\tNA");
//                    	setJ(1);
                    }
                //}
            }
        }
    }

    @Override
    protected void onStop() {
    }

    /**
     * @return The view of this agent.
     */
    protected DLNSAgentView getAgentView() {
        return agentView;
    }

    /**
     * @return The actions executable by the agent
     */
    protected DLNSAgentActions getAgentActions() {
        return agentActions;
    }
    
	public int getCurrentLeastUB() {
		return currentLeastUB;
	}

	public void setCurrentLeastUB(int currentLeastUB) {
		this.currentLeastUB = currentLeastUB;
	}

//	public int getF_j() {
//		return f_j;
//	}
//
//	public void setF_j(int f_j) {
//		this.f_j = f_j;
//	}
//
//	public static int getJ() {
//		return j;
//	}
//
//	public static void setJ(int j) {
//		DLNSagent.j = j;
//	}

    protected void DLNScycle() {

        destroyPhase.start();
        while (!destroyPhase.isTerminated()) {
            await();
        }

        repairPhase.start();
        while (!repairPhase.isTerminated()) {
            await();
        }

        // Accepts even if it does violate hard constraints!
        getAgentActions().setVariableValue(getAgentView().varCheckValueK);
        // System.out.println(k + ": " + getName() + " setting value= " + getAgentView().varCheckValueK);

        // Update bounds
        if (getAgentView().getPseudoTreeStar().isRoot()) {
            if (DCOPinfo.isSAT) {
                if (Constraint.isSat(getAgentView().lowerBoundK))
                    lowerBound = Math.max(lowerBound, getAgentView().lowerBoundK);
                if (Constraint.isSat(getAgentView().upperBoundK)) {
                    upperBound = Math.min(upperBound, getAgentView().upperBoundK);
                    if (upperBound < currentLeastUB) {
                    	System.out.println("J UPDATED");
                        repairPhase.setJ_updated(true);
                    	currentLeastUB = upperBound;
                    }
                    else {
                        repairPhase.setJ_updated(false);
                    }
                }
                System.out.println("ITER " + k + " is SAT");
            } else {
                System.out.println("ITER " + k + " is UNSAT");
            }
        }
    }


    /**
     * Constructs a pseudoTree for all agents.
     */
    public class PseudoTreeBuilder {
        private boolean recvPTinfo = false;

        public void start() {
            recvPTinfo = false;
            if (isLeader()) { // If leader:
                Thread.currentThread().setPriority(Thread.MAX_PRIORITY);

                final int nbAgents = DCOPinfo.nbAgents;
                PseudoTree[] treeAgents = new PseudoTree[nbAgents];
                for (int i = 0; i < nbAgents; i++) {
                    treeAgents[i] = new PseudoTree();
                }
                buildPseudoTree(treeAgents);

                // Update pseudoTree
                getAgentView().pseudoTreeStar.update(treeAgents[(int) getId()]);
                for (ComAgent agt : DCOPinfo.agentsRef) {
                    if (agt.getId() != getId()) {
                        agt.tell(new PTStarInfoMessage(treeAgents[(int) agt.getId()]), getSelf());
                        //System.out.println("Tree_"+agt.getId() + treeAgents[(int)agt.getId()].toString());
                    }
                }
                Thread.currentThread().setPriority(Thread.NORM_PRIORITY);
                recvPTinfo = true;
            }
        }

        public boolean isTerminated() {
            return recvPTinfo;
        }

        protected void buildPseudoTree(PseudoTree[] treeAgents) {
            final int nbAgents = DCOPinfo.nbAgents;
            boolean[] discovered= new boolean[nbAgents];
            Arrays.fill(discovered, false);
            Stack<ComAgent> dfsQueue = new Stack<>();
            int nDiscovered = 0;

            ComAgent root = DCOPinfo.leaderAgent;
            int rootID = (int) root.getId();
            dfsQueue.push(root);
            treeAgents[rootID].setParent(null);

            while (!dfsQueue.empty()) {
                ComAgent agt = dfsQueue.pop();
                int agtIdx = (int) agt.getId();

                if (!discovered[agtIdx]) {
                    for (ComAgent chAgt : agt.getNeighborsRef()) {
                        int chIdx = (int) chAgt.getId();
                        if (chAgt.equals(treeAgents[agtIdx].getParent())) continue;
                        dfsQueue.push(chAgt);
                        // chAgt is a child of agt; and agt is parent of chAgt
                        if (!discovered[chIdx]) {
                            treeAgents[agtIdx].addChild(chAgt);
                            treeAgents[chIdx].setParent(agt);
                        } else {
                            // Set backedges:
                            treeAgents[agtIdx].addPseudoParent(chAgt);
                            treeAgents[chIdx].addPseudoChild(agt);
                            treeAgents[chIdx].removeChild(agt);
                        }
                    }//-neighbors
                    discovered[agtIdx] = true;
                    nDiscovered++;
                }//-discovered
            }//-Tree

            assert (nDiscovered == nbAgents);
        }
    }

    public static class PTStarInfoMessage  {
        private PseudoTree treeAgent;

        public PTStarInfoMessage(PseudoTree treeAgent){
            this.treeAgent = treeAgent;
        }

        public PseudoTree getTreeAgent() {
            return treeAgent;
        }

        @Override
        public String toString() {
            return "Repair::PTInfoMessage";
        }
    }

}
