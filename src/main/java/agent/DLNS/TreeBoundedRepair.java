package agent.DLNS;

import communication.ComAgent;
import communication.DCOPinfo;
import communication.PseudoTree;
import kernel.AgentView;
import kernel.Constants;
import kernel.Constraint;
import kernel.Tuple;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Collectors;

/**
 * Created by ffiorett on 8/2/15.
 * TODO: Tree not needed - just save parent within this class.
 * TODO: UTIL message not need to change - allocate it once.
 */
public class TreeBoundedRepair implements RepairPhase {
    private boolean terminated = false;
    private boolean recvPTinfo = false;
    private int recvLNInfoMsgs = 0;
    private int recvUtilMsgs   = 0;
    private int recvValueMsgs  = 0;
    private int recvContextMsgs= 0;
    private int recvBoundMsgs  = 0;
    private boolean LN[];

    private DLNSagent selfRef;  // simulate outer-class model
    // Support classes for The bounded repair framework
    private RelaxationPhase relaxation;
    private SolvingPhase solving;
    private BoundingPhase bounding;
    private ContextPhase  context;
    
    private boolean j_updated;
    private int currentIteration;

    public TreeBoundedRepair(DLNSagent selfRef) {
        this.selfRef = selfRef;
        this.LN = new boolean[DCOPinfo.nbAgents];
        this.relaxation = new RelaxationPhase();
        this.solving = new SolvingPhase();
        this.bounding = new BoundingPhase();
        this.context = new ContextPhase();
        
        this.setJ_updated(false);
    }

    @Override
    public void onReceive(Message message, ComAgent sender) {
        if (message instanceof LNInfoMessage) { // Only the leader can receive this type of message
            LNInfoMessage info = (LNInfoMessage)message;
            LN[((int) sender.getId())] = info.isDestroyed();
            recvLNInfoMsgs++;

            // TODO: Have a (pseudo)-terminate method
            if (recvLNInfoMsgs == (DCOPinfo.nbAgents - 1)) {
                recvPTinfo = true;
                recvLNInfoMsgs = 0;
            }
        } else if (message instanceof PTInfoMessage) {
            PTInfoMessage ptInfo = (PTInfoMessage) message;
            selfRef.getAgentView().pseudoTreeK.update(ptInfo.getTreeAgent());
            //System.out.println(selfRef.getName() + " recv PT: " + getPseduoTreeK().toString());
            recvPTinfo = true;
        } else if (message instanceof UtilMessage) {
            UtilMessage utilMessage = (UtilMessage) message;
            solving.chUtilTables.add(utilMessage.getTable());
            recvUtilMsgs++;
        } else if (message instanceof ValueMessage) {
            ValueMessage valueMessage = (ValueMessage) message;
            solving.recvParValueCheck = valueMessage.agtValueCheck;
            solving.recvParValueHat   = valueMessage.agtValueHat;
            recvValueMsgs++;
        } else if (message instanceof LNContextMessage) {
            LNContextMessage msg = (LNContextMessage) message;
            selfRef.getAgentView().valueNeighborCheck.put(sender.getId(), msg.getCheckValue());
            selfRef.getAgentView().valueNeighborHat.put(sender.getId(), msg.getHatValue());
            recvContextMsgs++;
        } else if (message instanceof BoundMessage) {
            BoundMessage msg = (BoundMessage) message;
            bounding.LB.set(Constraint.add(bounding.LB.get(), msg.getLB()));
            bounding.UB.set(Constraint.add(bounding.UB.get(), msg.getUB()));
            // System.out.println(selfRef.getName() + " recv msg: " + msg + " from " + sender);
            recvBoundMsgs++;
        }

    }

    @Override
    public void start() {
        ///System.out.println(selfRef.getName() + " started REPAIR phase");
        terminated = false;
        recvPTinfo = false;

        // Relaxation Phase
        relaxation.start(); // Returns PT_i^k. Takes in input LN_i^k.

        // UtilPropagation
        // Returns \hat{x}_i and \check{x}_i. Takes in input PT_i^k.
        if (selfRef.getAgentView().isVarDestroyed())
            solving.start();

        // Context Propagation
        context.start();

        // Bounds
        bounding.start();

        terminated = true;
    }

    public void initialize() {
        relaxation.initialize();
        bounding.initialize();
    }

    @Override
    public boolean isTerminated() {
        return terminated;
    }

    private PseudoTree getPseduoTreeK() {
        return selfRef.getAgentView().getPseudoTreeK();
    }

    private PseudoTree getPseduoTreeStar() {
        return selfRef.getAgentView().getPseudoTreeStar();
    }

    private int getCheckValueK() {
        return selfRef.getAgentView().varCheckValueK;
    }

    private int getHatValueK() {
        return selfRef.getAgentView().varHatValueK;
    }

    public boolean isJ_updated() {
		return j_updated;
	}

	public void setJ_updated(boolean j_updated) {
		this.j_updated = j_updated;
	}

	public int getCurrentIteration() {
        return currentIteration;
    }

	public void setCurrentIteration(int currentIteration) {
        this.currentIteration = currentIteration;
    }

    /**
     * The relaxation phase.
     * Constructs a pseudoForest using exclusively the variables in the current LN^k
     */
    public class RelaxationPhase {

        private final int nbAgents = DCOPinfo.nbAgents;
        private boolean[] discovered;
        private ComAgent[] dfsQueue;
        int dfsQueueSize;
        private PseudoTree[] treeAgents;
        private ParentChild parentChildSet[][]; // for each agent a set of parent child

        RelaxationPhase() {
            if (selfRef.getId() == 0) {
                discovered = new boolean[nbAgents];
                dfsQueue = new ComAgent[nbAgents*nbAgents];
                dfsQueueSize = 0;
                treeAgents = new PseudoTree[nbAgents];

                for (int i = 0; i < nbAgents; i++) {
                    treeAgents[i] = new PseudoTree();
                }

                parentChildSet = new ParentChild[nbAgents][];
            }
        }

        public void initialize() {
            if (selfRef.getId() == 0) {
                // initialize parent Child Set
                // Khoi: for each agent, add all neighbors to its parent child set as [agent][neighbors]
                for (ComAgent agt : DCOPinfo.agentsRef) {
                    int agtIdx = (int) agt.getId();
                    parentChildSet[agtIdx] = new ParentChild[agt.getNbNeighbors()];
                    for (int nId = 0; nId < agt.getNbNeighbors(); nId++) {
                        ComAgent nAgt = agt.getNeighborsRef().get(nId);
                        parentChildSet[agtIdx][nId] = new ParentChild(agt, nAgt);
                    }
                }
            }
        }

        public void start() {
              if (!selfRef.isLeader()) { // If not leader:
                // Send message to leader to inform about my var state.
                LNInfoMessage msg = new LNInfoMessage(selfRef.getAgentView().isVarDestroyed());
                selfRef.getLeaderRef().tell(msg, selfRef.getSelf());

                Thread.currentThread().setPriority(Thread.MIN_PRIORITY);
                while (!recvPTinfo) { // Wait to receive list of {Pi, Ci, PPi} from leader.
                    selfRef.await();
                }
                Thread.currentThread().setPriority(Thread.NORM_PRIORITY);

            } else {
                LN[((int) selfRef.getId())] = selfRef.getAgentView().isVarDestroyed();

                while (!recvPTinfo) { // Wait to receive all DestroyInfoMessage from all agents.
                    selfRef.await();
                }

                Thread.currentThread().setPriority(Thread.MAX_PRIORITY);
                buildPseudoTree(LN, currentIteration);
                // Update pseudoTree
                PseudoTree Tk = getTreeAgent((int) selfRef.getId());
                selfRef.getAgentView().pseudoTreeK.update(Tk);
                for (ComAgent agt : DCOPinfo.agentsRef) {
                    if (!agt.equals(selfRef)) {
                        Tk = getTreeAgent((int) agt.getId());
                        agt.tell(new PTInfoMessage(Tk), selfRef);
                        //System.out.println("Tree_" + agt.getId() + Tk.toString());
                    }
                }
                Thread.currentThread().setPriority(Thread.NORM_PRIORITY);
            }
        }

        /**
         * The pseudoTree of iteration k associated to agent agentID.
         * @param agentID The agent ID
         * @return The PseudoTree T^k_i of agent a_i at iteration k.
         */
        public PseudoTree getTreeAgent(int agentID) {
            return treeAgents[agentID];
        }

        /**
         * Class holding a parent child relation. It is used in the neighbor ordering,
         * when constructing a pseudo-tree.
         */
        class ParentChild {
            public ComAgent parent;
            public ComAgent child;
            ParentChild(ComAgent parent, ComAgent child) {
                this.parent = parent;
                this.child = child;
            }
        }

        ///////////////////////////////////////////////
        /**
         * Prepares the data structures for the next pseudo-tree construction.
         */
        private void clear() {
            for (PseudoTree treeAgent : treeAgents)
                treeAgent.clear();
            for (int i = 0; i < nbAgents; i++)
                discovered[i] = false;
            dfsQueueSize = 0;
        }

        /**
         * Comparator which prefer agents with fewer neighbors.
         * Using this comparator, such agents will be located on the upper part of
         * the pseudo-tree.
         */
        class MinTreeWidthComparator implements Comparator<ComAgent> {
            @Override
            public int compare(ComAgent a, ComAgent b) {
                return a.getNbNeighbors() < b.getNbNeighbors() ? -1 // precendece to a
                        : a.getNbNeighbors() == b.getNbNeighbors() ? 0
                        : 1; // precedence to b
            }
        }

        /**
         * Comparator which prefers edges that have not been optimized yet.
         */
        class ParentChildComparator implements Comparator<ParentChild> {
            @Override
            public int compare(ParentChild a, ParentChild b) {
                int ax = (int) a.parent.getId();
                int ay = (int) a.child.getId();
                int bx = (int) b.parent.getId();
                int by = (int) b.child.getId();
                // (edge parent-child 'a' not optimized) while (edge parent-child 'b' optimized)
                return (!DCOPinfo.Theta[ax][ay] && DCOPinfo.Theta[bx][by]) ? -1 // prefers 'a'
                        // (edge parent-child 'a' optimized) while (edge parent-child 'b' not optimized)
                        : (DCOPinfo.Theta[ax][ay] && !DCOPinfo.Theta[bx][by]) ? 1 // prefers 'b'
                        : tieBreak(a.child, b.child); // Tie break
            }

            private int tieBreak(ComAgent a, ComAgent b) {
                return a.getNbNeighbors() < b.getNbNeighbors() ? -1 // precendece to a
                        : a.getNbNeighbors() == b.getNbNeighbors() ? 0
                        : 1; // precedence to b
            }
        }

        protected void buildPseudoTree(boolean[] LN, int iteration) {
            clear();

            while (true) {  // Forest exploration
                ComAgent root = DCOPinfo.leaderAgent;
                int rootID = (int) root.getId();
                while (rootID < nbAgents && (discovered[rootID] || !LN[rootID])) {
                    rootID++;
                }
                if (rootID >= nbAgents) break; // All agents in LN^k have been explored

                root = DCOPinfo.agentsRef[rootID];
                dfsQueue[dfsQueueSize++] = root;
                treeAgents[rootID].setParent(null);

                while (dfsQueueSize > 0) {
                    ComAgent agt =  dfsQueue[--dfsQueueSize];
                    int agtIdx = (int) agt.getId();
                    
                    // Khoi: if the first iteration, store the edges to be avoided
                    // For edges (vertexID1, vertexID2)
                    // Build a hashMap(agent) -> neighbors not for building edges
                    if (!discovered[agtIdx]) {
                        // Prefers edges which have not been explored yet
                        ParentChild[] neighbors = parentChildSet[agtIdx];
                        Arrays.sort(neighbors, new ParentChildComparator());

//                        Collections.sort(agt.getNeighborsRef(), new MinTreeWidthComparator());
//                        for (ComAgent chAgt : agt.getNeighborsRef()) {
                        for (ParentChild pc : neighbors) {
                            // Khoi:
                            // If the first iteration and pc in neighbor not for building edges
                            // Continue
                            
                            ComAgent chAgt = pc.child;
                            int chIdx = (int) chAgt.getId();

                            // Skip node if it is not in current LN (frozen)
                            if (!LN[chIdx]) continue;
                            if (chAgt.equals(treeAgents[agtIdx].getParent())) continue;

                            dfsQueue[dfsQueueSize++] = chAgt;

                            // chAgt is a child of agt; and agt is parent of chAgt
                            if (!discovered[chIdx]) {
                                treeAgents[agtIdx].addChild(chAgt);
                                treeAgents[chIdx].setParent(agt);
                            } else {
                                // Set backedges:
                                treeAgents[agtIdx].addPseudoParent(chAgt); // TODO: not needed
                                // treeAgents[chIdx].pseudoChildren.add(agt);
                                treeAgents[chIdx].removeChild(agt);
                            }
                        }//-neighbors
                        discovered[agtIdx] = true;
                    }//-discovered

                }//-Tree

//                int ptHeithg = 0;// Compute PT height
//                PseudoTree aj = treeAgents[rootID];
//                while (!aj.getChildren().isEmpty()) {
//                    int j = (int)aj.getChildren().get(0).getId();
//                    aj = treeAgents[j];
//                    ptHeithg++;
//                }
//                System.out.println("Tree Height: " + ptHeithg);
            }//-Forest

        }

    }

    /**
     * The Utility propagation phase.
     * It is executed exclusively for the destroyed agents. It proceeds as DPOP in the UTIL and
     * VALUE phases, solving the two relaxed problems, \check{P} and \hat{P}.
     * Finally, the agents propagate their values to all their neighbors (destroyed and not).
     */
    public class SolvingPhase {
        protected boolean terminated;
        protected List<UtilTable> chUtilTables;
        UtilTable table = null;
        int recvParValueCheck;
        int recvParValueHat;

        public SolvingPhase() {
            this.terminated = false;
            this.chUtilTables = new ArrayList<>();
            this.table = new UtilTable();
        }

        public void start() {
            terminated = false;

            // --------------------
            // UTIL Phase
            // --------------------
            while (recvUtilMsgs < getPseduoTreeK().getChildren().size()) {
                selfRef.await();
            }

            Thread.currentThread().setPriority(Thread.MAX_PRIORITY);
            table.init(getPseduoTreeK().getParent());
            if (getPseduoTreeK().isRoot()) {
                // Root also checks if current solution is sat.
                selfRef.getAgentView().setVarValuesK(table.getBestValue());
                //System.out.println(selfRef.getName() + " (Root agt) chooses values: " + selfRef.getAgentView().varCheckValueK + " " + selfRef.getAgentView().varHatValueK);
            } else {
                table.generate();
                getPseduoTreeK().getParent().tell(new UtilMessage(table), selfRef);
            }
            Thread.currentThread().setPriority(Thread.NORM_PRIORITY);

            // --------------------
            // Value Phase
            // --------------------
            if (!getPseduoTreeK().isRoot()) {
                while (recvValueMsgs == 0) {
                    selfRef.await();
                }
                int[] values = table.getBestValue(recvParValueCheck, recvParValueHat);
                selfRef.getAgentView().setVarValuesK(values);
            }

            // For each children create Value Messages and send it.
            for (UtilTable chUtilTable : chUtilTables) {
                chUtilTable.owner.tell(new ValueMessage(getCheckValueK(), getHatValueK()), selfRef);
            }

            // Send Context Message to each preserved neighbor:
            sendContext(getCheckValueK(), getHatValueK());

            terminate();
        }

        // TODO: check if it is faster to create the object as "new" at every iteration without clearing it
        public void terminate() {
            recvUtilMsgs = 0;
            recvValueMsgs = 0;
            chUtilTables.clear();
            table.clear();
            terminated = true;
        }

        /**
         * Send Context Message to each preserved neighbor.
         */
        private void sendContext(int checkVarValueK, int hatVarValueK) {
            for (ComAgent agt : selfRef.getNeighborsRef())
                agt.tell(new LNContextMessage(checkVarValueK, hatVarValueK), selfRef);
        }

        public class UtilTable {
            public ComAgent owner;
            public ComAgent parent;
            public int[][] table;
            public int[][] bestSelfValues;
            Tuple tupleTree;             // TODO: TupleTree need to be of size=2.
            Tuple tupleFrozen;
            // TODO: Here we assume all domains are the same.
            int dMin;
            int dMax;
            int dSize;

            public UtilTable() {
                owner = selfRef;
                parent = null;
                dMin = selfRef.getAgentView().getDomainMin();
                dMax = selfRef.getAgentView().getDomainMax();
                dSize = dMax - dMin + 1;
                bestSelfValues = new int[2][dSize];
                table = new int[2][dSize];
                tupleTree = new Tuple(2);
            }

            public void init(ComAgent parent) {
                this.parent = parent; // could be null;
                // Retrieve neighbors with retained (frozen) variables.
                List<Long> frozenNeighbors = new ArrayList<>();
                DLNSAgentView view = selfRef.getAgentView();
                for (ComAgent neighbor : selfRef.getNeighborsRef()) {
                    if (!view.destroyedNeighbor.get(neighbor.getId())) {
                        frozenNeighbors.add(neighbor.getId());
                    }
                }

                // Construct the tuples to be evaluated:
                // TupleTree   : [children, self]
                // TupleFozen  : [self, frozen_neighbors]
                tupleFrozen = new Tuple(1 +  frozenNeighbors.size());
                for (int i = 0; i < frozenNeighbors.size(); i++) {
                    long nId = frozenNeighbors.get(i);
                    tupleFrozen.set(1 + i, view.valueNeighborCheck.get(nId));
                }

                // Construct the constraint evaluator Retrieve constraints involved
                List<Long> treeAgtsID = new ArrayList<>();
                if(!getPseduoTreeK().isRoot()) {
                    treeAgtsID.add(parent.getId());
                    treeAgtsID.add(selfRef.getId());
                    // LB constraint evaluator analyzes constraints with xi and Pi
                    selfRef.getAgentView().pCheckEvaluatorK.initialize(treeAgtsID);
                }
                // UB  constraint evaluator analyzes constraints with xi and xj in N(ai) not in LN_k
                List<Long> frozenAgtsID = new ArrayList<>();
                frozenAgtsID.add(selfRef.getId());
                frozenAgtsID.addAll(frozenNeighbors);
                selfRef.getAgentView().pHatEvaluatorK.initialize(frozenAgtsID);

            }

            public void generate() {
                // pTree is only a sub-part of the problem to evaluate, to evaluate it compleatly
                // it need to be added to pHat
                AgentView.Evaluator pTree = selfRef.getAgentView().pCheckEvaluatorK;
                AgentView.Evaluator pFrozen = selfRef.getAgentView().pHatEvaluatorK;
                boolean hasFrozenNeighbors = (tupleFrozen.size() > 1);

                Arrays.fill(bestSelfValues[0], 0 /*Constants.NaN*/);
                Arrays.fill(bestSelfValues[1], 0 /*Constants.NaN*/);

                for (int vPar = dMin; vPar <= dMax; vPar++) {
                    tupleTree.set(0, vPar);

                    int bestUtilCheck = Constants.worstValue();
                    int bestUtilHat   = Constants.worstValue();
                    int utilCheck; int utilHat;

                    for (int vSelf = dMin; vSelf <= dMax; vSelf++) {
                       tupleTree.set(1, vSelf);
                        if (hasFrozenNeighbors) tupleFrozen.set(0, vSelf);

                        utilCheck = utilHat = pTree.evaluate(tupleTree, j_updated);

                        // Add children cost:
                        for (UtilTable chTable : chUtilTables) {
                            utilCheck = Constraint.add(utilCheck, chTable.table[0][vSelf - dMin]);
                            utilHat   = Constraint.add(utilHat, chTable.table[1][vSelf - dMin]);
                        }
                        if (hasFrozenNeighbors) {
                            utilCheck = Constraint.add(utilCheck, pFrozen.evaluate(tupleFrozen, j_updated));
                        }
                        // todo: check! utilCheck has to be Sat so for Hat to make sense?
                        // todo: Yes because Hat is based on Check.
                        if (Constraint.isUnsat(utilCheck)) continue;

                        // Save best values for this agent
                        if (Constraint.isSat(utilCheck) && utilCheck > bestUtilCheck) {
                            bestUtilCheck = utilCheck;
                            bestSelfValues[0][vPar - dMin] = vSelf;
                        }
                        if (Constraint.isSat(utilHat) && utilHat > bestUtilHat) {
                            bestUtilHat = utilHat;
                            bestSelfValues[1][vPar - dMin] = vSelf;
                        }
                    }
                    // Store projected values into table
                    if (Constraint.isSat(bestUtilCheck) || Constraint.isSat(bestUtilHat)) {
                        table[0][vPar - dMin] = bestUtilCheck;
                        table[1][vPar - dMin] = bestUtilHat;
                    }
                }
            }

            /**
             * This method is used by the root agent only.
             * @return A pair of values [check, hat] if the constraint was sat, or [NaN, NaN] otherwise.
             */
            public int[] getBestValue() {
                Tuple chTuple = new Tuple(1);
                AgentView.Evaluator pFrozen = selfRef.getAgentView().pHatEvaluatorK;
                boolean hasFrozenNeighbors = (tupleFrozen.size() > 1);

                // Performs Projection of self
                int bestUtilCheck = Constants.worstValue();
                int bestUtilHat   = Constants.worstValue();
                int bestValueCheck = 0;//Constants.NaN;
                int bestValueHat   = 0;//Constants.NaN;

                for (int vSelf = dMin; vSelf <= dMax; vSelf++) {
                    int utilCheck = 0;
                    int utilHat = 0;

                    chTuple.set(0, vSelf);
                    if (hasFrozenNeighbors) tupleFrozen.set(0, vSelf);

                    // Add children cost:
                    for (UtilTable chTable : chUtilTables) {
                        utilCheck = Constraint.add(utilCheck, chTable.table[0][vSelf - dMin]);
                        utilHat   = Constraint.add(utilHat, chTable.table[1][vSelf - dMin]);
                    }
                    if (hasFrozenNeighbors) {
                        utilCheck = Constraint.add(utilCheck, pFrozen.evaluate(tupleFrozen, j_updated));
                    }
                    if (Constraint.isUnsat(utilCheck)) continue;

                    if (Constraint.isSat(utilCheck) && utilCheck > bestUtilCheck) {
                        bestUtilCheck = utilCheck;
                        bestValueCheck = vSelf;
                    }
                    if (Constraint.isSat(utilHat) && utilHat > bestUtilHat) {
                        bestUtilHat = utilHat;
                        bestValueHat = vSelf;
                    }
                }

                //System.out.println(" Total Util = " + bestUtilCheck + ", " + bestUtilHat);
                return new int[]{bestValueCheck, bestValueHat};
            }

            /**
             *
             * @param vParCheck The best value selected by the parent for the problem \check{P}
             * @param vParHat   The best value selected by the parent for the problem \hat{P}
             * @return the best values for this agent for the problems check and hat P
             */
            public int[] getBestValue(int vParCheck, int vParHat) {
                int res[] = new int[2];
                res[0] = (Constraint.isSat(vParCheck)) ? bestSelfValues[0][vParCheck - dMin] : Constants.NaN;
                res[1] = (Constraint.isSat(vParHat)) ? bestSelfValues[1][vParHat - dMin] : Constants.NaN;
                return res;
            }


            void clear() {
                parent = null;
                // NEEDED ???
//                Arrays.fill(table[1], Constants.infinity);
//                Arrays.fill(table[0], Constants.infinity);
//                Arrays.fill(bestSelfValues[0], Constants.NaN);
//                Arrays.fill(bestSelfValues[1], Constants.NaN);
                // -----------
                tupleFrozen = null;
            }

            @Override
            public String toString() {
                String res = "Parent = " + parent.getName() + "\n";
                for( int v = dMin; v <= dMax; v++) {
                    res += "<" + v + "> : " + table[0][v-dMin] + ", "  + table[1][v-dMin]
                            + "  (" + bestSelfValues[0][v-dMin] + ", " + bestSelfValues[1][v-dMin] + ")\n";
                }
                return res;
            }
        }
    }

    /**
     * The context propagation phase.
     * It is executed by all agents. Each agent will wait to receive the new updated context,
     * build by the repair algorithm. The agents do not wait for messages from those neighbors which are
     * frozen.
     */
    public class ContextPhase {
        boolean terminated;

        /**
         * Only retained variable agents execute this part.
         * Wait for all the destoyed neighbors to send their updated information.
         */
        public void start() {
            terminated = false;

            // Count the number of messages that it is expected to receive:
            long nbDestroyedNeighbors =
                    selfRef.getAgentView().destroyedNeighbor.values().stream().filter(p -> p == true).count();

            while (recvContextMsgs < nbDestroyedNeighbors) {
                selfRef.await();
            }
            terminate();
        }

        private void terminate() {
            terminated = true;
            recvContextMsgs = 0;
        }
    }


    /**
     * Note: This class could be brought outside directly in DLNSagent
     * Oct-9-2015: To update the UB as the new proof requires, we first need the cost of the solution (hat UB) involving
     * exclusively the nodes in the LN_k (join the sum of all roots in the forest to the root?
     * ----------------
     * Also, we need to know the number of edges N_k optimized during this process.
     * Thus, the root can divide the UB_k by N_k. This will be the cost of the individual edges at iteration k.
     */
    public class BoundingPhase {
//        private boolean terminated;
        protected AgentView.Evaluator pCheckEvaluator;
        protected DLNSAgentView.UpperBoundTreeEvaluator pHatEvaluator;
        Tuple tupleCheck;
        Tuple tupleHatK;
        // The list of High Priority Context Neighbors: Pi, PPi (self)
        List<Long> HPNeighborContext;

        protected AtomicInteger LB;
        protected AtomicInteger UB;
        
        protected boolean j_updated;

        public BoundingPhase() {
            this.LB = new AtomicInteger(0);
            this.UB = new AtomicInteger(0);
//            this.terminated = false;
            pCheckEvaluator = selfRef.getAgentView().pCheckEvaluatorStar;
            pHatEvaluator = selfRef.getAgentView().pHatTreeEvaluatorStar;
        }
        
        public BoundingPhase(boolean j_updated) {
        	this();
        	this.j_updated = j_updated;
        }

        public void initialize() {
            int nTuple = getPseduoTreeStar().getPseudoParents().size() + 2;
            tupleCheck = new Tuple(nTuple);
            tupleHatK = new Tuple(nTuple);
            HPNeighborContext = new ArrayList<>();
            // Add parent
            if(!getPseduoTreeStar().isRoot()) {
                HPNeighborContext.add(getPseduoTreeStar().getParent().getId());
                // Add pseudo-parents
                HPNeighborContext.addAll(getPseduoTreeStar().getPseudoParents().stream().map(
                        ComAgent -> ComAgent.getId()).collect(Collectors.toList()));
            }
            // Init evaluator for check, including self
            List<Long> tmp = new ArrayList<>(HPNeighborContext);
            tmp.add(selfRef.getId());
            // System.out.println(selfRef.getName() + " Bounding HEADER: " + tmp);
            pCheckEvaluator.initialize(tmp);
            pHatEvaluator.initialize(tmp);
        }

        public void start() {
            terminated = false;

            selfRef.getAgentStatistics().getStopWatch().suspend();
            if (selfRef.getAgentView().currentIteration % DCOPinfo.nbAgents == 0) {
                pHatEvaluator.resetRelaxedConstraints();
                if (selfRef.isLeader()) {
                    for (int i = 0; i < DCOPinfo.Theta.length; i++)
                        Arrays.fill(DCOPinfo.Theta[i], false);
                }
            }
            selfRef.getAgentStatistics().getStopWatch().resume();

            while (recvBoundMsgs < getPseduoTreeStar().getChildren().size()) {
                selfRef.await();
            }

            // todo: these operations could be avoided if the problem happen to be unsat.
            if (!getPseduoTreeStar().isRoot()) {
                int n = HPNeighborContext.size();
                // Get current HPneighbors context and evaluate P-check constraints
                for (int i = 0; i < n; i++) {
                    tupleCheck.set(i, selfRef.getAgentView().valueNeighborCheck.get(HPNeighborContext.get(i)));
                    tupleHatK.set(i, selfRef.getAgentView().valueNeighborHat.get(HPNeighborContext.get(i)));
                }
                tupleCheck.set(n, selfRef.getAgentView().varCheckValueK);
                tupleHatK.set(n, selfRef.getAgentView().varHatValueK);

                //System.out.println(selfRef.getName() + " tuple hat: " + tupleHatK.toString() + " util: " + pHatEvaluator.evaluate(tupleHatK));

                LB.set(Constraint.add(LB.get(), pCheckEvaluator.evaluate(tupleCheck, j_updated))); //set as false for LB
                UB.set(Constraint.add(UB.get(), pHatEvaluator.evaluate(tupleHatK, j_updated)));

                // Send message to parent
                getPseduoTreeStar().getParent().tell(new BoundMessage(LB.get(), UB.get()), selfRef);
            }
            selfRef.getAgentView().lowerBoundK = LB.get();
            selfRef.getAgentView().upperBoundK = UB.get();
            //System.out.println(selfRef.getName() + " LB: " + LB.get() + " UB: " + UB.get());

            if (getPseduoTreeStar().isRoot()) {
                DCOPinfo.isSAT = Constraint.isSat(LB.get()) && Constraint.isSat(UB.get());
            }
            terminate();
        }

        private void terminate() {
            recvBoundMsgs = 0;
            LB.set(0);
            UB.set(0);
            terminated = true;
        }
    }

    /////////////////////////////////////////////////////////////////////////
    // Messages
    /////////////////////////////////////////////////////////////////////////
    public static class LNInfoMessage extends Message {
        /**
		 * 
		 */
		private static final long serialVersionUID = -1534254843982943269L;
		private final boolean destroyed;

        public LNInfoMessage(boolean destroyed) {
            super.setTrackable(false);
            this.destroyed = destroyed;
        }

        public boolean isDestroyed() {
            return destroyed;
        }

        @Override
        public String toString() {
            return "Rapair::LNInfoMessage";
        }
    }

    public static class PTInfoMessage extends Message {
        /**
		 * 
		 */
		private static final long serialVersionUID = -2568067695312169746L;
		private PseudoTree treeAgent;

        public PTInfoMessage(PseudoTree treeAgent){
            super.setTrackable(false);
            this.treeAgent = treeAgent;
        }

        public PseudoTree getTreeAgent() {
            return treeAgent;
        }

        public void setTreeAgent(PseudoTree treeAgent) {
            this.treeAgent = treeAgent;
        }

        @Override
        public String toString() {
            return "Repair::PTInfoMessage";
        }
    }

    public static class UtilMessage extends Message {
        /**
		 * 
		 */
		private static final long serialVersionUID = -775023823979424003L;
		private SolvingPhase.UtilTable table;

        public UtilMessage(SolvingPhase.UtilTable table) {
            this.table = table;
        }

        public SolvingPhase.UtilTable getTable() {
            return table;
        }

        @Override
        public String toString() {
            return "Repair::UtilMessage";
        }
    }

    public static class ValueMessage extends Message {
        /**
		 * 
		 */
		private static final long serialVersionUID = 3637777131843483224L;
		public int agtValueCheck;
        public int agtValueHat;

        public ValueMessage(int agtValueCheck, int agtValueHat) {
            this.agtValueCheck = agtValueCheck;
            this.agtValueHat = agtValueHat;
        }


        @Override
        public String toString() {
            return "Repair::ValueMessage";
        }

    }

    public static class LNContextMessage extends  Message {
        /**
		 * 
		 */
		private static final long serialVersionUID = -2417681406858090375L;
		private final int checkValueK;
        private final int hatValueK;

        public LNContextMessage(int checkValueK, int hatValueK) {
            this.checkValueK = checkValueK;
            this.hatValueK = hatValueK;
        }

        public int getCheckValue() {
            return checkValueK;
        }

        public int getHatValue() {
            return hatValueK;
        }

        @Override
        public String toString() {
            return "LNContextMessage{" +
                    "checkValueK=" + checkValueK +
                    ", hatValueK=" + hatValueK +
                    '}';
        }
    }

    public static class BoundMessage extends Message {
        /**
		 * 
		 */
		private static final long serialVersionUID = -4711330241061852605L;
		private final int LB;
        private final int UB;

        public BoundMessage(int LB, int UB) {
            this.LB = LB;
            this.UB = UB;
        }

        public int getLB() {
            return LB;
        }

        public int getUB() {
            return UB;
        }

        @Override
        public String toString() {
            return "BoundMessage{" +
                    "LB=" + LB +
                    ", UB=" + UB +
                    '}';
        }
    }
}
