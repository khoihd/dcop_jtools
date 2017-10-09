package agent.DLNS;

import communication.ComAgent;
import communication.DCOPinfo;
import communication.PseudoTree;
import kernel.*;

import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * Created by ffiorett on 8/2/15.
 */
public class BoundedRepairDPOP implements RepairPhase {
    private boolean terminated = false;
    private boolean recvPTinfo = false;
    private int recvLNInfoMsgs = 0;
    private int recvUtilMsgs   = 0;
    private int recvValueMsgs  = 0;
    private int recvContextMsgs= 0;
    private int recvBoundMsgs  = 0;
    private boolean LN[];
//    private boolean isCurrIterSat = true;

    private DLNSagent selfRef;  // simulate outer-class model
    // Support classes for The bounded repair framework
    private RelaxationPhase relaxation;
    private SolvingPhase solving;
    private BoundingPhase bounding;
    private ContextPhase  context;
    
    private boolean j_updated;
    private int currentIteration;

    public BoundedRepairDPOP(DLNSagent selfRef) {
        this.selfRef = selfRef;
        this.LN = new boolean[DCOPinfo.nbAgents];
        this.relaxation = new RelaxationPhase();
        this.solving = new SolvingPhase();
        this.bounding = new BoundingPhase();
        this.context = new ContextPhase();
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
        } else if (message instanceof  PTInfoMessage) {
            PTInfoMessage ptInfo = (PTInfoMessage) message;
            selfRef.getAgentView().pseudoTreeK.update(ptInfo.getTreeAgent());
            //System.out.println(selfRef.getName() + " PT: " + ptInfo.getTreeAgent().toString());
            recvPTinfo = true;
        } else if (message instanceof UtilMessage) {
            UtilMessage utilMessage = (UtilMessage) message;
            solving.chUtilTables.add(utilMessage.getTable());
            recvUtilMsgs++;
        } else if (message instanceof ValueMessage) {
            ValueMessage valueMessage = (ValueMessage) message;
            solving.recvValues = valueMessage.agtValues;
            recvValueMsgs++;
        } else if (message instanceof LNContextMessage) {
            LNContextMessage msg = (LNContextMessage) message;
            selfRef.getAgentView().valueNeighborCheck.put(sender.getId(), msg.getCheckValue());
            selfRef.getAgentView().valueNeighborHat.put(sender.getId(), msg.getHatValue());
            // System.out.println(selfRef.getName() + " recv msg: " + msg + " from " + sender);
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
//        isCurrIterSat = true;
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
            ///System.out.println(selfRef.getName() + " started RELAXATION "
            /// + "\t["+ selfRef.getAgentView().currentIteration+"]");

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
                buildPseudoTree(LN);
                // Update pseudoTree
                PseudoTree Tk = getTreeAgent((int) selfRef.getId());
                selfRef.getAgentView().pseudoTreeK.update(Tk);
                for (ComAgent agt : DCOPinfo.agentsRef) {
                    if (!agt.equals(selfRef)) {
                        Tk = getTreeAgent((int) agt.getId());
                        agt.tell(new PTInfoMessage(Tk), selfRef);
                    }
                }
                // System.out.println(selfRef.getName() + " " + selfRef.getAgentView().pseudoTreeK.toString());
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

        protected void buildPseudoTree(boolean[] LN) {
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

                    if (!discovered[agtIdx]) {

                        // Prefers edges which have not been explored yet
                        ParentChild[] neighbors = parentChildSet[agtIdx];
                        Arrays.sort(neighbors, new ParentChildComparator());

//                        Collections.sort(agt.getNeighborsRef(), new MinTreeWidthComparator());
//                        for (ComAgent chAgt : agt.getNeighborsRef()) {
                        for (ParentChild pc : neighbors) {
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
                                treeAgents[agtIdx].addPseudoParent(chAgt);
                                // treeAgents[chIdx].pseudoChildren.add(agt);
                                treeAgents[chIdx].removeChild(agt);
                            }
                        }//-neighbors
                        discovered[agtIdx] = true;
                    }//-discovered

                }//-Tree
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
        HashMap<Long,Integer[]> recvValues;

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
            ///System.out.println(selfRef.getName() + " UTIL Propagation started "
            ///        + "\t["+ selfRef.getAgentView().currentIteration+"]");

            while (recvUtilMsgs < getPseduoTreeK().getChildren().size()) {
                selfRef.await();
            }

            Thread.currentThread().setPriority(Thread.MAX_PRIORITY);
            table.init(getPseduoTreeK().getParent(), getPseduoTreeK().getPseudoParents(), chUtilTables);
            if (getPseduoTreeK().isRoot()) {
                // The \check and \hat values are saved locally to this class (and not copied in
                // the agent state), thus do not replace the prev one, as we do not know if this
                // assignment will be sat or not!
                int[] values = table.getBestValue();
                selfRef.getAgentView().setVarValuesK(values);
            } else {
                // Build l-dimensional Table involving parent and pseudo-parents:
                table.generate();
                // System.out.println(selfRef.getName() + "Table:\n" + table.toString());
                getPseduoTreeK().getParent().tell(new UtilMessage(table), selfRef);
            }
            Thread.currentThread().setPriority(Thread.NORM_PRIORITY);

            // --------------------
            // Value Phase
            // --------------------
            /// System.out.println(selfRef.getName() + " VALUE Propagation started "
            ///        + "\t["+ selfRef.getAgentView().currentIteration+"]");


            if (!getPseduoTreeK().isRoot()) {
                // Wait to receive value message from parent
                while (recvValueMsgs == 0) {
                    selfRef.await();
                }

                //Thread.currentThread().setPriority(Thread.MAX_PRIORITY);
                // Retrieve value:
                Tuple tupleCheck = new Tuple(table.getHeader().size() + 1);
                Tuple tupleHat = new Tuple(table.getHeader().size() + 1);
                for (long sepAgtId : table.getHeader()) {
                    int idxSepAgt = table.getHeader().indexOf(sepAgtId);
                    tupleCheck.set(idxSepAgt, recvValues.get(sepAgtId)[0]);
                    tupleHat.set(idxSepAgt, recvValues.get(sepAgtId)[1]);
                }

                int[] values = table.getBestValue(tupleCheck, tupleHat);
                selfRef.getAgentView().setVarValuesK(values);
            }
            // System.out.print( selfRef.getName() + " extracted value: " + getCheckValueK() + "," + getHatValueK()+ "\n");

            // For each children create Value Messages and send it.
            for (UtilTable chUtilTable : chUtilTables) {
                HashMap<Long, Integer[]> chValues = new HashMap<>();
                // These are the agents we need to insert in the message.
                for (long agtId : chUtilTable.header) {
                    if (agtId == selfRef.getId())
                        chValues.put(agtId, new Integer[]{getCheckValueK(), getHatValueK()});
                    else
                        chValues.put(agtId, recvValues.get(agtId));
                }
                chUtilTable.owner.tell(new ValueMessage(chValues), selfRef);
            }
            //Thread.currentThread().setPriority(Thread.NORM_PRIORITY);

            // Send Context Message to each preserved neighbor:
            sendContext(getCheckValueK(), getHatValueK());

            terminate();
        }

        // TODO: check if it is faster to create the object as "new" at every iteration
        //       without clearing it
        // TODO: not consider the clearing time
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
            public List<Long> header;   // TODO: Substituite ComAgent with ID!
            public HashMap<Tuple, Integer[]> table;
            private Permutations perm;
            private List<HashMap<Long, Integer>> chAgtHeaderMap;
            private List<Tuple> chTuples;
            Tuple tupleTree;
            Tuple tupleFrozen;

            public UtilTable() {
                owner = selfRef;
                header = new ArrayList<>();
                table = new HashMap<>();
                perm = new Permutations();
                chAgtHeaderMap = new ArrayList<>();
                chTuples = new ArrayList<>();
            }

            public void init(ComAgent parent, List<ComAgent> pseudoParents, List<UtilTable> chUtilTables) {
                // Construct Table header (contains all agents in sep(a_i)
                if (parent != null) header.add(parent.getId());
                header.addAll(pseudoParents.stream().map(
                        ComAgent -> ComAgent.getId()).collect(Collectors.toList()));
                for (UtilTable chTable : chUtilTables) {
                    for (Long agtId : chTable.header) {
                        if (!header.contains(agtId) && agtId != selfRef.getId()) {
                            header.add(agtId);
                        }
                    }
                }
                int n = header.size();

                // Construct permutations for the Util Table
                int dMin = selfRef.getAgentView().getDomainMin();
                int dMax = selfRef.getAgentView().getDomainMax();
                int[] range = IntStream.rangeClosed(dMin, dMax).toArray();
                perm.init(range, n);

                // Retrieve neighbors with retained (frozen) variables.
                List<Long> frozenNeighbors = new ArrayList<>();
                DLNSAgentView view = selfRef.getAgentView();
                for (ComAgent neighbor : selfRef.getNeighborsRef()) {
                    if (!view.destroyedNeighbor.get(neighbor.getId())) {
                        frozenNeighbors.add(neighbor.getId());
                    }
                }

                // Construct the tuples to be evaluated:
                // TupleCheck: [children, self]
                // TupleHat  : [self, frozen_neighbors]
                tupleTree = new Tuple(n + 1);
                tupleFrozen = new Tuple(1 +  frozenNeighbors.size());
                for (int i = 0; i < frozenNeighbors.size(); i++) {
                    long nId = frozenNeighbors.get(i);
                    tupleFrozen.set(1 + i, view.valueNeighborCheck.get(nId));
                }

                // Construct the constraint evaluator Retrieve constraints involved
                List<Long> treeAgtsID = new ArrayList<>(header);
                treeAgtsID.add(selfRef.getId());
                // LB constraint evaluator analyzes constraints with xi and xj in sep(ai)
                selfRef.getAgentView().pCheckEvaluatorK.initialize(treeAgtsID);
                // UB  constraint evaluator analyzes constraints with xi and xj in N(ai) not in LN_k
                List<Long> frozenAgtsID = new ArrayList<>();
                frozenAgtsID.add(selfRef.getId());
                frozenAgtsID.addAll(frozenNeighbors);
                selfRef.getAgentView().pHatEvaluatorK.initialize(frozenAgtsID);

                //- Aux Data structure for Children retrival.
                if (chUtilTables.size() > 0) {
                    for (UtilTable chTable : chUtilTables) {
                        // Create MAP[id of a \in sep(Ci)] -> index of var in Header of Table_{ai}
                        HashMap<Long, Integer> map = new HashMap<>();
                        for (int chHeadIdx = 0; chHeadIdx < chTable.header.size(); chHeadIdx++) {
                            long aSepChId = chTable.header.get(chHeadIdx);
                            int idx = treeAgtsID.indexOf(aSepChId);
                            map.put(aSepChId, idx);
                        }
                        chAgtHeaderMap.add(map);
                        chTuples.add(new Tuple(chTable.header.size()));
                    }
                }
            }

            public void generate() {
                int n = header.size();
                int dMin = selfRef.getAgentView().getDomainMin();
                int dMax = selfRef.getAgentView().getDomainMax();

                // pTree is only a sub-part of the problem to evaluate, to evaluate it compleatly
                // it need to be added to pHat
                AgentView.Evaluator pTree = selfRef.getAgentView().pCheckEvaluatorK;
                AgentView.Evaluator pFrozen = selfRef.getAgentView().pHatEvaluatorK;
                boolean hasFrozenNeighbors = (tupleFrozen.size() > 1);

                // TODO: This is ok, but if you want speed up use a branch and bound search here.
                while (perm.hasNext()) {
                    tupleTree.copy(perm.getPermutation(), 0, n);

                    int bestUtilCheck = Constants.worstValue();
                    int bestUtilHat   = Constants.worstValue();
                    int utilCheck; int utilHat;

                    // Performs Projection of self
                    for (int vSelf = dMin; vSelf <= dMax; vSelf++) {
                        tupleTree.set(n, vSelf);
                        if (hasFrozenNeighbors) tupleFrozen.set(0, vSelf);

                        utilCheck = utilHat = pTree.evaluate(tupleTree, false);
                        if (Constraint.isUnsat(utilCheck)) continue;

                        // children cost ...
                        for (int chIdx = 0; chIdx < chUtilTables.size(); chIdx++) {
                            UtilTable chTable = chUtilTables.get(chIdx);

                            Tuple chTuple = chTuples.get(chIdx);
                            HashMap<Long, Integer> chMap = chAgtHeaderMap.get(chIdx);

                            for (int chHeadIdx = 0; chHeadIdx < chTable.header.size(); chHeadIdx++) {
                                long aSepChId = chTable.header.get(chHeadIdx);
                                int idx = chMap.get(aSepChId);
                                if (idx == -1) idx = n;
                                chTuple.set(chHeadIdx, tupleTree.get(idx));
                            }
                            utilCheck = Constraint.add(utilCheck, chTable.table.get(chTuple)[0]);
                            utilHat = Constraint.add(utilHat, chTable.table.get(chTuple)[1]);
                        } //-Added children cost

                        if (hasFrozenNeighbors) {
                            utilCheck = Constraint.add(utilCheck, pFrozen.evaluate(tupleFrozen, false));
                        }
                        // todo: check! utilCheck has to be Sat so for Hat to make sense?
                        // if (Constraint.isUnsat(utilCheck)) continue;

                        bestUtilCheck = Math.max(utilCheck, bestUtilCheck);
                        bestUtilHat = Math.max(utilHat, bestUtilHat);
                    }

                    if (Constraint.isSat(bestUtilCheck) || Constraint.isSat(bestUtilHat)) {
                        table.put(new Tuple(perm.getPermutation()),
                                new Integer[]{bestUtilCheck, bestUtilHat});
                    }
                }
            }

            /**
             * This method is used by the root agent only.
             * @todo if you want to handle unary constraints, add the constraintEvaluator part back, to retrieve them.
             * @todo This can be handled in O(1) -> chrono.
             */
            public int[] getBestValue() {
                int dMin = selfRef.getAgentView().getDomainMin();
                int dMax = selfRef.getAgentView().getDomainMax();
                Tuple chTuple = new Tuple(1);

                AgentView.Evaluator pFrozen = selfRef.getAgentView().pHatEvaluatorK;
                boolean hasFrozenNeighbors = (tupleFrozen.size() > 1);

                // Performs Projection of self
                int bestUtilCheck = Constants.worstValue();
                int bestUtilHat   = Constants.worstValue();
                int bestValueCheck = Constants.NaN;
                int bestValueHat   = Constants.NaN;
                for (int vSelf = dMin; vSelf <= dMax; vSelf++) {
                    int utilCheck = 0;
                    int utilHat = 0;

                    chTuple.set(0, vSelf);
                    if (hasFrozenNeighbors) tupleFrozen.set(0, vSelf);

                    // children cost ...
                    for (UtilTable chTable  : chUtilTables) {
                        utilCheck = Constraint.add(utilCheck, chTable.table.get(chTuple)[0]);
                        utilHat = Constraint.add(utilHat, chTable.table.get(chTuple)[1]);
                    } //-Added children cost

                    // Frozen neighbors cost ...
                    if (hasFrozenNeighbors) {
                        int frozenUtils = pFrozen.evaluate(tupleFrozen, false);
                        utilCheck = Constraint.add(utilCheck, frozenUtils);
                    }

                    if (Constraint.isSat(utilCheck) && utilCheck > bestUtilCheck) {
                        bestUtilCheck = utilCheck;
                        bestValueCheck = vSelf;
                    }
                    if (Constraint.isSat(utilHat) && utilHat > bestUtilHat) {
                        bestUtilHat = utilHat;
                        bestValueHat = vSelf;
                    }
                }
                // System.out.println(" Total Util = " + bestUtilCheck + ", " + bestUtilHat);
                return new int[]{bestValueCheck, bestValueHat};
            }

            /**
              * @todo This can be handled in O(1) -> chrono.
             */
            public int[] getBestValue(Tuple tupleCheck, Tuple tupleHat) {
                int n = header.size();
                int dMin = selfRef.getAgentView().getDomainMin();
                int dMax = selfRef.getAgentView().getDomainMax();
                // Already init in the generation phase
                AgentView.Evaluator pTree = selfRef.getAgentView().pCheckEvaluatorK;
                AgentView.Evaluator pFrozen = selfRef.getAgentView().pHatEvaluatorK;
                boolean hasFrozenNeighbors = (tupleFrozen.size() > 1);

                // tupleFroze is already initialized with values of destroyed variables

                int bestUtilCheck = Constants.worstValue();
                int bestUtilHat   = Constants.worstValue();
                int bestValueCheck = Constants.NaN;
                int bestValueHat   = Constants.NaN;
                int utilCheck; int utilHat;
                for (int vSelf = dMin; vSelf <= dMax; vSelf++) {
                    tupleCheck.set(n, vSelf);
                    tupleHat.set(n, vSelf);

                    if (hasFrozenNeighbors) tupleFrozen.set(0, vSelf);

                    utilCheck = pTree.evaluate(tupleCheck, false);
                    utilHat   = pTree.evaluate(tupleHat, false);

                    // children cost ...
                    for (int chIdx = 0; chIdx < chUtilTables.size(); chIdx++) {
                        UtilTable chTable = chUtilTables.get(chIdx);
                        Tuple chTuple = chTuples.get(chIdx);
                        HashMap<Long, Integer> chMap = chAgtHeaderMap.get(chIdx);

                        // P Check:
                        for (int chHeadIdx = 0; chHeadIdx < chTable.header.size(); chHeadIdx++) {
                            long aSepChId = chTable.header.get(chHeadIdx);
                            int idx = chMap.get(aSepChId);
                            if (idx == -1) idx = n;
                            chTuple.set(chHeadIdx, tupleCheck.get(idx));
                        }
                        utilCheck = Constraint.add(utilCheck, chTable.table.get(chTuple)[0]);

                        // P Hat:
                        for (int chHeadIdx = 0; chHeadIdx < chTable.header.size(); chHeadIdx++) {
                            long aSepChId = chTable.header.get(chHeadIdx);
                            int idx = chMap.get(aSepChId);
                            if (idx == -1) idx = n;
                            chTuple.set(chHeadIdx, tupleHat.get(idx));
                        }
                        utilHat = Constraint.add(utilHat, chTable.table.get(chTuple)[1]);
                    } //-Added children cost

                    if (hasFrozenNeighbors) {
                        utilCheck = Constraint.add(utilCheck, pFrozen.evaluate(tupleFrozen, false));
                    }


                    if (Constraint.isSat(utilCheck) && utilCheck > bestUtilCheck) {
                        bestUtilCheck = utilCheck;
                        bestValueCheck = vSelf;
                    }
                    if (Constraint.isSat(utilHat) && utilHat > bestUtilHat) {
                        bestUtilHat = utilHat;
                        bestValueHat = vSelf;
                    }
                }

                return new int[]{bestValueCheck, bestValueHat};
            }

            public List<Long> getHeader() {
                return header;
            }

            void clear() {
                header.clear();
                table.clear();
                perm.clear();
                chAgtHeaderMap.clear();
                chTuples.clear();
                tupleTree = null;
                tupleFrozen = null;
            }

            @Override
            public String toString() {
                String res = "";
                for (long a : header) {
                    res += "a_" + a + " ";
                }
                res += "\n";
                for (Map.Entry<Tuple, Integer[]> kv : table.entrySet()) {
                    res += kv.getKey().toString() + " " + kv.getValue()[0] + ", " + kv.getValue()[1] + "\n";
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
            ///System.out.println(selfRef.getName() + " CONTEXT Propagation started "
            ///        + "\t["+ selfRef.getAgentView().currentIteration+"]");


            // Count the number of messages that it is expected to receive:
            // todo: you can speed up this phase by counting it already from the destroy phase, or by
            // subtracting neighbors from P, PP, C, PC.
            long nbDestroyedNeighbors =
                    selfRef.getAgentView().destroyedNeighbor.values().stream().filter(p -> p == true).count();

            while (recvContextMsgs < nbDestroyedNeighbors) {
                selfRef.await();
            }

            //System.out.println(selfRef.getName() + " N_check" + selfRef.getAgentView().valueNeighborCheck);
            //System.out.println(selfRef.getName() + " N_hat" + selfRef.getAgentView().valueNeighborHat);
            terminate();
        }

        private void terminate() {
            terminated = true;
            recvContextMsgs = 0;
        }
    }


    /**
     * Note: This class could be brought outside directly in DLNSagent
     */
    public class BoundingPhase {
//        private boolean terminated;
        protected AgentView.Evaluator pCheckEvaluator;
        protected DLNSAgentView.UpperBoundEvaluator pHatEvaluator;
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
            pHatEvaluator = selfRef.getAgentView().pHatEvaluatorStar;
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

            if (!getPseduoTreeStar().isRoot()) {
                int n = HPNeighborContext.size();
                // Get current HPneighbors context and evaluate P-check costraints
                for (int i = 0; i < n; i++) {
                    tupleCheck.set(i, selfRef.getAgentView().valueNeighborCheck.get(HPNeighborContext.get(i)));
                    tupleHatK.set(i, selfRef.getAgentView().valueNeighborHat.get(HPNeighborContext.get(i)));
                }
                tupleCheck.set(n, selfRef.getAgentView().varCheckValueK);
                tupleHatK.set(n, selfRef.getAgentView().varHatValueK);

                LB.set(Constraint.add(LB.get(), pCheckEvaluator.evaluate(tupleCheck, false)));
                UB.set(Constraint.add(UB.get(), pHatEvaluator.evaluate(tupleHatK, j_updated)));

                // Send message to parent
                getPseduoTreeStar().getParent().tell(new BoundMessage(LB.get(), UB.get()), selfRef);
            }
            selfRef.getAgentView().lowerBoundK = LB.get();
            selfRef.getAgentView().upperBoundK = UB.get();

            // System.out.println(selfRef.getName() + " LB: " + LB.get() + " UB: " + UB.get());

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
    public static class LNInfoMessage extends RepairPhase.Message {
        /**
		 * 
		 */
		private static final long serialVersionUID = 824477351979743608L;
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

    public static class PTInfoMessage extends RepairPhase.Message {
        /**
		 * 
		 */
		private static final long serialVersionUID = -1923520727601915099L;
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

    public static class UtilMessage extends RepairPhase.Message {
        /**
		 * 
		 */
		private static final long serialVersionUID = 8032671764621176790L;
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

    public static class ValueMessage extends RepairPhase.Message {
        /**
		 * 
		 */
		private static final long serialVersionUID = -1441778490198636710L;
		public HashMap<Long,Integer[]> agtValues;

        ValueMessage(HashMap<Long,Integer[]> agtValues) {
            this.agtValues = agtValues;
        }

        @Override
        public String toString() {
            return "Repair::ValueMessage";
        }

    }

    public static class LNContextMessage extends  RepairPhase.Message {
        /**
		 * 
		 */
		private static final long serialVersionUID = -8139408282813267744L;
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

    public static class BoundMessage extends RepairPhase.Message {
        /**
		 * 
		 */
		private static final long serialVersionUID = 376795792009432979L;
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
