package agent.DLNS;

import communication.ComAgent;
import communication.DCOPinfo;
import kernel.AgentView;
import kernel.Tuple;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Random;
import java.util.Stack;
import java.util.stream.Collectors;

/**
 * Created by ffiorett on 8/2/15.
 */
public class MeetingDestroy implements DestroyPhase {
    private boolean terminated = false;
    private int nbContextMsgReceived = 0;
    private int nbNogoodMsgReceived = 0;
    private boolean recvDestroyInfo = false;
    private ArrayList<Long>[] agtsNogoods;
    private AgentView.Evaluator constraintsEvaluator;
    private ArrayList<Long> evaluatorAgtsId = new ArrayList<>();
    private Tuple evaluatorTuple;
    private Destroyer destroyer;
    private int totNogoods;
    private int currentIteration;

    // Reference to the agentView of The DCOPagent
    private DLNSagent selfRef;

    public MeetingDestroy(DLNSagent selfRef) {
        this.selfRef = selfRef;
        destroyer = new Destroyer();
    }

    @SuppressWarnings("unchecked")
	@Override
    public void initialize() {
        terminated = false;
        recvDestroyInfo = false;
        nbNogoodMsgReceived = 0;
        nbContextMsgReceived = 0;
        totNogoods = 0;
        agtsNogoods = new ArrayList[DCOPinfo.nbAgents];
        for (int i = 0; i < DCOPinfo.nbAgents; i++)
            agtsNogoods[i] = new ArrayList<>();
        constraintsEvaluator = selfRef.getAgentView().nogoodsEvaluator;

        destroyer.initialize();
        evaluatorAgtsId = new ArrayList<>();
        evaluatorAgtsId.add(selfRef.getId());
        evaluatorAgtsId.addAll(selfRef.getNeighborsRef().stream().map(ComAgent ->
                ComAgent.getId()).collect(Collectors.toList()));
        constraintsEvaluator.initialize(evaluatorAgtsId);
        evaluatorTuple = new Tuple(evaluatorAgtsId.size());
    }


    @Override
    public void start() {
        terminated = false;

        if (selfRef.getAgentView().currentIteration == 1) {
            destroyer.destroyAgtRandom();
            // selfRef.getAgentView().varDestroyed = false;  // todo: remove this and keep the above.

        }
        else {
            // Prepare list of nogoods:
            evaluatorTuple.set(0, selfRef.getAgentView().getVariableValue());
            for (int i = 1; i < evaluatorTuple.size(); i++) {
                int val = selfRef.getAgentView().valueNeighborCheck.get(evaluatorAgtsId.get(i));
                evaluatorTuple.set(i, val);
            }
            ArrayList<Long> nogoods = constraintsEvaluator.getNogoods(evaluatorTuple);
            //System.out.println(selfRef.getName() + " Nogoods Links with Var: " + nogoods.toString());

            if (!selfRef.isLeader()) {
                // Send NoGood message to Leader:
                DCOPinfo.leaderAgent.tell(new NogoodMessage(nogoods), selfRef);

                // Wait to receive the Destroied Info state
                while (!recvDestroyInfo) {
                    selfRef.await();
                }
            } else {

                // wait to receive all NoGood messages
                while (nbNogoodMsgReceived < (DCOPinfo.nbAgents-1)) {
                    selfRef.await();
                }
                agtsNogoods[(int)selfRef.getId()] = nogoods;
                totNogoods += nogoods.size();

                // if no conflict: random assign them:
                if (totNogoods == 0) {
                    //System.out.println("Destroying at random");
                    destroyer.destroyRandom();
                } else {
                    //System.out.println("Tot conflicts: " + totNogoods + " Calling specialized destory");
                    destroyer.destroyConflicts();
                }
                for (ComAgent agt : DCOPinfo.agentsRef) {
                    if (!agt.equals(selfRef)) {
                        agt.tell(new DestroyStateInfo(
                                destroyer.isDestroyed((int) agt.getId())), selfRef);
                    } else {
                        selfRef.getAgentView().varDestroyed = destroyer.isDestroyed((int) agt.getId());
                    }
                }
            }
        }

        if (selfRef.getAgentView().varDestroyed) {
           //System.out.println(selfRef.getAgentView().currentIteration + ": " + selfRef.getName() + " var DESTROYED");
           // do not reset this value, otherwise i cannot take value of frozen values at previous iteration.
           // selfRef.getAgentActions().setVariableValue(Constants.NaN);
        } else {
            int val = selfRef.getAgentView().getVariableValue();
            selfRef.getAgentView().varCheckValueK = val;
            selfRef.getAgentView().varHatValueK   = val;
            //System.out.println(selfRef.getAgentView().currentIteration + ": " + selfRef.getName() + " var KEEPT: " + val);
        }

        // Send messages to all neighbors
        for (ComAgent a : selfRef.getNeighborsRef()) {
            a.tell(new MeetingDestroy.ContextMessage(selfRef.getAgentView().isVarDestroyed(),
                    selfRef.getAgentView().getVariableValue()), selfRef);
        }

        while (nbContextMsgReceived < selfRef.getNeighborsRef().size()) {
            selfRef.await();
        }

        terminate();
    }

    @Override
    public boolean isTerminated() {
        return terminated;
    }

    @Override
    public void onReceive(Message message, ComAgent sender) {
        if (message instanceof ContextMessage) {
            // System.out.println(selfRef.getName() + " recv message " + message.toString() + " from " + sender.getName() );
            ContextMessage msg = (ContextMessage) message;
            selfRef.getAgentView().destroyedNeighbor.put(sender.getId(), msg.isDestroyed());
            selfRef.getAgentView().valueNeighborCheck.put(sender.getId(), msg.getValue());
            selfRef.getAgentView().valueNeighborHat.put(sender.getId(), msg.getValue());
            nbContextMsgReceived ++;
        } else if (message instanceof DestroyStateInfo) {
            DestroyStateInfo msg = (DestroyStateInfo) message;
            selfRef.getAgentView().varDestroyed = msg.isDestroyState();
            recvDestroyInfo = true;
        } else if (message instanceof  NogoodMessage) {
            NogoodMessage msg = (NogoodMessage) message;
            agtsNogoods[(int)sender.getId()] = msg.getNogoods();
            totNogoods += msg.getNogoods().size();
            nbNogoodMsgReceived++;
        }
    }

    public void terminate() {
        nbContextMsgReceived = 0; // Prepare for next execution
        nbNogoodMsgReceived = 0;  // Prepare for next execution
        recvDestroyInfo = false;  // Prepare for next execution
        totNogoods = 0;
        terminated = true;
    }

    public class Destroyer {
        boolean[] discovered;
        int[] destroyedAgts;
        Stack<ComAgent> dfsQueue;
        private Random rnd;


        protected void initialize() {
            final int nbAgents = DCOPinfo.nbAgents;
            discovered = new boolean[nbAgents];
            destroyedAgts = new int[nbAgents];
            Arrays.fill(discovered, false);
            Arrays.fill(destroyedAgts, -1);
            dfsQueue = new Stack<>();
            rnd = new Random();
        }

        protected void destroyConflicts() {
            Arrays.fill(discovered, false);
            Arrays.fill(destroyedAgts, -1);

            ComAgent root = DCOPinfo.leaderAgent;
            dfsQueue.push(root);

            while (!dfsQueue.empty()) {
                ComAgent agt = dfsQueue.pop();
                int agtIdx = (int) agt.getId();

                if (!discovered[agtIdx]) {
                    if (destroyedAgts[agtIdx] == -1) {
                        destroyedAgts[agtIdx] = agtsNogoods[agtIdx].isEmpty() ? 0 : 1;
                    }

                    for (ComAgent chAgt : agt.getNeighborsRef()) {
                        int chIdx = (int) chAgt.getId();
                        dfsQueue.push(chAgt);
                        // chAgt is a child of agt; and agt is parent of chAgt
                        if (destroyedAgts[chIdx] == -1) {
                            if (agtsNogoods[agtIdx].contains(chAgt.getId())) {
                                destroyedAgts[chIdx] = (destroyedAgts[agtIdx] + 1) % 2;
                            }
                        }
                    }//-neighbors
                    discovered[agtIdx] = true;
                }//-discovered
            }//-Tree

        }

        protected void destroyRandom() {
            for (ComAgent agt : DCOPinfo.agentsRef) {
                destroyedAgts[(int) agt.getId()] = rnd.nextBoolean() ? 1 : 0;
            }
        }

        protected void destroyAgtRandom() {
            selfRef.getAgentView().varDestroyed = rnd.nextBoolean();
        }

        protected boolean isDestroyed(int agtID) {
            return destroyedAgts[ agtID ] == 1;
        }
    }

    /////////////////////////////////////////////////////////////////////////
    // Messages
    /////////////////////////////////////////////////////////////////////////
    public static class ContextMessage extends Message {
        /**
		 * 
		 */
		private static final long serialVersionUID = -2667857522827334044L;
		private final boolean destroyed;
        private final int value;

        public ContextMessage(boolean destroyed, int value) {
            this.destroyed = destroyed;
            this.value = value;
        }

        public int getValue() {
            return value;
        }

        public boolean isDestroyed() {
            return destroyed;
        }

        @Override
        public String toString() {
            return "Destroy::ContextMessage";
        }
    }

    public static class NogoodMessage extends Message {
        /**
		 * 
		 */
		private static final long serialVersionUID = 101394393474631337L;
		private ArrayList<Long> nogoods = new ArrayList<>();

        public NogoodMessage(ArrayList<Long> nogoods) {
            this.nogoods = nogoods;
        }

        public ArrayList<Long> getNogoods() {
            return nogoods;
        }

        @Override
        public String toString() {
            return "Destroy::NogoodMessage";
        }
    }

    public static class DestroyStateInfo extends Message {
        /**
		 * 
		 */
		private static final long serialVersionUID = 5537306227421320567L;
		private boolean destroyState;

        public DestroyStateInfo(boolean destroyState) {
            this.destroyState = destroyState;
        }

        public boolean isDestroyState() {
            return destroyState;
        }
    }

    @Override
    public void setCurrentIteration(int iteration) {
        // TODO Auto-generated method stub
        this.currentIteration = iteration;
    }
}

