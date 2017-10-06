package agent.DLNS;

import communication.ComAgent;

import java.util.Random;

/**
 * Created by ffiorett on 8/2/15.
 */
public class RandomDestroy implements DestroyPhase {
    boolean terminated = false;
    int nbContextMsgReceived = 0;

    private static Random rnd;

    // Reference to the agentView of The DCOPagent
    private DLNSagent selfRef;

    public RandomDestroy(DLNSagent selfRef) {
        this.selfRef = selfRef;
        RandomDestroy.rnd = new Random();
    }

    @Override
    public void initialize() {
        terminated = false;
        nbContextMsgReceived = 0;
    }


    @Override
    public void start() {
        terminated = false;
        selfRef.getAgentView().varDestroyed = rnd.nextBoolean();

        if(selfRef.getAgentView().varDestroyed) {
        } else {
            int val = selfRef.getAgentView().getVariableValue();
            selfRef.getAgentView().varCheckValueK = val;
            selfRef.getAgentView().varHatValueK   = val;
        }

        // Send messages to all neighbors
        for (ComAgent a : selfRef.getNeighborsRef()) {
            a.tell(new RandomDestroy.ContextMessage(selfRef.getAgentView().isVarDestroyed(),
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
            ContextMessage msg = (ContextMessage) message;
            selfRef.getAgentView().destroyedNeighbor.put(sender.getId(), msg.isDestroyed());
            selfRef.getAgentView().valueNeighborCheck.put(sender.getId(), msg.getValue());
            selfRef.getAgentView().valueNeighborHat.put(sender.getId(), msg.getValue());
            nbContextMsgReceived ++;
        }
    }

    public void terminate() {
        nbContextMsgReceived = 0; // Prepare execution
        terminated = true;
    }

    /////////////////////////////////////////////////////////////////////////
    // Messages
    /////////////////////////////////////////////////////////////////////////
    public static class ContextMessage extends DestroyPhase.Message {
        /**
		 * 
		 */
		private static final long serialVersionUID = 4249844916731921279L;
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
}

