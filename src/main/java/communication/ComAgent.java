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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.BlockingQueue;

/**
 * Created by ffiorett on 7/17/15.
 * This is an abstract class, which describes a basic "communicating agent", that is, an
 * agent which is able to communicate over the network with other agents.
 * Each DCOP agent (or AKKA actor) should extend from this class or one of its subclasses,
 * as it contains the messageStatistics.
 */
public abstract class ComAgent extends Thread { //implements Runnable {

    private long agentID; // ID of the agent starting from 0
    private List<ComAgent> neighborsRef;
    private HashMap<Long, ComAgent> neigbhorRefByID;
    private ComAgent leaderRef = null;
    private AgentStatistics agentStatistics;
    private BlockingQueue<TrackableObject> mailbox;
    //String name;

    public ComAgent(String name, long agentID) {
        super.setName(name);
        this.agentID = agentID;
        this.neighborsRef = new ArrayList<ComAgent>();
        this.neigbhorRefByID = new HashMap<Long, ComAgent>();
        this.agentStatistics = new AgentStatistics();
        this.mailbox = new ArrayBlockingQueue<TrackableObject>(1000);
        agentStatistics.getStopWatch().start();
    }

    @Override
    public void run() {
        preStart();
        while (!terminationCondition()) {
            await();
        }
        preStop();
    }

    protected abstract boolean terminationCondition();

    protected abstract void preStart();

    protected abstract void preStop();

    protected void onReceive(Object message, ComAgent sender) {
        if (message instanceof BasicMessage) {
            // Save statistics info
            agentStatistics.getStopWatch().suspend();
            long recvSimTime = ((BasicMessage) message).getSimulatedNanoTime();
            agentStatistics.getStopWatch().updateTimeIfFaster(recvSimTime);
            agentStatistics.getStopWatch().resume();            // Resumes Simulated Time (if suspended)
        } else if (message instanceof Messages.RegisterNeighbor) {
            Messages.RegisterNeighbor actorNeighbor = (Messages.RegisterNeighbor) message;
            if (actorNeighbor.getAgentRef() != getSelf()) {
                neighborsRef.add(actorNeighbor.getAgentRef());
                neigbhorRefByID.put(actorNeighbor.getAgentID(), actorNeighbor.getAgentRef());
            }
        } else if (message instanceof  Messages.RegisterLeader) {
            Messages.RegisterLeader leaderMsg = (Messages.RegisterLeader) message;
            if (leaderMsg.getAgentRef() != getSelf()) {
                leaderRef = leaderMsg.getAgentRef();
            }
        }
    }

    /**
     * Sends a message to this agent.
     * @param message The message to be sent
     * @param sender  The sender of the message
     */
    public void tell(Object message, ComAgent sender) {
        try {
//            String sName = sender == null ? "none" : sender.getName();
//            System.out.println(sName + " sending " + message.toString() + " to " + getName());
            mailbox.put(new TrackableObject(message, sender));
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }

    /**
     * Mirror of tell function for BasicMessage objects.
     * It is used to update the statistics.
     * @param message The message to be sent
     * @param sender  The sender of the message
     */
    public void tell(BasicMessage message, ComAgent sender) {
        sender.getAgentStatistics().getStopWatch().suspend();
        if (message.isTrackable())
            message.setSimulatedNanoTime(sender.getAgentStatistics().getStopWatch().getNanoTime());
        try {
            mailbox.put(new TrackableObject(message, sender));
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
        if (message.isTrackable())
            sender.getAgentStatistics().incrSentMessages();
        sender.getAgentStatistics().getStopWatch().resume();
    }


    /**
     * Awaits while checking if the message queue is non empty. In which case, it process the message.
     * TODO: Change for await to some condition?
     */
    public void await() {
        agentStatistics.getStopWatch().suspend();

        if (mailbox.isEmpty()) {
            Thread.yield();
        } else {
            try {
                TrackableObject to = mailbox.take();

                agentStatistics.getStopWatch().resume();
                onReceive(to.getObject(), to.getTrack());
            } catch (Exception e) {
                e.printStackTrace();
            }
        }
    }

    public ComAgent getSelf() {
        return this;
    }

    /**
     * Overrides the Thread ID method to return the agent ID
     */
    @Override
    public long getId() {
        return agentID;
    }

    public static ComAgent noSender() {
        return null;
    }

    /**
     * @return The agent's neighbors references.
     */
    public List<ComAgent> getNeighborsRef() {
        return neighborsRef;
    }

    public int getNbNeighbors() {
        return neighborsRef.size();
    }

    public ComAgent getNeigbhorRefByID(long agentID) {
        return neigbhorRefByID.get(agentID);
    }

    public ComAgent getLeaderRef() {
        return leaderRef;
    }

    public boolean isLeader() {
        return leaderRef == null;
    }

    /**
     * @return The agent statistcs.
     */
    public AgentStatistics getAgentStatistics() {
        return agentStatistics;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof ComAgent)) return false;

        ComAgent comAgent = (ComAgent) o;

        if (agentID != comAgent.agentID) return false;

        return true;
    }

    @Override
    public int hashCode() {
        return (int) (agentID ^ (agentID >>> 32));
    }

    @Override
    public String toString() {
        return getName();
    }
}
