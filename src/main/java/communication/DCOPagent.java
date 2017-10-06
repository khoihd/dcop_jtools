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

import kernel.DCOPalgorithmState;

/**
 * Created by ffiorett on 7/10/15.
 */
public abstract class DCOPagent extends ComAgent {

    private ComAgent statsCollector;
    private int algorithmState;

    public DCOPagent(ComAgent statsCollector, String agentName, long agentID) {
        super(agentName, agentID);
        this.algorithmState = DCOPalgorithmState.INIT;
        this.statsCollector = statsCollector;
    }

    @Override
    protected void preStart() {
        statsCollector.tell(new StatisticsDeamon.WatchMe(getSelf()), getSelf());
    }

    @Override
    protected void onReceive(Object message, ComAgent sender) {
        super.onReceive(message, sender);

        if (message instanceof Messages.StartSignal) {
            algorithmState = DCOPalgorithmState.RUNNING;
            // Starts statistics collection
            getAgentStatistics().getStopWatch().start();

            onStart();
        }
        if (message instanceof Messages.EndSignal) {
            algorithmState = DCOPalgorithmState.STOP;
            preStop();
        }
    }

    @Override
    protected void preStop() {
        // Stops the statistics collection
        getAgentStatistics().getStopWatch().stop();
        long nanoTime = getAgentStatistics().getStopWatch().getNanoTime();
        long sentMessages = getAgentStatistics().getSentMessages();
        long NCCCs = 0;
        long milliTime = (long)(nanoTime * 1.0e-6);
//        System.out.println(getName() + " REPORT: sim time: " + milliTime + " ms. "
//        + " nb. msgs: " + sentMessages);
        statsCollector.tell(new StatisticsDeamon.AgentStatisticsInfo(milliTime, sentMessages, NCCCs), this);

        onStop();
    }

    /**
     * Actions to to prior starting the DCOP algorithm.
     */
    protected void onStart() {}

    /**
     * Actions to to prior terminating the DCOP algorithm.
     */
    protected void onStop() {
        if (!isAlgorithmState(DCOPalgorithmState.TERMINATED)) {
            for (ComAgent agt : getNeighborsRef()) {
                agt.tell(new Messages.EndSignal(), this);
            }
        }
        setAlgorithmState(DCOPalgorithmState.TERMINATED);
    }


    /**
     * @return The algorithm state code.
     */
    protected int getAlgorithmState() {
        return algorithmState;
    }

    /**
     * Checks if the algorithm state is the same as that given in input
     * @param state The state to be checked for equality
     */
    protected boolean isAlgorithmState(int state) {
        return algorithmState == state;
    }

    /**
     * Sets the algorithm state code.
     * @param algorithmState The algorithm state code.
     */
    protected void setAlgorithmState(int algorithmState) {
        this.algorithmState = algorithmState;
    }

}
