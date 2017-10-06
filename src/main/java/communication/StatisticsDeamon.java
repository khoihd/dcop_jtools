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

import java.io.Serializable;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.BlockingQueue;

/**
 * Created by ffiorett on 7/14/15.
 */
public class StatisticsDeamon extends ComAgent {
    BlockingQueue<ComAgent> watched = new ArrayBlockingQueue<ComAgent>(500);

    private long simulatedTimeMillisec;
//    private long totSentMessages;
    private long maxSentMessages;
//    private int  solutionQuality;
    private long NCCCs;
    private int nbAgents;
    private int nbWatched;

    public StatisticsDeamon(int nbAgents) {
        super("statisticDeamon", -1);
        this.nbAgents = nbAgents;
        this.nbWatched = 0;
        simulatedTimeMillisec = 0;
//        totSentMessages = 0;
        maxSentMessages = 0;
        NCCCs = 0;
    }

    @Override
    public void preStart() {

    }

    @Override
    public void preStop() {
//        System.out.println("Algorithm Statistics: \n" +
//                " Quality: " + solutionQuality + "\n" +
//                " Simulated time: " + simulatedTimeMillisec + " ms\n" +
//                " Network load  : " + totSentMessages + "(" + maxSentMessages + ")\n" +
//                " NCCCs         : " + NCCCs);
    }

    @Override
    public void onReceive(Object message, ComAgent sender) {
        //onReceive(message, sender);

        if (message instanceof WatchMe) {
            WatchMe watchme = (WatchMe) message;
            try { watched.put(watchme.ref); } catch (InterruptedException e) {e.printStackTrace();}
            nbWatched++;
        } else if (message instanceof AgentStatisticsInfo) {
            AgentStatisticsInfo stats = (AgentStatisticsInfo) message;
            simulatedTimeMillisec = Math.max(simulatedTimeMillisec, stats.simulatedTimeMillisec);
            maxSentMessages = Math.max(maxSentMessages, stats.sentMessages);
            NCCCs = Math.max(NCCCs, stats.NCCCs);
//            totSentMessages += stats.sentMessages;
//            String sName = sender == null ? "none" : sender.getName();
//            String sName = sender == null ? "none" : sender.getName();

            watched.remove(sender);
        }


    }

    @Override
    public boolean terminationCondition() {
        return (nbWatched == nbAgents && watched.isEmpty());
    }

    //////////////
    // Messages
    //////////////
    public static class AgentStatisticsInfo implements Serializable {
        private static final long serialVersionUID = 3000000000000000001L;
        public long simulatedTimeMillisec;
        public long sentMessages;
        public long NCCCs = 0;
        public int solutionQuality = 0;
        // public int[] solution;

        public AgentStatisticsInfo(long simulatedTimeMillisec, long sentMessages, long NCCC) {
            this.simulatedTimeMillisec = simulatedTimeMillisec;
            this.sentMessages = sentMessages;
            this.NCCCs = NCCC;
        }

        @Override
        public String toString() {
            return "KillMe and Stats";
        }

    }

    public static class WatchMe implements Serializable {
        private static final long serialVersionUID = 1000000000000000001L;
        public ComAgent ref;

        public WatchMe(ComAgent ref) {
            this.ref = ref;
        }

        @Override
        public String toString() {
            return "WatchMe";
        }

    }

}
