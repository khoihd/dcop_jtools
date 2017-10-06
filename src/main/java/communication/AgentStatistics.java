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
import java.util.List;

/**
 * Created by ffiorett on 7/13/15.
 */
public class AgentStatistics {
    private StopWatch stopWatch;
    private int sentMessages;

    private List<Integer> sentMessagesIter;
    private List<Long> nanoTimeIter;
    private List<Integer[]> solutionBoundsIter;

    public AgentStatistics() {
        this.stopWatch = new StopWatch();
        sentMessages = 0;
        sentMessagesIter = new ArrayList<>();
        nanoTimeIter = new ArrayList<>();
        solutionBoundsIter = new ArrayList<>();
    }

    public StopWatch getStopWatch() {
        return stopWatch;
    }

    public void incrSentMessages() {
        sentMessages++;
    }

    public void incrSentMessages(int n) {
        sentMessages += n;
    }

    public void updateIterationStats() {
        stopWatch.suspend();
        sentMessagesIter.add(sentMessages);
        nanoTimeIter.add(stopWatch.getNanoTime());
        stopWatch.resume();
    }

    public void updateIterationBounds(int LB, int UB) {
        solutionBoundsIter.add(new Integer[]{LB, UB});
    }

    public Integer[] getBounds(int iter) {
        return solutionBoundsIter.get(iter);
    }

    public int size() {
        return solutionBoundsIter.size();
    }

    public int getSentMessages() {
        return sentMessages;
    }

    public int getSentMessages(int iter) {
        return sentMessagesIter.get(iter);
    }

    public long getMilliTime(int iter) {
        return (long) (nanoTimeIter.get(iter) * 1.0e-6);
    }

    public void resetSentMessages() {sentMessages = 0;}

    @Override
    public String toString() {
        return  "simulated Time: " + stopWatch.getMilliTime() + " ms " +
                " sent Messages: " + sentMessages;
    }
}
