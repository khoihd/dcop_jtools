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

/**
 * Created by ffiorett on 7/10/15.
 */
public class StopWatch {
    private long startTime;
    private long stopTime;
    private long totalTime;
    private boolean suspended;

    public StopWatch() {
        this.startTime = 0;
        this.stopTime = 0;
        this.totalTime = 0;
        this.suspended = false;
    }

    /**
     * Gets the start time of the StopWatch in nanoseconds.
     */
    public long getStartTime() {
        return startTime;
    }

    /**
     * Gets the stop time of the StopWatch in nanoseconds.
     */
    public long getStopTime() {
        return stopTime;
    }

    /**
     * Gets the total time of the StopWatch in nanoseconds.
     */
    public long getNanoTime() {
        return totalTime;
    }

    public long getMilliTime() {
        return (long)(totalTime * 1.0e-6);
    }

    /**
     * Sets the total time of the StopWatch in nanoseconds if totalTime > this.totalTime.
     * @param totalTime Another total time in nanoseconds.
     */
    public void updateTimeIfFaster(long totalTime) {
        if (this.totalTime < totalTime)
            this.totalTime = totalTime;
    }

    /**
     * Starts the StopWatch.
     */
    public void start() {
        startTime = System.nanoTime();
        stopTime = startTime;
        suspended = false;
    }

    /**
     * Stops the StopWatch.
     */
    public void stop() {
        stopTime = System.nanoTime();
        if (!suspended)
            totalTime += (stopTime - startTime);
    }

    public void suspend() {
        if (!suspended) {
            suspended = true;
            long timeNow = System.nanoTime();
            totalTime += (timeNow - startTime);
            startTime = 0;
        }
    }

    public void resume() {
        if (suspended) {
            start();
            suspended = false;
        }
    }

    /**
     * The method is used to find out if the StopWatch is started.
     */
    boolean isStarted() {
        return startTime != 0;
    }

    /**
     * The method is used to find out if the StopWatch is suspended.
     */
    public boolean isSuspended() {
        return suspended;
    }

    /**
     * The method is used to find out if the StopWatch is stopped.
     */
    public boolean isStopped() {
        return stopTime != startTime;
    }

    /**
     * Resets the StopWatch.
     */
    public void reset() {
        startTime = 0;
        stopTime = 0;
        totalTime = 0;
        suspended = false;
    }

    @Override
    public String toString() {
        return "StopWatch{" +
                "startTime=" + (long)(startTime / 1.0e-6) + "ms" +
                ", stopTime=" + (long)(stopTime / 1.0e-6) + "ms" +
                ", totalTime=" + (long)(totalTime / 1.0e-6) + "ms" +
                ", suspended=" + suspended +
                '}';
    }
}
