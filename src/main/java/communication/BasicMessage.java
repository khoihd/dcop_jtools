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

/**
 * Created by ffiorett on 7/9/15.
 */
public class BasicMessage implements Serializable {
    private static final long serialVersionUID = 4374372743494239547L;
    private boolean trackable;
    private long simulatedNanoTime;
    private long NCCCs;
//    ComAgent sender;

    // Carries NCCCs and simulated time.
    public BasicMessage() {
        simulatedNanoTime = 0;
        NCCCs = 0;
        trackable = true;
    }

    public BasicMessage(boolean trackable/*ComAgent sender*/) {
        simulatedNanoTime = 0;
        NCCCs = 0;
        this.trackable = trackable;
    }

    public long getSimulatedNanoTime() {
        return simulatedNanoTime;
    }

    public void setSimulatedNanoTime(long simulatedNanoTime) {
        this.simulatedNanoTime = simulatedNanoTime;
    }

    public long getNCCCs() {
        return NCCCs;
    }

    public void setNCCCs(long NCCCs) {
        this.NCCCs = NCCCs;
    }

    public boolean isTrackable() {
        return trackable;
    }

    public void setTrackable(boolean trackable) {
        this.trackable = trackable;
    }
}
