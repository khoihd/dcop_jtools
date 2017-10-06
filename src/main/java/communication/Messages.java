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
 * Created by ffiorett on 7/17/15.
 */
public class Messages {
    public static class RegisterNeighbor implements Serializable {
        private static final long serialVersionUID = 1100000000000000001L;
        private final ComAgent agentRef;
        private final long agentID;

        public RegisterNeighbor(ComAgent ref, long agentID) {
            this.agentRef = ref;
            this.agentID = agentID;
        }

        public ComAgent getAgentRef() {
            return agentRef;
        }

        public long getAgentID() {
            return agentID;
        }

        @Override
        public String toString() {
            return "Register Neighbor";
        }
    }

    public static class RegisterLeader implements Serializable {
        private static final long serialVersionUID = 1100000000000000001L;
        private final ComAgent agentRef;

        public RegisterLeader(ComAgent ref) {
            this.agentRef = ref;
        }

        public ComAgent getAgentRef() {
            return agentRef;
        }

        @Override
        public String toString() {
            return "Register Leader";
        }
    }

    public static class StartSignal implements Serializable {
        private static final long serialVersionUID = 1100000000000000002L;

        @Override
        public String toString() {
            return "Start Signal";
        }
    }

    public static class EndSignal implements Serializable {
        private static final long serialVersionUID = 1100000000000000003L;

        @Override
        public String toString() {
            return "End Signal";
        }

    }
}
