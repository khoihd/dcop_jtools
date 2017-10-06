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

package kernel;

import java.util.ArrayList;
import java.util.Random;

/**
 * Created by ffiorett on 7/7/15.
 */
public class IntVariable implements Variable {
    private String name;
    long ID;
    private Domain domain;
    private int value;

    AgentState ownerAgentState;
    ArrayList<Constraint> participatingConstraints;
    Random rand;

    public IntVariable(String name, long ID, int min, int max) {
        this.name = name;
        this.ID = ID;
        this.domain = new BoundDomain(min, max);
        this.value = domain.getMin();
        this.rand = new Random();

        participatingConstraints = new ArrayList<Constraint>();
    }

    @Override
    public Domain getDomain() {
        return domain;
    }

    @Override
    public void setDomain(Domain domain) {
        this.domain = domain;
    }

    @Override
    public long getID() {
        return ID;
    }

    @Override
    public void setID(long ID) {
        this.ID = ID;
    }

    @Override
    public int getValue() {
        return value;
    }

    @Override
    public void setValue(int value) {
        this.value = value;
    }

    @Override
    public void setValueAtRandom() {
        this.value = rand.nextInt(domain.getMax() - domain.getMin() + 1) + domain.getMin();
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public void setName(String name) {
        this.name = name;
    }

    @Override
    public void registerOwnerAgent(AgentState ownerAgentState) {
        this.ownerAgentState = ownerAgentState;
    }

    @Override
    public AgentState getOwnerAgent() {
        return ownerAgentState;
    }

    @Override
    public void registerParticipatingConstraint(Constraint constraint) {
        participatingConstraints.add(constraint);
        ownerAgentState.registerConstraint(constraint);
    }

    @Override
    public ArrayList<Constraint> getParticipatingConstraints() {
        return participatingConstraints;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        IntVariable that = (IntVariable) o;

        return ID == that.ID;
    }

    @Override
    public int hashCode() {
        return (int) (ID ^ (ID >>> 32));
    }

    @Override
    public String toString() {
        return "IntVariable{" +
                "domain=" + domain +
                ", value=" + value +
                ", name='" + name + '\'' +
                ", ID=" + ID +
                ", Owner=" + ownerAgentState.getName() +
                '}';
    }
}
