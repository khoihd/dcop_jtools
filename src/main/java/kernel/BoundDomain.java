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

/**
 * Created by ffiorett on 7/7/15.
 */
public class BoundDomain implements Domain {

    private String name;
    private long ID;
    private int min = 1;
    private int max = 0;

    public BoundDomain(int min, int max) {
        this.min = min;
        this.max = max;
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
    public void setID(long ID) {
        this.ID = ID;
    }

    @Override
    public long getID() { return ID; }

    @Override
    public int getElement(int pos) {
        try {
            if (pos < min || pos > max)
                throw new RuntimeException();
        } catch (Exception exc) {
            System.err.println("Trying to access invalid element " + exc.toString());
        }
        return ((max - min - 1) + pos);
    }

    @Override
    public int getMin() {
        return min;
    }

    @Override
    public int getMax() {
        return max;
    }

    @Override
    public boolean contains(int elem) {
        return (elem >= min && elem <= max);
    }

    @Override
    public boolean isEmpty() {
        return min > max;
    }

    @Override
    public int size() {
        return Math.max(0, max - min + 1);
    }

    @Override
    public String toString() {
        return "[" + min + "," + max + "]";
    }
}
