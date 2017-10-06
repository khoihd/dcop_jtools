package kernel;/*
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

import java.util.Arrays;

public class Permutations {
    int[] indexes;
    int[] domain;
    int[] currPermutation;
    int total;
    int nbVariables;
    int currPermutationIdx;

    public Permutations() { }

    public Permutations(int[] domain, int nbVariables){
        init(domain, nbVariables);
    }

    public void init(int[] domain, int nbVariables) {
        this.nbVariables = nbVariables;
        this.domain = domain;

        this.indexes = new int[nbVariables];
        this.currPermutation = new int[nbVariables];
        this.total = (int) Math.pow(domain.length, nbVariables);
        this.currPermutationIdx = 0;
    }

    public boolean hasNext() {
        if (currPermutationIdx++ == total)
            return false;

        for (int i = 0; i < nbVariables; i++)
            currPermutation[i] = domain[indexes[i]];

        for (int i = nbVariables-1; i >= 0; i--) {
            if (indexes[i] >= domain.length - 1) {
                indexes[i] = 0;
            } else {
                indexes[i]++;
                break;
            }
        }
        return true;
    }

    public int[] getPermutation() {
        return currPermutation;
    }

    public void reset() {
        Arrays.fill(indexes, 0);
        Arrays.fill(currPermutation, Constants.NaN);
        currPermutationIdx = 0;
    }

    public void clear() {
        indexes = null;
        domain = null;
        currPermutation = null;
        currPermutationIdx = 0;
        nbVariables = 0;
        total = 0;
    }
}
