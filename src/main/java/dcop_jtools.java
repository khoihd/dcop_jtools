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

import communication.DCOPagent;
import communication.DCOPinfo;
import communication.Spawner;
import kernel.Constants;
import kernel.Constraint;
import kernel.DCOPInstance;
import kernel.DCOPInstanceFactory;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.nio.file.Paths;

/**
 * Created by ffiorett on 7/7/15.
 */
public class dcop_jtools {

	public static void main(String argv[]) {
        String repairPhase = "TDBR";
        String destroyPhase = "RAND";
        List<Object> algParams = new ArrayList<>();
        int nbIterations = 500;
        long timeoutMs = Constants.infinity; // no-timeout
//        String path = Paths.get(".").toAbsolutePath().normalize().toString();
        // String file = "/Users/ffiorett/GitRepositories/dcop_jtools/src/test/files/simple.xml";
        // String file = "/Users/ffiorett/GitRepositories/dcop_generator/build/test/rep_0_test.xml";
//        String file = path + "src/test/files/meeting.xml";
        // String file = "/home/grad12/ffiorett/research/IJCAI2015/LNS-DCOP/instances/exp4_25/rep_0_exp4.xml";

        if (argv.length < 1) {
            System.out.println(getUsage());
            return;
        }
        String file = argv[0];
        for (int i = 1; i < argv.length; i++) {
            if (argv[i].equals("-i") || argv[i].equals("--iterations")) {
                nbIterations = Integer.parseInt(argv[i+1]);
            }
            if (argv[i].equals("-r") || argv[i].equals("--repair")) {
                repairPhase = argv[i+1];
            }
            if (argv[i].equals("-d") || argv[i].equals("--destroy")) {
                destroyPhase = argv[i+1];
            }
            if (argv[i].equals("-t") || argv[i].equals("--timeout")) {
                timeoutMs = Long.parseLong(argv[i+1]);
            }
        }

        DCOPInstance dcopInstance = DCOPInstanceFactory.importDCOPInstance(file);
        Spawner spawner = new Spawner(dcopInstance);
        algParams.add(destroyPhase);
        algParams.add(repairPhase);
        algParams.add(nbIterations);
        algParams.add(timeoutMs);
        spawner.spawn(algParams);

        // Summary Output
        System.out.println(getSummary(spawner.getSpawnedAgents(), nbIterations));
    }

    public static String getUsage() {
        return "dcop_jtool FILE.xml [options]\n" +
                "  where options is one of the following:\n" +
                "  --repair (-r) [GDBR, TDBR(default)]. The DLNS repair phase.\n" +
                "  --destroy (-d) [RAND(default), MEETINGS]. The DLNS destroy phase.\n" +
                "  --iterations (-i) (default=500). The number of iterations of DLNS.\n" +
                "  --timeout (-t) (default=no timeout (0)). The simulated time maximal execution time.\n";
    }

    public static String getSummary(Collection<DCOPagent> agents, int nbIterations) {
        String res = "time\tLB\tUB\tIterAgtMsgs\tnAgtMsgs\tNetLoad\n";
        int maxIter = DCOPinfo.leaderAgent.getAgentStatistics().size();
        int bestLB = DCOPinfo.leaderAgent.getAgentStatistics().getBounds(maxIter-1)[0];
        long maxTime = 0; int nMsgs = 0; int netLoad = 0;
        int lb = 0; int ub = 0;
        int prevLB = Constants.NaN; int prevUB = Constants.NaN;

        for (int iter = 0; iter < maxIter; iter++) {
            int agtMsgs = 0;
            boolean save = false;
            for (DCOPagent agt : agents) {
                if (iter >= agt.getAgentStatistics().size()) continue;
                maxTime = Math.max(maxTime, agt.getAgentStatistics().getMilliTime(iter));
                int msgNow =  agt.getAgentStatistics().getSentMessages(iter);
                int msgPrev = iter == 0 ? 0 : agt.getAgentStatistics().getSentMessages(iter-1);
                nMsgs = Math.max(nMsgs, msgNow);
                agtMsgs = Math.max(agtMsgs, (msgNow - msgPrev));
                netLoad += (msgNow - msgPrev);
                if (agt.isLeader()) {
                    lb = agt.getAgentStatistics().getBounds(iter)[0];
                    ub = agt.getAgentStatistics().getBounds(iter)[1];
//                    if (ub < bestLB) ub = bestLB;         // TODO: !!!!!!!!!!! Fix this !!!!!!!!!!!!
                    if (prevLB != lb) {prevLB = lb; save = true;}
                    if (prevUB != ub) {prevUB = ub; save = true;}
                }
            }
            if (save) {
                res += maxTime + "\t";
                if (Constraint.isSat(ub) && Constraint.isSat(lb)) {
                    res += lb + "\t" + ub + "\t";
                } else {
                    res += "NA\tNA\t";
                }
                res += + agtMsgs + "\t" + nMsgs + "\t" + netLoad + "\n";
            }
        }
        return  res;
    }

}

