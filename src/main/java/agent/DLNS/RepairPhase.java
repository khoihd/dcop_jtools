package agent.DLNS;

import communication.BasicMessage;
import communication.ComAgent;

/**
 * Created by ffiorett on 8/2/15.
 */
public interface RepairPhase {

    void start();

    void initialize();

    boolean isTerminated();

    void onReceive(RepairPhase.Message message, ComAgent sender);
    
	public void setJ_updated(boolean j_updated);
	
	public void setCurrentIteration(int iteration);

    static class Message extends BasicMessage {

		/**
		 * 
		 */
		private static final long serialVersionUID = -8988136705188323892L;}

}
