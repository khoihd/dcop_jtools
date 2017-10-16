package agent.DLNS;

import communication.BasicMessage;
import communication.ComAgent;

/**
 * Created by ffiorett on 8/2/15.
 */
public interface DestroyPhase {

    void start();

    void initialize();

    boolean isTerminated();

    void onReceive(DestroyPhase.Message message, ComAgent sender);
    
    public void setCurrentIteration(int iteration);

    static class Message extends BasicMessage {

		/**
		 * 
		 */
		private static final long serialVersionUID = -674712959488828759L;}
}

