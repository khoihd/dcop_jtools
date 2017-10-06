package kernel;

/**
 * Created by ffiorett on 8/1/15.
 * Defines the actions of the agent.
 */
public class AgentActions {

    private final AgentState agentState;

    public AgentActions(AgentState agentState) {
        this.agentState = agentState;
    }

    public void setVariableValue(int value) {
        agentState.getVariable().setValue(value);
    }

    public void setVariableValue(int varIdx, int value) {
        agentState.getVariable(varIdx).setValue(value);
    }

    public void setVariableVariableAtRandom() {
        agentState.getVariable().setValueAtRandom();
    }

    public void setVariableVariableAtRandom(int varIdx) {
        agentState.getVariable(varIdx).setValueAtRandom();
    }

}
