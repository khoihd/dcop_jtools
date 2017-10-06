package communication;

/**
 * Created by ffiorett on 7/31/15.
 */
public class TrackableObject {

    private Object first;
    private ComAgent second;

    public TrackableObject(Object first, ComAgent second) {
        super();
        this.first = first;
        this.second = second;
    }

    public int hashCode() {
        int hashFirst = first != null ? first.hashCode() : 0;
        int hashSecond = second != null ? second.hashCode() : 0;

        return (hashFirst + hashSecond) * hashSecond + hashFirst;
    }

    public boolean equals(Object other) {
        if (other instanceof TrackableObject) {
            TrackableObject otherPair = (TrackableObject) other;
            return
                    ((this.first == otherPair.first ||
                            (this.first != null && otherPair.first != null &&
                                    this.first.equals(otherPair.first))) &&
                            (this.second == otherPair.second ||
                                    (this.second != null && otherPair.second != null &&
                                            this.second.equals(otherPair.second))));
        }

        return false;
    }

    public String toString() {
        return "(" + first + ", " + second + ")";
    }

    public Object getObject() {
        return first;
    }

    public ComAgent getTrack() {
        return second;
    }

}