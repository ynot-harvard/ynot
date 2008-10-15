import java.util.*;

public class Event {
    public Date date;
    public String message;
    public int status;

    public static final int ACKED = 1;
    public static final int PENDING = 2;
}
