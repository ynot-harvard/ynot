import java.io.*;
import java.text.*;
import java.util.*;

public class Reminder {
    IterSet acknowledgedEvents;
    IterSet displayedEvents;
    IterSet pendingEvents;

    private static final String ackedStr = "acked";
    private static final String pendingStr = "pending";

    private void parseError(String msg) {
        throw new Error("PARSE ERROR: " + msg);
    }

    private void parseEntry(String dateLine, String textLine, String statusLine) {
        Util.wrConsole("Parsing entry:");
        Util.wrConsole(dateLine);
        Util.wrConsole(textLine);
        Util.wrConsole(statusLine);
        Event e = new Event();
        SimpleDateFormat df = 
            new SimpleDateFormat("EEE, d MMM yyyy HH:mm:ss z");
        try {
            e.date = df.parse(dateLine);
        } catch (ParseException ex) {
            parseError("Error parsing date " + dateLine);
        }
        e.message = textLine;
        if (statusLine.equals(ackedStr)) {
            e.status = Event.ACKED;
        } else if (statusLine.equals(pendingStr)) {
            e.status = Event.PENDING;
        } else {
            parseError("Count not parse status description " + statusLine);
        }
        pendingEvents.add(e);
    }

    private void parseFrom(String fileName) throws IOException {
        LineNumberReader f = 
            new LineNumberReader(new FileReader(new File(fileName)));
        while (true) {
            String dateLine = f.readLine();
            if (dateLine==null) { break; }
            String textLine = f.readLine();
            if (textLine==null) { 
                parseError("Fragmented last entry:" + dateLine);
                break; 
            }
            String statusLine = f.readLine();
            if (statusLine==null) { 
                parseError("Fragmented last entry:" + textLine);
                break; 
            }
            String emptyLine = f.readLine();
            if ((emptyLine==null) || emptyLine.equals("")) {
                parseEntry(dateLine, textLine, statusLine);
            } else { 
                parseError("Expected blank or no line for entry " + textLine);
                break;
            }
        }
    }

    private void printAllPending() {
        pendingEvents.initIter();
        int pending = 0;
        while (true) {
            Object o = pendingEvents.next();
            if (o==null) {
                break;
            }
            Event e = (Event)o;
            pending++;
        }
        Util.wrConsole("Total pending events: " + pending);
    }

    private void processEvents() {
        Date currentDate = Util.currentDate();
        pendingEvents.initIter();
        int pending = 0;
        boolean change = false;
        while (true) {
            Object o = pendingEvents.next();
            if (o==null) {
                break;
            }
            Event e = (Event)o;
            if (e.date.before(currentDate)) {
                pendingEvents.remove(e);
                if (e.status==Event.PENDING) {
                    Util.wrConsole("EVENT TRIGGERED: " + e.message);
                    Util.wrDisplay("EVENT TRIGGERED: " + e.message);
                    displayedEvents.add(e);
                } else if (e.status==Event.ACKED) {
                    acknowledgedEvents.add(e);
                } else {
                    throw new Error("Unknown Event status!");
                }
                change = true;
            } else {
                pending++;
            }
        }
        if (change) {
            Util.wrConsole("Remaining pending events: " + pending);
        }
    }
        
    public Reminder(String fileName) {
        acknowledgedEvents = new List();
        displayedEvents = new List();
        pendingEvents = new List();
        try {
            parseFrom(fileName);
            Util.wrConsole("Parsing completed.\n");
        } catch (IOException e) {
        }
        printAllPending();
        Util.wrConsole("Event watching loop started.\n");
        while (true) {
            processEvents();
            Util.sleep(1);
        }
    }


    public static void main(String[] args) {
        Reminder r = new Reminder("reminder.txt");
    }
}
