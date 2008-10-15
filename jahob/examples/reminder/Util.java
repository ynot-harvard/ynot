import javax.swing.*;        
import java.util.*;

public final class Util {
    public static void sleep(long seconds) {
        try {
            Object o = new Object();
            synchronized (o) { 
                o.wait(seconds * 1000); 
            }
        } catch (InterruptedException e) {
        }
    }

    public static void wrConsole(String msg) {
        System.out.println(msg);
    }

    public static void wrDisplay(String message) {
        //Create and set up the window.
        JFrame frame = new JFrame(message);
        frame.setDefaultCloseOperation(JFrame.DISPOSE_ON_CLOSE);

        //Add the label.
        JLabel label = new JLabel(message);
        frame.getContentPane().add(label);

        //Display the window.
        frame.pack();
        frame.setVisible(true);
    }

    public static long currentTimeSec() {
        return System.currentTimeMillis() / 1000;
    }

    public static Date currentDate() {
        Calendar c = Calendar.getInstance();
        return c.getTime();        
    }

    public static void main(String[] args) {
        for (int i = 0; i<4; i++) {
            wrDisplay("Current time: " + currentTimeSec());
            sleep(1);
        }
        wrConsole("Done counting!");
    }
}
