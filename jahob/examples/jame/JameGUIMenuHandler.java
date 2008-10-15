import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.ItemEvent;
import java.awt.event.ItemListener;

import javax.swing.JMenuItem;

public class JameGUIMenuHandler implements ActionListener, ItemListener 
{
	public void actionPerformed(ActionEvent e) {
        JMenuItem source = (JMenuItem)(e.getSource());
        String event = source.getText();
        
        
        if( event.equalsIgnoreCase( "New game" ) )
        {
        	Jame.createGame(Jame.mapMaxWidth, Jame.mapMaxHeight, new String[]{"Player1", "Player2"} );
        }
        else if( event.equalsIgnoreCase( "End turn" ) )
        {
        	Jame.nextPlayer();
        }
        else if( event.equalsIgnoreCase( "Start demo" ) )
        {
        	Jame.demoMode = true;
        	Jame.iniDemo();
        }
    }

	public void itemStateChanged(ItemEvent e) 
    {
    	
    }
}
