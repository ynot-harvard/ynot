import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;
//import javax.swing.Action;
//import java.awt.event.ActionEvent;
//import java.awt.event.ActionListener;

public class JameGUIKeyHandler implements KeyListener
{
	public void keyTyped(KeyEvent e) 
	{
    }
	
	public void keyReleased(KeyEvent e) 
	{
    }
	
	public void keyPressed(KeyEvent e) 
	{
		int keyCode = e.getKeyCode();
        //System.out.println( KeyEvent.getKeyText(keyCode) + "::" + keyCode );
		
		// move unit
		if( e.getSource() instanceof JameGUIBoardElement && ((JameGUIBoardElement)e.getSource()).getData() instanceof JameUnit )
		{
			JameUnit unit = (JameUnit) ((JameGUIBoardElement)e.getSource()).getData();
			int x = unit.field.xPos;
			int y = unit.field.yPos;
		
			if( KeyEvent.getKeyText(keyCode) == "Left" )
				x--;
			else if( KeyEvent.getKeyText(keyCode) == "Up" )
				y--;
			else if( KeyEvent.getKeyText(keyCode) == "Right" )
				x++;
			else if( KeyEvent.getKeyText(keyCode) == "Down" )
				y++;
			else
				return;
			
			JameCommandContainer com = new JameMoveUnitCommand( Jame.currentPlayer, unit, unit.field, JameMap.getField(x, y) );			
			com.execute();
			return;
		}
    }
}
