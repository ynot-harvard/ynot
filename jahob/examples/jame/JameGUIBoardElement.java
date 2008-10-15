
import java.awt.event.FocusAdapter;
import java.awt.event.FocusEvent;
import java.awt.event.FocusListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.awt.Color;

import javax.swing.BorderFactory;
import javax.swing.JComponent;
import javax.swing.JLabel;
import javax.swing.ImageIcon;

public class JameGUIBoardElement extends JLabel{
	
	private JameMapContainer dataObj;
	private ImageIcon icon;
	
	public JameGUIBoardElement( JameMapContainer dataObj, ImageIcon icon )
	{		
		super(icon);
		this.dataObj = dataObj;
		this.icon = icon;
		this.setBounds(JameGUI.setoffX + (dataObj.field.xPos - 1) * icon.getIconWidth(), JameGUI.setoffY + (dataObj.field.yPos - 1) * icon.getIconHeight(), icon.getIconWidth(), icon.getIconHeight());
		
		MouseListener getFocus = new MouseAdapter()
		{
			public void mouseClicked( MouseEvent e )
			{
				//System.out.println("clicked");
				((JComponent)e.getSource()).requestFocusInWindow();
			}
		};
			
		FocusListener registerCurrent = new FocusAdapter()
		{
			public void focusGained(FocusEvent e)
			{
				//System.out.println("we got it");
				JameGUIBoardElement cComp = (JameGUIBoardElement) e.getComponent();
				Jame.gui.currentSelected = (JameGUIBoardElement) e.getComponent();
				cComp.setBorder(BorderFactory.createLineBorder(Color.DARK_GRAY));
			}
			public void focusLost(FocusEvent e)
			{
				JameGUIBoardElement cComp = (JameGUIBoardElement) e.getComponent();
				cComp.setBorder(BorderFactory.createEmptyBorder());
				//System.out.println("we lost it");
			}
		};
				
		setEnabled(true);
		setFocusable(true);
		addFocusListener(registerCurrent);
		addMouseListener(getFocus);
		addKeyListener(Jame.gui.keyHandler);
	}
	
	public JameMapContainer getData()
	{
		return this.dataObj;
	}
	
	public void refreshPosition()
	{
		this.setLocation(JameGUI.setoffX + (dataObj.field.xPos - 1) * icon.getIconWidth(), JameGUI.setoffY + (dataObj.field.yPos - 1) * icon.getIconHeight());
	}

}
