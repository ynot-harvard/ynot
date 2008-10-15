
import java.awt.Dimension;
import java.awt.Color;

import javax.swing.BoxLayout;
import javax.swing.JLabel;
import javax.swing.ImageIcon;
import javax.swing.BorderFactory;
import javax.swing.JPanel;

public class JameGUIPlayerSidebar extends JPanel 
{
	public JamePlayer player;	
	
	JameGUIPlayerSidebar( JamePlayer player )
	{
		this.player = player;
		setLayout(new BoxLayout(this, BoxLayout.PAGE_AXIS));
        setOpaque(true);
        setBorder(BorderFactory.createTitledBorder(player.name));
        setPreferredSize(new Dimension(JameGUI.sidebarWidth, JameGUI.mapTileY * Jame.mapMaxHeight));
	}
	
	public void refreshContent()
	{
		this.removeAll();
		JLabel cComp;
		ImageIcon icon;
		for( int i = 0; i < Jame.resNames.length; ++i )
		{
			JameResource cRes = player.resStore.get( Jame.resNames[i] );
			icon = JameGUI.createImageIcon( cRes.name.toLowerCase() + ".gif");			
			cComp = new JLabel( Integer.toString( cRes.value ), icon, JLabel.LEFT);
			cComp.setMaximumSize( new Dimension(JameGUI.sidebarWidth, icon.getIconHeight() + 5));
			add( cComp );
		}
		updateUI();
	}
	
	public void setActive( boolean flag )
	{
		if( flag )
		{
			setBorder(BorderFactory.createTitledBorder(BorderFactory.createLineBorder(Color.black, 2),player.name));
		}
		else
		{
			setBorder(BorderFactory.createTitledBorder(player.name));
		}
	}
}
