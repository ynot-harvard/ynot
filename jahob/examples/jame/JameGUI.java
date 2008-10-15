/*import java.awt.Container;
import java.awt.Dimension;
import java.awt.GridLayout;
import java.awt.Font;*/
import java.awt.*;
import java.awt.event.*;

/*import javax.swing.JLabel;
import javax.swing.JTextArea;
import javax.swing.ImageIcon;
import javax.swing.BorderFactory;
import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;
import javax.swing.JLayeredPane;
import javax.swing.JPanel;
import javax.swing.JSplitPane;
import javax.swing.KeyStroke;*/
import javax.swing.*;


public class JameGUI
{

	static final int mapTileX = 32;
	static final int mapTileY = 32;
	static final int mapTileZ = 9;
	static final int mapBuildingZ = 10;
	static final int mapUnitZ = 10;
	static final int setoffX = 5;
	static final int setoffY = 17;
	static final int sidebarWidth = 200;
	static final String imgPath = "images/";
	
	JLayeredPane mapPane;
	JPanel sidePane;
	JTextArea messageBoard;
	JSplitPane contentPane;
	JMenuBar menuBar;
	JameGUIMenuHandler menuHandler;
	JameGUIKeyHandler keyHandler;
	JameGUIBoardElement currentSelected;

	JLabel[][] mapBGTiles;
	JameCollection mapBuildings;
	JameCollection mapUnits;
	JameCollection playerSidebars;
	
	public Container createGameBoard()
	{		
		keyHandler = new JameGUIKeyHandler();
		createMap();
		createSimpleSidebar();
		contentPane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT, mapPane, sidePane );
		contentPane.setDividerLocation(mapTileX * Jame.mapMaxWidth + 11);		
		contentPane.setDividerSize(2);
		contentPane.setOneTouchExpandable(false);
		contentPane.setOpaque(true);
	
	    return contentPane;
	}

	public JMenuBar createMenuBar() 
	{        
	    JMenu menu;
	    JMenuItem menuItem;
	
	    // initialize menu handler
	    menuHandler = new JameGUIMenuHandler();
	    
	    // Create the menu bar.
	    menuBar = new JMenuBar();
	
	    // Build the game menu.
	    menu = new JMenu("Game");
	    menuBar.add(menu);
	
	    menuItem = new JMenuItem("New game");
	    menuItem.addActionListener(menuHandler);
	    menu.add(menuItem);
	    
	    menuItem = new JMenuItem("End turn");
	    menuItem.addActionListener(menuHandler);
	    menuItem.setEnabled(false);
	    menu.add(menuItem);
	    
	    menuItem = new JMenuItem("Start demo");
	    menuItem.addActionListener(menuHandler);
	    menu.add(menuItem);
	    
	    return menuBar;
	}

	public void setGameMode( boolean flag )
	{
		mapBuildings = new JameCollection();
		mapUnits = new JameCollection();
				
		createGameMap();
		createPlayerSidebar();
		// enable "next turn" and actions menu
		menuBar.getMenu(0).getMenuComponent(0).setEnabled(!flag);
		menuBar.getMenu(0).getMenuComponent(1).setEnabled(flag);
		menuBar.getMenu(0).getMenuComponent(2).setEnabled(!flag);
	}

	public void setDemoMode( boolean flag)
	{
		mapBuildings = new JameCollection();
		mapUnits = new JameCollection();
		
		for( int i = 0; i < menuBar.getMenuCount(); ++i )
		{
			menuBar.getMenu(i).setEnabled(!flag);
		}
	}

	public void setMessage( String message )
	{
		messageBoard.setText( message );
		messageBoard.setForeground(Color.BLACK);
	}
	
	public void setWarning( String warning )
	{
		messageBoard.setText( warning );
		messageBoard.setForeground(Color.RED);
	}

	public void setBoardTitle(String title)
	{
		mapPane.setBorder(BorderFactory.createTitledBorder( title ));
	}

	public void updateSidebar()
	{
		JameGUIPlayerSidebar cBar;
		playerSidebars.resetIter();
		while( playerSidebars.hasNext() )
		{
			cBar = (JameGUIPlayerSidebar) playerSidebars.next();
			cBar.refreshContent();
			if( cBar.player == Jame.currentPlayer )
			{
				cBar.setActive(true);
			}
			else
			{
				cBar.setActive(false);
			}
		}
	}

	public void updateBuildings()
	{
		mapBuildings.resetIter();
		while(mapBuildings.hasNext())
		{
			JameGUIBoardElement cElement = (JameGUIBoardElement) mapBuildings.next();
			mapPane.remove( cElement );
			mapBuildings.remove( cElement );
		}
		
		Jame.currentPlayer.buildings.resetIter();
		while( Jame.currentPlayer.buildings.hasNext() )
		{
			JameMapContainer cElement = (JameMapContainer) Jame.currentPlayer.buildings.next();
			addMapElement(  cElement );
		}
	}

	public void updateUnits()
	{
		mapUnits.resetIter();
		while(mapUnits.hasNext())
		{
			JameGUIBoardElement cElement = (JameGUIBoardElement) mapUnits.next();
			mapPane.remove( cElement );
			mapUnits.remove( cElement );
		}
		
		Jame.currentPlayer.units.resetIter();
		while( Jame.currentPlayer.units.hasNext() )
		{
			JameMapContainer cElement = (JameMapContainer) Jame.currentPlayer.units.next();
			addMapElement( cElement );
		}
	}

	public void updateCurrent()
	{
		if( currentSelected != null )
		{
			currentSelected.refreshPosition();
		}
	}

	public void updateViewRange()
	{
		// reset background
		for( int x = JameMap.leftBoundary; x <= JameMap.rightBoundary; ++x )
	    {
	    	for( int y = JameMap.topBoundary; y <= JameMap.bottomBoundary; ++y )
	        {
	    		ImageIcon icon = createImageIcon( "meadow_fog.gif" );        		
	    		mapBGTiles[x-1][y-1].setIcon(icon);
	        }
	    }
		
	
		// remove all previously seen things from map
		mapUnits.resetIter();
		while( mapUnits.hasNext() )
		{
			JameGUIBoardElement cElement = (JameGUIBoardElement) mapUnits.next();
			if( cElement.getData().owner != Jame.currentPlayer )
			{				
				mapPane.remove( cElement );
				mapUnits.remove( cElement );
			}
		}
		
		mapBuildings.resetIter();
		while( mapBuildings.hasNext() )
		{
			JameGUIBoardElement cElement = (JameGUIBoardElement) mapBuildings.next();
			if( cElement.getData().owner != Jame.currentPlayer )
			{
				mapPane.remove( cElement );
				mapBuildings.remove(cElement);
			}
		}
		
		// collect things that are visible to units owned by the current player, but don't belong to the current player or have been collected already
		// also paint every visible field lighter
		
		JameCollection toBeDisplayed = new JameCollection();
		
		JameCollection collection = Jame.currentPlayer.units; 
		collection.resetIter();
		while( collection.hasNext() )
		{
			JameMapContainer cElement = (JameMapContainer) collection.next();
			for( int x = Math.max(JameMap.leftBoundary, cElement.field.xPos - cElement.type.viewrange); x <= Math.min(JameMap.rightBoundary, cElement.field.xPos + cElement.type.viewrange); ++x )
			{
				for( int y = Math.max(JameMap.topBoundary, cElement.field.yPos - cElement.type.viewrange); y <= Math.min(JameMap.bottomBoundary, cElement.field.yPos + cElement.type.viewrange); ++y )
				{
					JameMapContainer cCont = JameMap.getFieldBuilding( JameMap.getField(x, y));
					if( cCont != null && cCont.owner != Jame.currentPlayer && !toBeDisplayed.contains(cCont) )
					{
						toBeDisplayed.add(cCont);
					}
					
					cCont = JameMap.getFieldUnit( JameMap.getField(x, y));
					if( cCont != null && cCont.owner != Jame.currentPlayer && !toBeDisplayed.contains(cCont) )
					{
						toBeDisplayed.add(cCont);
					}
					// make field visible
					ImageIcon icon = createImageIcon( "meadow.gif" );        		
	        		mapBGTiles[x-1][y-1].setIcon(icon);
				}
			}
		}
		
		collection = Jame.currentPlayer.buildings; 
		collection.resetIter();
		while( collection.hasNext() )
		{
			JameMapContainer cElement = (JameMapContainer) collection.next();
			for( int x = Math.max(JameMap.leftBoundary, cElement.field.xPos - cElement.type.viewrange); x <= Math.min(JameMap.rightBoundary, cElement.field.xPos + cElement.type.viewrange); ++x )
			{
				for( int y = Math.max(JameMap.topBoundary, cElement.field.yPos - cElement.type.viewrange); y <= Math.min(JameMap.bottomBoundary, cElement.field.yPos + cElement.type.viewrange); ++y )
				{
					JameMapContainer cCont = JameMap.getFieldBuilding( JameMap.getField(x, y));
					if( cCont != null && cCont.owner != Jame.currentPlayer && !toBeDisplayed.contains(cCont) )
					{
						toBeDisplayed.add(cCont);
					}
					
					cCont = JameMap.getFieldUnit( JameMap.getField(x, y));
					if( cCont != null && cCont.owner != Jame.currentPlayer && !toBeDisplayed.contains(cCont) )
					{
						toBeDisplayed.add(cCont);
					}
					// make field visible
					ImageIcon icon = createImageIcon( "meadow.gif" );        		
	        		mapBGTiles[x-1][y-1].setIcon(icon);
				}
			}
		}
		
		// paint things
		toBeDisplayed.resetIter();
		while( toBeDisplayed.hasNext() )
		{
			addMapElement( (JameMapContainer) toBeDisplayed.next() );
		}
		
	}

	public void addMapElement( JameMapContainer newElement )
	{
		//System.out.println("added " + newElement.getClass().toString());
			
		ImageIcon icon = createImageIcon( newElement.type.name.toLowerCase() + ".gif" );
		JameGUIBoardElement cElement = new JameGUIBoardElement( newElement, icon );
		
		if( newElement instanceof JameBuilding )
		{
			mapPane.add( cElement, new Integer(mapBuildingZ) );
			mapBuildings.add( cElement );
		}
		else if( newElement instanceof JameUnit )
		{
			mapPane.add( cElement, new Integer(mapUnitZ) );
			mapUnits.add( cElement );
		}
	}

	private Container createMap()
	{
		mapPane = new JLayeredPane();
        mapPane.setOpaque(true);
        mapPane.setBorder(BorderFactory.createTitledBorder( "Jame Game Board" ));
        mapPane.setPreferredSize(new Dimension(mapTileX * Jame.mapMaxWidth + 11, mapTileY * Jame.mapMaxHeight));
        mapPane.setFocusable(false);
        currentSelected = null;
        
        mapBGTiles = new JLabel[Jame.mapMaxWidth][Jame.mapMaxHeight];
        
        ImageIcon icon;
		JLabel tile;        
        for( int x = 0; x < Jame.mapMaxWidth; ++x )
        {
        	for( int y = 0; y < Jame.mapMaxHeight; ++y )
            {
        		icon = createImageIcon( "meadow.gif" );
        		tile = new JLabel(icon);
        		tile.setBounds(setoffX + x * mapTileX, setoffY + y * mapTileY, icon.getIconWidth(), icon.getIconHeight());
        		mapPane.add( tile, new Integer(mapTileZ - 1) );
        		mapBGTiles[x][y] = tile;
            }
        }
        return mapPane;
	}
	
	private Container createSimpleSidebar()
	{
		sidePane = new JPanel( new GridLayout(0,1) );
		messageBoard = new JTextArea();
		messageBoard.setBackground(sidePane.getBackground());
		messageBoard.setEditable(false);
		messageBoard.setLineWrap(true);
		messageBoard.setFont(new Font("SansSerif", Font.BOLD, 12));
		messageBoard.setBorder(BorderFactory.createTitledBorder("Jame"));
				
		sidePane.setOpaque(true);
        sidePane.setSize(sidebarWidth, mapTileY * Jame.mapMaxHeight);
        sidePane.add(messageBoard);
        
		return sidePane;
	}
	
	private Container createPlayerSidebar()
	{
		
		sidePane = new JPanel( new GridLayout(0, 1) );
		sidePane.add(messageBoard);
		
		playerSidebars = new JameCollection();
		JameGUIPlayerSidebar bar;
		for( int i = 0; i < Jame.playerNames.length; ++i )
		{
			bar = new JameGUIPlayerSidebar( JamePlayer.getPlayer( Jame.playerNames[i] ));
			sidePane.add(bar);
			playerSidebars.add(bar);
		}
		sidePane.setOpaque(true);
		sidePane.setPreferredSize(new Dimension(sidebarWidth, mapTileY * Jame.mapMaxHeight));		
		
		contentPane.setRightComponent(sidePane);
		contentPane.setDividerLocation(mapTileX * Jame.mapMaxWidth + 11);
		
		return sidePane;
	}
	
	private void createGameMap()
	{
		for( int x = 0; x < JameMap.rightBoundary; ++x )
        {
        	for( int y = 0; y < JameMap.bottomBoundary; ++y )
            {
        		JameTerrain cField = JameMap.getField(x+1, y+1);
        		if( !cField.type.name.equals("Meadow") )
        		{
        			ImageIcon icon = createImageIcon( cField.type.name.toLowerCase() + ".gif" );
        			mapPane.add( new JameGUIBoardElement( cField, icon ), new Integer(mapTileZ) );
        		}
            }
        }
	}
	
	protected static ImageIcon createImageIcon(String path) {
	    java.net.URL imgURL = JameGUI.class.getResource( imgPath + path);
	    if (imgURL != null) {
	        return new ImageIcon(imgURL);
	    } else {
	        System.err.println("Couldn't find file: " + path);
	        return null;
	    }
	}
		
}


