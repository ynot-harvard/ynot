import javax.swing.JFrame;

/*
 * Created on Mar 4, 2005
 */

/**
 * Main class of Jame. Here starts and ends the world.
 * Contains global scope. 
 * 
 * @author aragos
 */
public class Jame {
	
	public static String[] playerNames;
	public static int currentPlayerPosition;
	public static JamePlayer currentPlayer;
	public static JameCollection pendingCommands;
	
	public static final int mapMaxWidth = 15;
	public static final int mapMaxHeight = 15;
	
	public static JameGUI gui;
	public static JameDemo demo;
	
	public static String[] resNames; 
	public static int buildingView;
	
	public static boolean demoMode = false;
	
	public static void main(String[] args) 
	{
		// Schedule a job for the event-dispatching thread:
        // creating and showing jame GUI.
		javax.swing.SwingUtilities.invokeLater(new Runnable() 
		{
            public void run() 
            {
                createAndShowGUI();
            }
        });
	}
	
	public static void createAndShowGUI()
	{
		// Make sure we have nice window decorations.
        JFrame.setDefaultLookAndFeelDecorated(true);

        // Create and set up the window.
        JFrame frame = new JFrame("Jame");
        frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);

        //Create and set up the content pane.
        gui = new JameGUI();
        frame.setJMenuBar(gui.createMenuBar());
        frame.setContentPane(gui.createGameBoard());
        gui.setMessage("This is Jame. Please start the demo.");

        //Display the window.
        frame.setSize( JameGUI.mapTileX * mapMaxWidth + 20 + JameGUI.sidebarWidth, JameGUI.mapTileY * mapMaxHeight + 77 );
        frame.setVisible(true);
	}
	
	public static void createGame( int mapWidth, int mapHeight, String[] players )
	{		
		JameStandardStartup.iniTypes();
		JameStandardStartup.iniMap( mapWidth, mapHeight );
		JameStandardStartup.iniPlayers( players );
		playerNames = players;
		currentPlayerPosition = playerNames.length - 1;
		gui.setGameMode(true);

		nextPlayer();
		
		
		// test
		/*(new JameBuildCommand( Jame.currentPlayer, JameBuildingType.getType("Holdfast"), JameMap.getField(1,1) )).execute();
		(new JamePlaceUnitCommand( Jame.currentPlayer, JameUnitType.getType("Knight"), JameMap.getField(1,2) )).execute();
		nextPlayer();
		(new JameBuildCommand( Jame.currentPlayer, JameBuildingType.getType("Holdfast"), JameMap.getField(Jame.mapMaxWidth, Jame.mapMaxHeight) )).execute();
		(new JamePlaceUnitCommand( Jame.currentPlayer, JameUnitType.getType("Knight"), JameMap.getField(Jame.mapMaxWidth, Jame.mapMaxHeight - 1) )).execute();
		nextPlayer();*/
	}	
	
	public static void nextPlayer()
	{
		currentPlayerPosition = currentPlayerPosition + 1;
		if( currentPlayerPosition == playerNames.length )
			currentPlayerPosition = 0;
		
		currentPlayer = JamePlayer.getPlayer( playerNames[currentPlayerPosition] );
		
		currentPlayer.produceIncome();
		currentPlayer.replenishUnits();
		
		gui.setBoardTitle( currentPlayer.name + " on turn");
		gui.setMessage(currentPlayer.name + " please make your turn." );
		gui.updateUnits();
		gui.updateBuildings();
		gui.updateSidebar();	
		gui.updateViewRange();
	}
	
	public static String fight( JameUnit aggressor, JameUnit defender )
	/*:
	 modifies "JameMap.units..JameCollection.collection", "JameMap.units..JameCollection.free", "JameMap.units..JameCollection.size", 
	 			"aggressor..JameMapContainer.owner..JamePlayer.units..JameCollection.collection", "aggressor..JameMapContainer.owner..JamePlayer.units..JameCollection.free", 
	 			"aggressor..JameMapContainer.owner..JamePlayer.units..JameCollection.size", "defender..JameMapContainer.owner..JamePlayer.units..JameCollection.collection", 
	 			"defender..JameMapContainer.owner..JamePlayer.units..JameCollection.free", "defender..JamePlayer.units..JameCollection.size" 
	 ensures "
	 	JameMap.units..JameCollection.collection <= (old JameMap.units..JameCollection.collection) &
     	( ALL u . u : ((old JameMap.units..JameCollection.collection) - JameMap.units..JameCollection.collection) 
     			--> (u = aggressor | u = defender) )
	 	"     	
	 */
    {
		JameCollection casualities = new JameCollection();
        if( aggressor.attack > defender.defense )
        {
            casualities.add(defender);
        }
        
        if( defender.attack > aggressor.defense )
        {
            casualities.add(aggressor);
        }
        String report = "";
		JameUnit dead;
		casualities.resetIter();
		while( casualities.hasNext() )
		{
			dead = (JameUnit) casualities.next();
			JamePlayer owner = dead.owner;
			JameUnitType type = (JameUnitType)dead.type;
			report = report + "[" +owner.name+ "]" + type.name + ", ";
			JameMap.removeUnit( dead );
            owner.removeUnit( dead );
		}
		return report;
    }	
	
	public static void iniDemo()
	{
		demo = new JameDemo();
		gui.setDemoMode(true);
		gui.setMessage( "This is the demo. Press any key to go on." );
		String[] demoPlayer =  new String[]{"Demo Player 1", "Demo Player 2"};
		createGame( mapMaxWidth , mapMaxHeight, demoPlayer );
		
		JameResourceSet add = new JameResourceSet();
		add.add( new JameResource("Gold", 10000) );
		add.add( new JameResource("Timber", 10000) );
		add.add( new JameResource("Stone", 10000) );
		
		JameCollection player = JamePlayer.player;
		player.resetIter();
		while( player.hasNext() )
		{
			((JamePlayer)player.next()).addResources(add);
		}
		demo.sleep();
	}
	
	public static void commandSuccessful( String message, JameMapContainer newElement )
	{
		if( newElement != null )
		{
			gui.addMapElement( newElement );
			gui.updateSidebar();
		}
		else
		{
			if( !demoMode )
				gui.updateCurrent();
			else
			{
				gui.updateBuildings();
				gui.updateUnits();
			}
		}
		gui.updateViewRange();		
		gui.setMessage( message );
	}
	
	public static void commandFailed( String warning )
	{
		gui.setWarning( warning );
	}
	
	public static void executePendingCommands()
	{
		pendingCommands.resetIter();
		while( pendingCommands.hasNext() )
		{
			((JameCommandContainer)pendingCommands.next()).execute();
		}
	}
	
	/**
     * jahob replacement for equals on strings
     * @param a string	a string
     * @param b string	another string
     * @return 	boolean	are the strings equal?
     */
    public static boolean equals(String a, String b)
    /*:
     ensures "result = (a = b)"
     */
    {
    	return a.equals(b);
    }
}


