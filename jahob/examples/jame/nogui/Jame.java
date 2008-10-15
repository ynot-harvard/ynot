
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
	
	public static String[] resNames; 
	public static int buildingView;
	
	public static boolean demoMode = false;
	
	public static void main(String[] args) 
	{
	}
	
	public static void createAndShowGUI()
	{
	}	
	
	public static void nextPlayer()
	{
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
	}
	
	public static void commandSuccessful( String message, JameMapContainer newElement )
	{
	}
	
	public static void commandFailed( String warning )
	{
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
