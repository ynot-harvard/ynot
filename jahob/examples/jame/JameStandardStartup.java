/*
 * Created on Mar 9, 2005
 */

//import java.util.Random;

/**
 * Jame startup action.
 * 
 * Runs all processes necessary to run the game:
 * 	* initialises types (buildings, units, terrain)
 * 	* initialises map (fields)
 *  * initialises players
 *  * initialises current game data (units, fields, buildings, resources, etc.pp.) 
 * 
 * @author aragos 
 */
public class JameStandardStartup
{    
    public static void iniTypes()
    {
    	JameResourceSet cost;
    	JameResourceSet prod;
    	JameCollection cond;
    	
    	// set global information
    	Jame.resNames = new String[]{ "Gold", "Timber", "Stone" };
    	Jame.buildingView = 2;
    	
    	// create terrain types
    	new JameTerrainType( "Meadow", 1 );
    	new JameTerrainType( "Wood", 2 );
    	new JameTerrainType( "Mountain", 3 );
    	
    	// create researches
    	cost = new JameResourceSet(); prod = new JameResourceSet(); 
    	cost.add( new JameResource("Stone", 100) ); cost.add( new JameResource("Timber", 50) );
    	JameResearch wheel = new JameResearch( "Wheel", cost, new JameCollection() );
    	
    	// create building types
    	cost = new JameResourceSet(); prod = new JameResourceSet();
    	cost.add( new JameResource("Stone", 100) ); cost.add( new JameResource("Timber", 50) );
    	prod.add( new JameResource("Gold", 20) );
    	new JameBuildingType( "Holdfast", false, true, cost, prod, 10, 10, 100, 100, 100, new JameCollection() );
    	
    	cost = new JameResourceSet(); prod = new JameResourceSet();
    	cost.add( new JameResource("Timber", 10) );
    	prod.add( new JameResource("Timber", 10) );
    	new JameBuildingType( "Lumberjack", false, true, cost, prod, 0, 0, 10, 10, 10, new JameCollection() );
    	
    	// create unit types
    	cost = new JameResourceSet(); cond = new JameCollection();
    	cost.add( new JameResource("Gold", 30) ); cost.add( new JameResource("Timber", 10) );
    	new JameUnitType( "Knight", false, true, cond, cost, 50, 10, 5, 5, 3 );  
    	
    	cost = new JameResourceSet(); cond = new JameCollection();
    	cost.add( new JameResource("Gold", 10) ); cost.add( new JameResource("Timber", 50) );
    	cond.add( wheel );
    	new JameUnitType( "Ballista", false, true, cond, cost, 30, 10, 20, 3, 1 );  
    }
    
    public static void iniMap( int width, int height )
    {
    	//String[] tTypes = new String[]{ "Meadow", "Wood", "Mountain" };
    	//Random rand = new Random();
    	JameMap.initialise( new JameCollection(), new JameCollection(), new JameCollection(), 1,width,height,1 );
        for( int y = 1; y <= height; y = y + 1 )
        {
            for( int x = 1; x <= width; x = x + 1 )
            {
                //new JameTerrain( JameTerrainType.getType(tTypes[rand.nextInt(3)]), x, y );
            	if( x > 6 && x < 10)
            	{
            		new JameTerrain( JameTerrainType.getType("Wood"), x, y );
            	}
            	else if( y > 6 && y < 10 )
            	{
            		new JameTerrain( JameTerrainType.getType("Mountain"), x, y );
            	}
            	else
            	{
            		new JameTerrain( JameTerrainType.getType("Meadow"), x, y );
            	}
            }
        }                
    }
    
    public static void iniPlayers( String[] players )
    {
    	JameResourceSet startRes = new JameResourceSet();
    	startRes.add( new JameResource("Gold", 100) ); startRes.add( new JameResource("Timber", 100) ); startRes.add( new JameResource("Stone", 100) );
    	for( int i = 0; i < players.length; i = i + 1 )
    	{
    		new JamePlayer( players[i], new JameCollection(), new JameCollection(), new JameCollection(), startRes.copy() );
    	}
    }
}


