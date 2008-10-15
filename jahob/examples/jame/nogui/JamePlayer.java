/*
 * Created on Mar 4, 2005
 * CHECKED 2
 */

/**
 * Player object for Jame.
 * 
 * Contains a unit of all the buildings and units which belong to a single player.
 * 
 * @author aragos
 */
public class JamePlayer {

	public /*:readonly*/ JameCollection units;			/* public specvar playerUnitSet :: objset */		// units belonging to the player
	// vardefs "playerUnitSet == if units = null then {} else units .. JameCollection.collection"
	public /*:readonly*/ JameCollection buildings;		/* public specvar playerBuildingSet :: objset */	// buildings belonging to the player
	// vardefs "playerBuildingSet == if buildings = null then {} else buildings .. JameCollection.collection"
	public /*:readonly*/ JameCollection research;		/* public specvar playerResearchSet :: objset */	// collection of researches finished by player
	// vardefs "playerResearchSet == if research = null then {} else research .. JameCollection.collection"	
	
	public /*:readonly*/ JameResourceSet resStore;		// player resource storage
	
	public /*:readonly*/ String name;					// players name
	
	public /*:readonly*/ static JameCollection player; 	/* public static specvar playerSet :: objset */
	// "player .. JameCollection.collection == if player = null then {} else player .. JameCollection.collection"
	
	//: inv "player ~= null --> (ALL p . p : player..JameCollection.collection --> p ~= null & p : JamePlayer)"
	
	// inv "units ~= null --> (ALL u . u : units..JameCollection.collection --> u ~= null & u : JameUnit)"
	// inv "buildings ~= null --> (ALL b . b : buildings..JameCollection.collection --> b ~= null & b : JameBuilding)"
	// inv "research ~= null --> (ALL r . r : research..JameCollection.collection --> r ~= null & r : JameResearch)"
	// & (units ~= null --> (ALL u . u : units..JameCollection.collection --> u ~= null & u : JameUnit)) & (buildings ~= null --> (ALL b . b : buildings..JameCollection.collection --> b ~= null & b : JameBuilding)) & (research ~= null --> (ALL r . r : research..JameCollection.collection --> r ~= null & r : JameResearch))
	
	/**
	 * Jame player constructor.
	 * @param newName players name
	 * @param newUnits players units
	 * @param newBuildings players buildings
	 * @param newResearch researches done by the player
	 * @param resources players resources
	 */
	public JamePlayer( String newName, JameCollection newUnits, JameCollection newBuildings, 
	        	JameCollection newResearch, JameResourceSet resources )
	/*:
	 modifies player, units, buildings, research, resStore, name, "JameCollection.collection", "JameResourceSet.resSet"
	 ensures "
	 	units = newUnits&
	 	buildings = newBuildings &
	 	research = newResearch &
	 	resStore = resources &
	 	name = newName &
	 	this : player..JameCollection.collection"
	 */
	{		
		this.units = newUnits;
		this.buildings = newBuildings;
		this.research = newResearch;
		this.resStore = resources;
		this.name = newName;		
		register( this );
	}
	
	/**
	 * Set a new name for player.
	 * @param newName players new name
	 */
	public void setName( String newName )
	/*:	 
	 modifies name
	 ensures "name = newName"
	 */
	{
	    this.name = newName;
	}
	
	/**
	 * Add resources to players resource storage
	 * @param addRes additional resources
	 * @return the resulting storage
	 */
	public void addResources( JameResourceSet addRes )
	/*:
	 requires"addRes ~= null & resStore ~= null"	 
	 modifies "JameResourceSet.resSet"
	 ensures "(resStore.. JameResourceSet.resSet = 
     			{ r .	( EX y n . y : (old (resStore..JameResourceSet.resSet)) & (n : addRes..JameResourceSet.resSet) & fst n = fst y & fst r = fst y & snd r = (snd y) + (snd n) ) |
     					( EX y n . y : (old (resStore..JameResourceSet.resSet)) & (n ~: addRes..JameResourceSet.resSet) & fst n = fst y & fst r = fst y & snd r = snd y ) |
     					( EX y n . y ~: (old (resStore..JameResourceSet.resSet)) & (n : addRes..JameResourceSet.resSet) & fst n = fst y & fst r = fst n & snd r = snd n )
     			})"
    */
	{
	    resStore.addSet( addRes );
	}
	
	/**
	 * Substract resources from players resource storage
	 * @param subRes resources to be substracted
	 * @return the resulting storage
	 * TODO ensures clause (see jameresoureceset)
	 */
	public JameResourceSet subResources( JameResourceSet subRes )
	/*:
	  requires"subRes ~= null & resStore ~= null"	 
	  modifies "JameResourceSet.resSet"
	  ensures "(resStore.. JameResourceSet.resSet = 
     			{ r .	( EX y n . y : (old (resStore..JameResourceSet.resSet)) & (n : subRes..JameResourceSet.resSet) & fst n = fst y & fst r = fst y & snd r = (snd y) - (snd n) ) |
     					( EX y n . y : (old (resStore..JameResourceSet.resSet)) & (n ~: subRes..JameResourceSet.resSet) & fst n = fst y & fst r = fst y & snd r = snd y ) |
     					( EX y n . y ~: (old (resStore..JameResourceSet.resSet)) & (n : subRes..JameResourceSet.resSet) & fst n = fst y & fst r = fst n & snd r = snd n )
     			})"
     */
	{
	    return this.resStore.substractSet( subRes );
	}
	
	/**
     * Assign building to player.
     * @param building building to be added
     */
    public void addBuilding( JameBuilding building )
    /*:
     requires 	"buildings ~= null & building ~= null"
     modifies 	"this..JamePlayer.buildings..JameCollection.collection", "this..JamePlayer.buildings..JameCollection.free", "this..JamePlayer.buildings..JameCollection.size", "building..JameMapContainer.owner"
     ensures	"(buildings..JameCollection.collection = (old buildings..JameCollection.collection) Un {building}) & building..JameMapContainer.owner = this" 
     */
    {
        if( !buildings.contains( building ) )
        {
            buildings.add( building );
        }
        building.assignOwner( this );
    }
    
    /**
     * Assign unit to player.
     * @param unit unit to be added
     */
    public void addUnit( JameUnit newUnit )
    /*:
     requires "units ~= null & newUnit ~= null" 
     modifies "JameCollection.collection", "JameMapContainer.owner"
     ensures "newUnit : units .. JameCollection.collection & newUnit..JameMapContainer.owner = this" 
     */
    {
        if( !units.contains( newUnit ) )
        {
            units.add( newUnit );
        }
        newUnit.assignOwner( this );
    }
    
    /**
     * Add research to player.
     * @param research research to be added
     */
    public void addResearch( JameResearch newResearch )
    /*: 
     requires "research ~= null & newResearch ~= null"
     modifies "JameCollection.collection"
     ensures "newResearch : research .. JameCollection.collection" 
     */
    {
        if( !research.contains( newResearch ) )
        {
            research.add( newResearch );
        }
    }
    
    /**
     * Removes a unit from players ownership. 
     * @param unit unit to be removed
     */
    public void removeUnit( JameUnit removedUnit )
    /*:
     requires "units ~= null & removedUnit ~= null & this ~= null"
     modifies "JameCollection.collection", "JameMapContainer.owner"
     ensures "removedUnit ~: units .. JameCollection.collection & removedUnit..JameMapContainer.owner ~= this"   
     */
    {
        units.remove( removedUnit );
        removedUnit.assignOwner( null );
    }
    
    /**
     * Removes a building from players ownership.
     * @param building building to be removed
     */
    public void removeBuilding( JameBuilding building ) // uses superclass call in building
    /*: 
     requires "buildings ~= null & building ~= null & this ~= null"
     modifies "JameCollection.collection", "JameMapContainer.owner"
     ensures "building ~: buildings .. JameCollection.collection & building..JameMapContainer.owner ~= this"  
     */
    {
        buildings.remove( building );
        building.assignOwner( null );
    }
    
    public void produceIncome()
    /*:
     requires "buildings ~= null & resStore ~= null"
     modifies "JameResourceSet.resSet", "JameCollection.free"
     ensures "ALL build . build : buildings..JameCollection.collection & build .. JameMapContainer.type .. JameBuildingType.prod..JameResourceSet.resSet ~= {} -->
     			resStore.. JameResourceSet.resSet = 
     			{ x .	( EX y n . y : (old resStore..JameResourceSet.resSet) & (n : build..JameMapContainer.type..JameBuildingType.prod..JameResourceSet.resSet) & fst n = fst y & fst x = fst y & snd x = (snd y) + (snd n) ) |
     					( EX y n . y : (old resStore..JameResourceSet.resSet) & (n ~: build..JameMapContainer.type..JameBuildingType.prod..JameResourceSet.resSet) & fst n = fst y & fst x = fst y & snd x = snd y ) |
     					( EX y n . y ~: (old resStore..JameResourceSet.resSet) & (n : build..JameMapContainer.type..JameBuildingType.prod..JameResourceSet.resSet) & fst n = fst y & fst x = fst n & snd x = snd n )
     			}"
     */
    {
    	buildings.resetIter();
    	while
    	/*: inv
    	 "(ALL build . build : ( buildings..JameCollection.collection - buildings..JameCollection.free ) & build .. JameMapContainer.type .. JameBuildingType.prod..JameResourceSet.resSet ~= {} -->
    	 		resStore.. JameResourceSet.resSet = 
     			{ x .	( EX y n . y : (old resStore..JameResourceSet.resSet) & (n : build..JameMapContainer.type..JameBuildingType.prod..JameResourceSet.resSet) & fst n = fst y & fst x = fst y & snd x = (snd y) + (snd n) ) |
     					( EX y n . y : (old resStore..JameResourceSet.resSet) & (n ~: build..JameMapContainer.type..JameBuildingType.prod..JameResourceSet.resSet) & fst n = fst y & fst x = fst y & snd x = snd y ) |
     					( EX y n . y ~: (old resStore..JameResourceSet.resSet) & (n : build..JameMapContainer.type..JameBuildingType.prod..JameResourceSet.resSet) & fst n = fst y & fst x = fst n & snd x = snd n )
     			})  & (player ~= null --> (ALL p . p : player..JameCollection.collection --> p ~= null & p : JamePlayer)) & buildings ~= null & resStore ~= null" */
    	(buildings.hasNext())
    	{
    		/*: assume "ALL x . x : buildings .. JameCollection.collection -->
    		x ~= null & x : JameBuilding &  
            x..JameMapContainer.type ~= null & x..JameMapContainer.type : JameBuildingType &
            x..JameMapContainer.type..JameBuildingType.prod ~= null" */
    		resStore.addSet(((JameBuildingType)((JameBuilding)buildings.next()).type).prod);
    	}
    }
    
    public void replenishUnits()
    /*:
     requires "units ~= null"     
     modifies "JameUnit.movement", "JameCollection.free"
     ensures "(ALL x . x : units..JameCollection.collection --> x .. JameUnit.movement = x .. JameMapContainer.type .. JameUnitType.movement)"
     */
    {
    	units.resetIter();
    	while 
    	/*: inv "(ALL x . x : (units..JameCollection.collection - units..JameCollection.free ) --> x .. JameUnit.movement = x .. JameMapContainer.type .. JameUnitType.movement) & units ~= null & 
    	 		 (player ~= null --> (ALL p . p : player..JameCollection.collection --> p ~= null & p : JamePlayer))"    	 
    	 */
    	(units.hasNext())
    	{
    		/*: assume "ALL x . x : units .. JameCollection.collection -->  
    		x ~= null & x : JameUnit &           
            x..JameMapContainer.type ~= null & x..JameMapContainer.type : JameUnitType" */
    		JameUnit cUnit = (JameUnit) units.next();
    		cUnit.movement = ((JameUnitType)cUnit.type).movement;
    	}
    }
    
    /**
	 * Keep track of players.
	 * @param newPlayer player to be registered
	 */
	private void register( JamePlayer newPlayer )
	/*:	 
	 requires "newPlayer ~= null & newPlayer : JamePlayer" 
	 modifies "JameCollection.collection"
	 ensures "player..JameCollection.collection = old (player .. JameCollection.collection) Un {newPlayer}"
	 */
	{
		if( player == null )
		{
			player = new JameCollection();
		}
	    player.add( newPlayer );
	}
	
	public static JamePlayer getPlayer( String name )
	/*:
	 requires "name ~= null & player ~= null"
     modifies "JameCollection.free"
     ensures "(result = null & (ALL x . x : player..JameCollection.collection --> x..JamePlayer.name ~= name)) |
              ((result .. JamePlayer.name = name) & 
               (result : player..JameCollection.collection))"
	 */
	{	    
	    player.resetIter();
	    while /*: inv "	(ALL x. (x : player..JameCollection.collection - player..JameCollection.free) 
            				--> x..JamePlayer.name ~= name) &
            		    (ALL x . x : player .. JameCollection.collection 
            		    	--> x ~= null & x : JamePlayer) &
            		    player ~= null" */
	    ( player.hasNext() )
	    {
	        JamePlayer cPlayer = (JamePlayer) player.next();
	        if( Jame.equals( cPlayer.name, name) )
	        {
	            return cPlayer;
	        }
	    }
	    return null;
	}
}

