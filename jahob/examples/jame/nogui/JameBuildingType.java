/*
 * Created on Mar 4, 2005
 * CHECKED 2
 */

/**
 * Building type object for Jame.
 * 
 * Contains the specifications of a building type.
 * 
 * @author aragos
 */
public class JameBuildingType extends JameMapType {
	
    public /*:readonly*/ boolean onWater;		// indicates whether building type can be build on water
    public /*:readonly*/ boolean onLand;		// indicates whether building type can be build on land
    	
    public /*:readonly*/ JameResourceSet cost;	// cost as a collection of resources  
    public /*:readonly*/ JameResourceSet prod;	// production as a collection of resources
    	
    public /*:readonly*/ int unitSlots;			// units building type supports
    public /*:readonly*/ int buildSlots;		// building building type supports
    
    public /*:readonly*/ int attack;			// buildings standard attack value
    public /*:readonly*/ int defense;			// buildings standard defense value
    public /*:readonly*/ int healthPoints;		// buildings standard health
    
    public /*:readonly*/ JameCollection conditions; /*: public specvar conditionSet :: objset */ 	// conditions necessary to build building of this type
    //: vardefs "conditionSet == if conditions = null then {} else conditions .. JameCollection.collection"
    
    public /*:readonly*/ static JameCollection buildingTypes; /*: public static specvar buildingTypeSet :: objset */
    //: vardefs "buildingTypeSet == if buildingTypes = null then {} else buildingTypes .. JameCollection.collection"
        
    /**
     * Jame building type constructor.
     * @param newName types name 
     * @param water indicates whether buildings vcan be build on water
     * @param land indicates whether building can be build on land
     * @param costSet collection of resources needed to build the building
     * @param prodSet collections of resources the building produces per turn
     * @param newUnitSlots number of units the building supports
     * @param newBuildSlots number of buildings the building supports
     * @param newAttack buildings standard attack value
     * @param newDefense buildings standard defense value
     * @param newHealth buildings standard health
     * @param cond collection of conditions needed to be fulfilled for building
     */
	public JameBuildingType( 	String newName,
	        			boolean water, boolean land,
	        			JameResourceSet costSet, JameResourceSet prodSet,
	        			int newUnitSlots, int newBuildSlots,
	        			int newAttack, int newDefense, int newHealth,
	        			JameCollection cond )
	    /*:
	     modifies "JameMapType.name", "JameMapType.viewrange", onWater, onLand, cost, prod, unitSlots, buildSlots, attack, defense, healthPoints, conditionSet
	     ensures "
	     	(this..JameMapType.name = newName) &	     	
	     	onWater = water &
	     	onLand = land &
	     	cost = costSet &
	     	prod = prodSet &
	     	unitSlots = newUnitSlots &
	     	buildSlots = newBuildSlots &
	     	attack = newAttack &
	     	defense = newDefense &
	     	healthPoints = newHealth &
	     	conditionSet = cond..JameCollection.collection &
	     	JameMapType.viewrange = Jame.buildingView"
	     */
	    {
	    init( newName );
	    this.onWater = water;
	    this.onLand = land;
	    this.cost = costSet;
	    this.prod = prodSet;
	    this.unitSlots = newUnitSlots;
	    this.buildSlots = newBuildSlots;
	    this.attack = newAttack;
	    this.defense = newDefense;
	    this.conditions = cond;
	    this.healthPoints = newHealth;
	    this.viewrange = Jame.buildingView;
	    
	    register( this );
	}
	
	/**
	 * Keep track of building types.
	 * @param newType type to be registered
	 */
	private static void register( JameBuildingType newType )
	/*:
	 modifies buildingTypeSet
	 ensures "newType : buildingTypeSet"
	 */
	{
		if( buildingTypes == null )
			buildingTypes = new JameCollection();
	    buildingTypes.add( newType );
	}
	
	public static JameBuildingType getType( String name )
	/*:
	 ensures "result : buildingTypeSet & result..JameMapType.name = name"
	 */
	{
	    buildingTypes.resetIter();
	    while( buildingTypes.hasNext() )
	    {
	        JameBuildingType cType = (JameBuildingType) buildingTypes.next();
	        String cName = cType.name;
	        if( Jame.equals(cName, name) )
	        {
	            return cType;
	        }
	    }
	    return null;
	}
	
}
