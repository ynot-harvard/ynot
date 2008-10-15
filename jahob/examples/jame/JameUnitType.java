/*
 * Created on Mar 4, 2005
 * CHECKED 2
 */

/**
 * Unit type object for Jame.
 * 
 * Contains the specifications of a unit type.
 * 
 * @author aragos
 */
public class JameUnitType extends JameMapType 
{
    public /*:readonly*/ boolean onWater; 	// indicates whether unit type can be on water
    public /*:readonly*/ boolean onLand;	// indicates whether unit type can be on water
    
    public /*:readonly*/ JameResourceSet cost; // collection of resources representing the cost of the unit
    
    public /*:readonly*/ int healthPoints;	// units standard healthpoints    
    public /*:readonly*/ int attack;		// units standard attack
    public /*:readonly*/ int defense;		// units standard defense
    public /*:readonly*/ int movement;		// units standard movement
    
    public /*:readonly*/ JameCollection conditions; /*: public specvar conditionSet :: objset */ // collections of conditions necessary for this unit to be build
    //: vardefs "conditionSet == if conditions = null then {} else conditions .. JameCollection.collection"
    
    public /*:readonly*/ static JameCollection unitTypes; /*: public static specvar unitTypeSet :: objset */
//  //: vardefs "unitTypeSet == if unitTypes = null then {} else unitTypes .. JameCollection.collection"
    
    /**
     * Jame unit type constructor.
     * @param newName types name
     * @param water indicates whether unit can move on water
     * @param land indicates whether unit can move on land
     * @param cond collection of reosurces needed to create unit
     * @param newHealth unit types standard healthpoints
     * @param newAttack unit types standard attack value
     * @param newDefense unit types standard defense value
     * @param newMovement unit types standard movement value
     * @param newView unit types standard view
     */
    public JameUnitType( 	String newName,
            		boolean water, boolean land, JameCollection cond, JameResourceSet newCost, 
            		int newHealth, int newAttack, int newDefense, int newMovement, int newView )
    /*:
     modifies "JameMapType.name", "JameMapType.viewrange",healthPoints, attack, defense, movement, onWater, onLand, conditionSet, cost
     ensures "
     	(this..JameMapType.name = newName) &
     	(this..JameMapType.viewrange = newView) &
     	healthPoints = newHealth &
     	attack = newAttack &
     	defense = newDefense &
     	movement = newMovement &
     	onWater = water &
     	onLand = land &
     	conditionSet = cond..JameCollection.collection &
     	cost = newCost"
     */
    {
        init( newName );
        
        this.onLand = land;
        this.onWater = water;
        this.conditions = cond;
        this.cost = newCost;
        this.healthPoints = newHealth;
        this.attack = newAttack;
        this.defense = newDefense;
        this.movement = newMovement;
        this.viewrange = newView;
        register(this);
    }
    
    /**
	 * Keep track of unit types.
	 * @param newType type to be registered
	 */
	private static void register( JameUnitType newType )
	/*:
	 modifies unitTypeSet
	 ensures "newType : unitTypeSet"
	 */
	{
		if( unitTypes == null )
			 unitTypes = new JameCollection();
	    unitTypes.add( newType );
	}
	
	public static JameUnitType getType( String name )
	/*:
	 ensures "result : unitTypeSet & result..JameMapType.name = name"
	 */
	{
	    unitTypes.resetIter();
	    while( unitTypes.hasNext() )
	    {
	        JameUnitType cType = (JameUnitType) unitTypes.next();
	        String cName = cType.name;
	        if( Jame.equals( cName, name) )
	        {
	            return cType;
	        }
	    }
	    return null;
	}
}
