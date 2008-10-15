/*
 * Created on Mar 4, 2005
 * CHECKED 2
 */
/**
 * Unit object for Jame.
 * 
 * Represents a unit in Jame.
 * 
 * @author aragos
 */
public class JameUnit extends JameMapContainer{

    public int healthPoints;	// units standard healthpoints    
    public /*:readonly*/ int attack;		// units standard attack
    public /*:readonly*/ int defense;		// units standard defense
    public int movement;		// units standard movement
    
    /**
     * Jame unit contructor.
     * @param newType units type
     * @param newField field unit is placed on
     * @param newOwner units owner
     */
	public JameUnit( JameUnitType newType, JameTerrain newField, JamePlayer newOwner )
	/*:
	 modifies "JameMapContainer.type", "JameMapContainer.field", "JameMapContainer.owner", healthPoints, attack, defense, movement 
	 ensures "
		(this..JameMapContainer.type = newType) &
		(this..JameMapContainer.field = newField) &
		(this..JameMapContainer.owner = newOwner) &
		healthPoints = newType..JameUnitType.healthPoints &
		attack = newType..JameUnitType.attack &
		defense = newType..JameUnitType.defense &
		movement = newType..JameUnitType.movement"
	*/
	{
		init( newType, newField, newOwner );
		this.healthPoints = newType.healthPoints;
        this.attack = newType.attack;
        this.defense = newType.defense;
        this.movement = newType.movement;
	}
	
	/**
	 * Reduce units health.
	 * @param subHealth healthpoints to be substracted
	 * @return new health status
	 */
	public int reduceHealth( int subHealth )
	/*:
	 modifies healthPoints
	 ensures "healthPoints = old healthPoints - subHealth & result = healthPoints"
	 */
	{
	    healthPoints = healthPoints - subHealth;
	    return healthPoints;
	}
	
	/**
	 * Restore units health up to max.
	 * @param additionalHealth healthpoints to be added
	 * @return new health status
	 */
	public int restoreHealth( int additionalHealth )
	/*:
	 modifies healthPoints
	 ensures "	(healthPoints = old healthPoints + additionalHealth) & (healthPoints <= (this..JameMapContainer.type..JameUnitType.healthPoints)) & 
	 			(result = healthPoints)"
	 */
	{
	    
	    this.healthPoints = healthPoints + additionalHealth;
	    if( this.healthPoints > ( (JameUnitType) this.type ).healthPoints )
	        this.healthPoints = ( (JameUnitType) this.type ).healthPoints;
	    return this.healthPoints;
	}
}
