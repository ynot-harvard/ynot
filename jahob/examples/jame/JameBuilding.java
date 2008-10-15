/*
 * Created on Mar 4, 2005
 * CHECKED 2
 */

/**
 * Building object for Jame.
 * 
 * Represents a building in Jame.
 * 
 * @author aragos
 */
public class JameBuilding extends JameMapContainer {
	    
    public /*:readonly*/ int attack;		// buildings attack
    public /*:readonly*/ int defense;		// buildings defense
    public /*:readonly*/ int healthPoints;	// buildings healthPoints
        
    /**
     * Jame building constructor.
     * @param type type of building
     * @param field field the building is placed on
     * @param owner buildings owner
     */
	public JameBuilding( JameBuildingType newType, JameTerrain newField, JamePlayer newOwner )
	/*:
	 modifies "this..JameMapContainer.type", "this..JameMapContainer.field", "this..JameMapContainer.owner", attack, defense, healthPoints
	 ensures "
		(this..JameMapContainer.type = newType) &
		(this..JameMapContainer.field = newField) &
		(this..JameMapContainer.owner = newOwner) &
		attack = newType..JameBuildingType.attack &
		defense = newType..JameBuildingType.defense &
		healthPoints = newType..JameBuildingType.healthPoints"
	*/
	{
		init( newType, newField, newOwner );
		this.attack = newType.attack;
	    this.defense = newType.defense;
	    this.healthPoints = newType.healthPoints;
	}
	
	

}
