/*
 * Created on Mar 4, 2005
 * CHECKED 2
 */

/**
 * Terrain object for Jame.
 * 
 * Represents a terrain field within Jame.
 * 
 * @author aragos
 */
public class JameTerrain extends JameMapContainer {
	
	public /*:readonly*/ int xPos; // fields x position on the map
	public /*:readonly*/ int yPos; // fields y position on the map
	public /*:readonly*/ int movementPoints; // points units have to spend to step on the field
		
	/**
	 * constructor
	 * @param type a type of terrain
	 * @param x x coordinate of field
	 * @param y y coordinate of field
	 */
	public JameTerrain( JameTerrainType newType, int x, int y )
	/*: 
	 modifies xPos, yPos, "JameMap.fields..JameCollection.collection", "JameMapContainer.field", "JameMapContainer.type", "JameMapContainer.owner", movementPoints 
	 ensures "
	 	xPos = x & 
	 	yPos = y & 
	 	JameMap.fields..JameCollection.collection = (old JameMap.fields..JameCollection.collection) Un {this} & 
	 	JameMapContainer.field = this &
	 	JameMapContainer.type = newType &
	 	JameMapContainer.owner = null &
	 	movementPoints = newType..JameTerrainType.movementPoints"
	 */
	{
		init( newType, null, null );
		assignField( this );
		this.xPos = x;
		this.yPos = y;
		this.movementPoints = newType.movementPoints;
		JameMap.addField( this );				
	}
	
	/**
	 * Sets coordinates
	 * @param x new x coordinate
	 * @param y new y coordinate
	 */
	void assignCoordinates( int x, int y)
	/*:
	 modifies xPos, yPos
	 ensures "xPos = x & yPos = y"
	 */
	{
		this.xPos = x;
		this.yPos = y;
	}
}
