/*
 * Created on Mar 4, 2005
 * CHECKED 2
 */

/**
 * Terrain type object for Jame.
 * 
 * Contains the specifications of a terrain type.
 * Instances must be distinctive.
 * 
 * @author aragos
 */
public class JameTerrainType extends JameMapType {
	
	public /*:readonly*/ int movementPoints; // standard movement points on this terrain type
	
	public /*:readonly*/ static JameCollection terrainTypes; /*: public static specvar terrainTypeSet :: objset */
	//: vardefs "terrainTypeSet == if terrainTypes = null then {} else terrainTypes .. JameCollection.collection"
		
	/**
	 * Terrain type constructor 
	 * @param name name of terrain
	 * @param movementPoints standard movement points
	 */
	public JameTerrainType( String newName, int newMovementPoints )
	/*:
	 modifies "JameMapType.name", movementPoints
	 ensures "JameMapType.name = newName & movementPoints = newMovementPoints"  
	 */
	{
		init( newName );
		this.movementPoints = newMovementPoints;
		register( this );		
	}	
	
	/**
	 * Keep track of terrain types.
	 * @param newType type to be registered
	 */
	private static void register( JameTerrainType newType )
	/*:
	 modifies terrainTypeSet
	 ensures "newType : terrainTypeSet"
	 */
	{
		if( terrainTypes == null )
			 terrainTypes = new JameCollection();
	    terrainTypes.add( newType );
	}
	
	public static JameTerrainType getType( String name )
	/*:
	 ensures "result : terrainTypeSet & result..name = name"
	 */
	{	    
	    terrainTypes.resetIter();	    	 
	    while( terrainTypes.hasNext() )
	    {
	        JameTerrainType cType = (JameTerrainType) terrainTypes.next();
	        if( Jame.equals( cType.name , name) )
	        {
	            return cType;
	        }
	    }
	    return null;
	}
}
