/*
 * Created on Mar 4, 2005
 * CHECKED 2
 */


/**
 * Static map object for Jame. 
 * Must be initialised by calling initialise() before first use.
 * Contains a list of all fields in the map, as well as a list of units and one of buildings.
 *  
 * @author aragos
 */
public class JameMap {
    	
    public /*:readonly*/ static boolean initialised = false;	// indicates map initilisation status
    
    public /*:readonly*/ static JameCollection fields;			// collection of all fields on map
    public /*:readonly*/ static JameCollection units;			// collection of all units on map
    public /*:readonly*/ static JameCollection buildings;		// collection of all buildings on map
    public /*:readonly*/ static int topBoundary;				// top map boundary
    public /*:readonly*/ static int rightBoundary;				// right map boundary
    public /*:readonly*/ static int bottomBoundary;				// bottom map boundary
    public /*:readonly*/ static int leftBoundary;				// left map boundary
    
    /*: inv "initialised -->
     		( units ~= null &
     		  buildings ~= null &
     		  fields ~= null )"     
     */
    /* 
     inv "initialised & ( ALL u.u : units..JameCollection.collection --> ( u..JameMapContainer.owner : JamePlayer.player | u..JameMapContainer.owner )"
     */
    /*
     inv "initialised & ( ALL b.b : buildings..JameCollection.collection --> ( u..JameMapContainer.owner : JamePlayer.player | u..JameMapContainer.owner )"
     */
    
    
    /**
     * Initialise the map.
     * @param newFields	list of terrain fields
     * @param newUnits	list of units
     * @param newBuildings list of buildings
     * @param newTopBoundary value of top boundary of the map
     * @param newRightBoundary value of top boundary of the map
     * @param newBottomBoundary value of top boundary of the map
     * @param newLeftBoundary value of top boundary of the map
     */
    public static void initialise( 	JameCollection newFields, JameCollection newUnits, JameCollection newBuildings, 
            						int newTopBoundary, int newRightBoundary, int newBottomBoundary, int newLeftBoundary )
    /*:
     requires "newFields ~= null & newUnits ~= null & newBuildings ~= null"
     modifies "JameCollection.collection", initialised, units, fields, buildings, topBoundary, bottomBoundary, leftBoundary, rightBoundary
     ensures 
     "fields = newFields &
     units = newUnits &
     buildings = newBuildings &
     topBoundary = newTopBoundary &
     rightBoundary = newRightBoundary &
     bottomBoundary = newBottomBoundary &
     leftBoundary = newLeftBoundary &
     initialised = True"
     */
    {
        fields = newFields;
        units = newUnits;
        buildings = newBuildings;
        topBoundary = newTopBoundary;
        rightBoundary = newRightBoundary;
        bottomBoundary = newBottomBoundary;
        leftBoundary = newLeftBoundary;
        initialised = true;
    }
    
    /**
     * Counts the occurence of the given terrain type in the map lists and returns the result
     * @param type a JameTerrainType to be counted
     * @return number of occurences
     */
    public static int getTerrainTypeCount( JameTerrainType type )
    /*:
     requires "initialised"
     modifies "JameCollection.free"
     ensures "result = icard { elem . elem : fields..JameCollection.collection & elem..JameMapContainer.type = type }"	   
     */
    {
        int count = 0;
        fields.resetIter();
        while
        	/*: 
            inv "(count = icard { elem . elem : (fields..JameCollection.collection - fields..JameCollection.free) & elem..JameMapContainer.type = type }) & initialized
            		& (initialised --> ( units ~= null & buildings ~= null & fields ~= null ))"         
            */
        ( fields.hasNext() )
        {
        	//: assume " ((ALL x.x : fields..Jamecollection.collection) --> x ~= null & x : JameMapContainer)"
            JameMapType cElemType = ( ( JameMapContainer ) fields.next() ).type;
            if( cElemType == type )
                count = count + 1;	        
        }
        return count;
    }
    
    /**
     * Counts the occurence of the given unit type in the map lists and returns the result
     * @param type a JameTerrainType to be counted
     * @return number of occurences
     */
    public static int getUnitTypeCount( JameUnitType type )
    /*:
     requires "initialised"
     modifies "JameCollection.free"
     ensures "result = icard { elem . elem : units..JameCollection.collection & elem..JameMapContainer.type = type }"	   
     */
    {
        int count = 0;
        
        units.resetIter();
        while
        /*: 
         inv "(count = icard { elem . elem : (units..JameCollection.collection - units..JameCollection.free) & elem..JameMapContainer.type = type }) & initialized
         		& (initialised --> ( units ~= null & buildings ~= null & fields ~= null ))"         
         */	
        ( units.hasNext() )
        {
        	//: assume " ((ALL x.x : units..Jamecollection.collection) --> x ~= null & x : JameMapContainer)"
            JameMapType cElemType = ( ( JameMapContainer ) units.next() ).type;
            if( cElemType == type )
                count = count + 1;	        
        }
        return count;
    }
    
    /**
     * Counts the occurence of the given building type in the map lists and returns the result
     * @param type a JameBuildingType to be counted
     * @return number of occurences
     */
    public static int getBuildingTypeCount( JameBuildingType type )
    /*:
     requires "initialised"
     modifies "JameCollection.free"
     ensures "result = icard { elem . elem : buildings..JameCollection.collection & elem..JameMapContainer.type = type }"	   
     */
    {
        int count = 0;
        
        buildings.resetIter();
        while
        /*: 
         inv "(count = icard { elem . elem : (buildings..JameCollection.collection - buildings..JameCollection.free) & elem..JameMapContainer.type = type }) & initialized
         		& (initialised --> ( units ~= null & buildings ~= null & fields ~= null ))"         
         */	
        ( buildings.hasNext() )
        {
        	//: assume " ((ALL x.x : buildings..Jamecollection.collection) --> x ~= null & x : JameMapContainer)"
            JameMapType cElemType = ( ( JameMapContainer ) buildings.next() ).type;
            if( cElemType == type )
                count = count + 1;	        
        }
        return count;
    }
    
    /**
     * Returns the number of units currently on the map
     * @return number of units
     */	
    public static int getUnitCount()
    /*: 
     requires "initialised"
     ensures "result = icard units..JameCollection.collection"
     */	
    {
        return units.size;
    }
    
    /**
     * Returns the number of buildings currently on the map
     * @return number of buildings
     */
    public static int getBuildingCount()
    /*: 
     requires "initialised"
     ensures "result = icard buildings..JameCollection.collection" 
     */
    {		
        return buildings.size;
    }
    
    /**
     * Finds and retuns field with given coordinates, returns null if field doesn't exist
     * @param x x coordinate of requested field
     * @param y y coordinate of requested field
     * @return requested field or null
     */
    public static JameTerrain getField( int x, int y )
    /*: 
     requires "initialised"
     modifies "JameCollection.free"
     ensures "( result = null & (ALL f . f : fields..JameCollection.collection --> ~(f..JameTerrain.xPos = x & f..JameTerrain.yPos = y ))) |
     		  ( result ~= null & result : fields..JameCollection.collection & result..JameTerrain.xPos = x & result..JameTerrain.yPos = y )"
     */
    {		
    	
    	//: assume "(ALL w. (w : fields..JameCollection.collection) --> (w..JameTerrain.xPos < rightBoundary & w..JameTerrain.xPos > leftBoundary & w..JameTerrain.yPos < bottomBoundary & w..JameTerrain.yPos > topBoundary))"
        if( x < leftBoundary || x > rightBoundary || y < topBoundary || y > bottomBoundary )
        {
            return null;
        }
        
        fields.resetIter();
        while
        /*: 
         inv "( ALL f . f : (fields..JameCollection.collection - fields..JameCollection.free)  --> f..JameTerrain.xPos ~= x & f..JameTerrain.yPos ~= y ) & initialised
         		& (initialised --> ( units ~= null & buildings ~= null & fields ~= null ))"
         */ 	
        ( fields.hasNext() )
        {
        	//: assume "( ALL f . f : fields..JameCollection.collection --> f ~= null & f : JameTerrain & f : alloc.JameTerrain)"
            JameTerrain cField = ( JameTerrain ) fields.next();
            if( cField.xPos == x && cField.yPos == y )
                return cField;
        }
        return null;
    }
    
    /**
     * Finds and returns units on given field
     * @param field map field for which units are returned
     * @return list of units
     */
    public static JameUnit getFieldUnit( JameTerrain field )
    /*: 
     requires "initialised & field ~= null"
     modifies "JameMap.units..JameCollection.free"
     ensures "( result = null & ( ALL b . b : JameMap.units..JameCollection.collection --> b..JameMapContainer.field ~= field ) ) |
     		  ( result : JameMap.units..JameCollection.collection & result..JameMapContainer.field = field )"
     */
    //ensures "result..JameCollection.collection = { e . e : units..JameCollection.collection & e..JameMapContainer.field = field} & result ~= null"
    // SUCCEEDS
    {
        return (JameUnit)fieldElement( units, field );
    }
    
    /**
     * Finds and returns buildings on given field
     * @param field map field for which buildings are returned
     * @return list of buildings
     */
    public static JameBuilding getFieldBuilding( JameTerrain field )
    /*: 
     requires "initialised & field ~= null"
     modifies "JameMap.buildings..JameCollection.free"
     ensures "( result = null & ( ALL b . b : JameMap.buildings..JameCollection.collection --> b..JameMapContainer.field ~= field ) ) |
     		  ( result : JameMap.buildings..JameCollection.collection & result..JameMapContainer.field = field )" 
     */
    // SUCCEEDS
    {
        return (JameBuilding)fieldElement( buildings, field );
    }
    /**
     * Moves unit to the given field.
     * @param unit unit to be moved
     * @param field field of destination
     */
    public static void moveUnit( JameUnit movedUnit, JameTerrain field )
    /*:
     requires "initialised & field ~= null & movedUnit ~= null"
     modifies "movedUnit..JameMapContainer.field"     
     ensures "movedUnit..JameMapContainer.field = field"
     */
    {
        movedUnit.assignField( field );
    }
    
    /**
     * Place buildings on map.
     * @param building building to be placed
     * @param field field where building is placed
     */
    public static void placeBuilding( JameBuilding building, JameTerrain field )
    /*: 
     requires "initialised & building ~= null & field ~= null"
     modifies "JameMap.buildings..JameCollection.collection", "JameMap.buildings..JameCollection.free", "JameMap.buildings..JameCollection.size", "JameMap.buildings..JameMapContainer.field"
     ensures "buildings..JameCollection.collection = old buildings..JameCollection.collection Un {building} & building..JameMapContainer.field = field" 
     */
    {
        if( !buildings.contains( building ) )
        {
            buildings.add( building );
        }	
        building.assignField( field );		
    }
    
    /**
     * Place unit on map.
     * @param unit unit to be placed
     * @param field field where unit is placed
     */
    public static void placeUnit( JameUnit placedUnit, JameTerrain field )
    /*: 
     requires "initialised & placedUnit ~= null & field ~= null"
     modifies "JameCollection.collection"
     ensures "units..JameCollection.collection = old units..JameCollection.collection Un {placedUnit} & placedUnit..JameMapContainer.field = field"
     */
    {
        if( !units.contains( placedUnit ) )
        {
            units.add( placedUnit );
        }
        placedUnit.assignField( field );		
    }
    
    /**
     * Add a field to the map.
     * @param field field to be placed
     */
    public static void addField( JameTerrain field )
    /*: 
     requires "initialised & field ~= null"
     modifies "JameCollection.collection"
     ensures "fields..JameCollection.collection = old fields..JameCollection.collection Un {field}"
     */
    {
        if( !fields.contains( field ) )
        {
            fields.add( field );
        }			
    }
    
    /**
     * Removes a unit from the map
     * @param unit unit to be removed
     */
    public static void removeUnit( JameUnit removedUnit )
    /*:
     requires "initialised"
     modifies "JameCollection.collection"
     ensures "units..JameCollection.collection = old units..JameCollection.collection - {removedUnit}"
     */
    {
        units.remove( removedUnit );
    }
    
    /**
     * Removes a building from the map.
     * @param building building to be removed
     */
    public static void removeBuilding( JameBuilding building )
    /*: 
     requires "initialised"
     modifies "JameCollection.collection"
     ensures "buildings..JameCollection.collection = old buildings..JameCollection.collection - {building}"
     */
    // SUCCEEDS
    {
        buildings.remove( building );
    }
    
    /**
     * Returns a list of elements from the list on the given field
     * @param list list from which elments are selected
     * @param field field which is selection criterium
     * @return list of elements on given field 
     */
    private static JameMapContainer fieldElement( JameCollection elmList, JameTerrain field )
    /*: 
     requires "initialised & elmList ~= null & field ~= null"
     modifies "elmList..JameCollection.free"
     ensures "result..JameCollection.collection  = { e . e : elmList..JameCollection.collection & e..JameMapContainer.field = field} & result : JameCollection"
     */
    {
        elmList.resetIter();
        while
        ( elmList.hasNext() )
        {
        	//: assume "( ALL x . x : elmList..JameCollection.collection --> x ~= null & x : JameMapContainer & x : alloc.JameMapContainer)"        	
            JameMapContainer cElement = ( JameMapContainer ) elmList.next();
            if( field == cElement.field )
            {
                return cElement;
            }		   
        }
        return null;
    }
}


