/*
 * Created on Mar 5, 2005
 * CHECKED 2
 */

/**
 * Container for any element on the map.
 * Supplies basic methods and attributes.
 *  
 * Subclasses must call super().
 * 
 * @author aragos
 */
/*abstract*/ class JameMapContainer {
	
	public /*:readonly*/ JameTerrain field;	// reference to the containers field
	public /*:readonly*/ JamePlayer owner;	// reference to the containers owner
	public /*:readonly*/ JameMapType type;	// reference to the containers type, specific to the type of container
	
	/**
	 * Map type constructor. Super constructor for any element on the map.
	 * @param type elements type
	 * @param field field element is placed on
	 * @param owner elements owner
	 */
	public void init( JameMapType newType, JameTerrain newField, JamePlayer newOwner )
	/*:
	 modifies type, field, owner
	 ensures "
	 	type = newType &
	 	owner = newOwner &
	 	field = newField"
	 */
	{
		this.type = newType;
		this.field = newField;
		this.owner = newOwner;
	}
	
	/**
	 * Assings given field to the element.
	 * @param field field to be assigned to element
	 */
	void assignField( JameTerrain newField )
	/*:
	 modifies "this..JameMapContainer.field"
	 ensures "field = newField"
	 */
	{
		this.field = newField;
	}
	
	/**
	 * Assigns given owner to the element.
	 * @param owner owner to be assigned to the element
	 */
	void assignOwner( JamePlayer newOwner )
	/*:
	 modifies owner
	 ensures "owner = newOwner"
	 */
	{
		this.owner = newOwner;
	}
	
	/**
	 * Assings given type to the element.
	 * @param type type to be assigned to the element
	 */
	void assignType( JameMapType newType )
	/*:
	 modifies type
	 ensures "type = newType"
	 */
	{
		this.type = newType;
	}

	/*public String toString(){
		return this.getClass().toString() + ":" + this.type.getClass().toString();
	}*/
}
