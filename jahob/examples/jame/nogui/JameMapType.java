/*
 * Created on Mar 5, 2005
 * CHECKED 2
 */

/**
 * Type container for Jame.
 * Types can only be initialised, not changed later on, 
 * and of every distinctive type, there exists only one.
 * Subclasses must call super().
 * 
 * @author aragos
 */
/*abstract*/ class JameMapType {
	
	public /*:readonly*/ String name; // name of type	 
	public /*:readonly*/ int viewrange; //viewrange of type
	
	/**
	 * constructor, subclasses must call
	 * @param name name of type
	 */
	public void init( String newName )
	/*: 
	 modifies name
	 ensures "name = newName"
	 */
	{
	   this.name = newName;	   
	   this.viewrange = 0;
	}	
		
	
	public String toString(){
		return name;
	}
}
