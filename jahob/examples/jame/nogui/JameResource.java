/*
 * Created on Mar 9, 2005
 * CHECKED
 */

/**
 * Resources for Jame.
 * 
 * @author aragos
 */
public class JameResource
{
    public /*:readonly*/ String name;
    public /*:readonly*/ int value;
    
    // public specvar resource :: "obj * int" 
    // vardefs "resource == ( name, value )"
    
    /**
     * Jame resource constructor.
     * @param newName resource name
     * @param newValue resource intial value
     */
    public JameResource( String newName, int newValue )
    /*:
     modifies name, value
     ensures "name = newName & value = newValue"
     */
    
    /*ensures "resource = ( newName, newValue )"
     */
    {
        this.name = newName;
        this.value = newValue;
    }

    /**
     * Set a new value for this resource.
     * @param newValue new value
     */
    public void setValue( int newValue )
    /*:
     modifies value
     ensures "value = newValue"
     */
    /*ensures "resource = ( fst (old resource ), newValue )"
     */
    {
        this.value = newValue;
    }
    /**
     * Add value to this resource.
     * @param addValue additional value
     */
    public void add( int addValue )
    /*:
     modifies value
     ensures "value = (old value) + addValue"
     */
    /*ensures "resource = ( (old name), ( old value ) + addValue ) & result = (snd resource)"
     */
    {
        int v;
        v = this.value + addValue;
        this.value = v;
    }
    
    /**
     * Substract value from resource.
     * @param subValue value to be substracted
     */
    public void sub( int subValue )
    /*:
     modifies value
     ensures "value = (old value) - subValue"
     */
    /*ensures "resource = ( (old name), ( old value ) - subValue ) & result = (snd resource)"
     */
    {
        int v;
        v = this.value - subValue;
        this.value = v;
    }
}
