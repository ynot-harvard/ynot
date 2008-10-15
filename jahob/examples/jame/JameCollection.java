/*
 * Created on Mar 8, 2005
 * CHECKED 2
 */

/**
 * Doubly-Linked list implementation of a set with an iterator within Jame.
 * 
 * @author aragos
 */
public class JameCollection
{
	// set of elements in the collection, defined as transitive closure over nodes
	// starting from and including head
    //: public specvar collection :: objset 
    /*: vardefs "collection == 
          	(if (head = null) then {} 
          	else { c . EX n . c = n..JameNode.content & ( head, n ) : rtrancl ( fgraph JameNode.next ) })"
    */
	
	// set of elements in the collection not yet looked at in the current iteration
	// starting from current
	//: public specvar free :: objset
	/*: vardefs "free == 
	 		(if (current = null) then {} 
	 		else { c . EX n . c = n..JameNode.content & ( current, n ) : rtrancl ( fgraph JameNode.next ) })"
	 */

	//: public inv "free <= collection"
	
    private JameNode head;
    private JameNode current;
    
    public /*:readonly*/ int size;
    //: public vardefs "size == icard collection"
    
    /**
     * Jame collection constructor.
     */
    public JameCollection()
    /*:
     modifies collection, free     
     ensures "collection = {} & free = {}" 
     */
    {
        head = null;
        current = null;
        size = 0;
    }
    
    /**
     * Adds an element to the beginning of the list.
     * @param o element to be added
     */
    public void add( Object newObject )
    /*:
     modifies collection
     ensures "collection = old collection Un {newObject}"
     */
    {        
        JameNode newNode = new JameNode();
        newNode.init(newObject);
        if( this.head != null )
        {
            newNode.setNext( this.head );
            this.head.setPrev( newNode );
        }
        this.head = newNode;
        this.size = this.size + 1;
    }
       
    /**
     * Removes element from the collection. 
     * @param delObject element to be removed
     */            
    public void remove( Object delObject )
    /*:
     modifies collection
     ensures "delObject ~: collection"  
     */
    {
        JameNode cNode = this.head;
        while( cNode != null )
        {    
        	if( cNode.content == delObject )
        	{
        		if( cNode == this.head )        			
        			this.head = cNode.next;
        		if( cNode == this.current )
        			this.current = cNode.next;
        		JameNode tmp = cNode.prev;
        		if( tmp != null)
        			tmp.setNext( cNode.next );
                tmp = cNode.next;
                if( tmp != null )
                	tmp.setPrev( cNode.prev );
                this.size = this.size - 1;
                return;
            }
        	cNode = cNode.next;
        }
    }
    
    /**
     * Reset iteration. Must be called before beginnging an iteration.
     */
    public void resetIter()
    /*:
     modifies free
     ensures "free = collection"
     */
    {
    	this.current = this.head;
    }
    
    /**
     * Returns the next object in list (can be null if end of list) and advances the internal pointer.
     * @return next object in list
     */
    public Object next()
    /*:
     modifies free
     ensures "result ~: free & result : collection & result : old free"
     */
    {	
    	//: assume "current ~= null"
    	Object temp = current.content;
        this.current = this.current.next;
        return temp;        
    }    
    
    /**
     * Returns whether the iteration has more elements.
     * @return true if elements are left, false otherwise
     */            
    public boolean hasNext()
    /*:
     ensures "result = (free ~= {})"
     */
    {
    	return current != null;
    }
        
    /**
     * Checks whether given element is contained within this collection.
     * @param cObject object to be checked for
     * @return whether object is contained
     */
    public boolean contains( Object cObject )
    /*:
     modifies "this..JameCollection.free"
     ensures "result = (cObject : collection)"
     */
    {          	
    	this.resetIter();
    	while( this.hasNext()  )
    	{
    		if( this.next() == cObject )
    			return true;
    	}
    	return false;
    }
    
    /**
     * Checks whether given collection is conatined in this collection.
     * @param c collection to be checked for
     * @return whether given collection is contained
     */
    public boolean containsCollection( JameCollection c )
    /*:
     ensures "result = (c..JameCollection.collection <= collection)"   
     */
    {
        if( c.size > this.size )
            return false;
        if( c.isEmpty() )
            return true;
        
        JameNode cNode = c.head;
        while( cNode != null )
        {
            if( !this.contains( cNode.content ) )
            {
                return false;
            }
            cNode = cNode.next;
        }
        return true;        
    }
    
    /**
     * Returns a clone of the original collection.
     * @return clone
     */
    public JameCollection copy()
    /*:       
     ensures "comment ''copy'' (result .. JameCollection.collection = this .. JameCollection.collection)
     			 & result : ( alloc.JameCollection - ( old alloc.JameCollection ) )"
     */
    {
        JameCollection clone = new JameCollection();
        this.resetIter();        
        while //: inv "clone .. JameCollection.collection = collection - free & free <= collection & clone : ( alloc.JameCollection - ( old alloc.JameCollection ) )"
        ( this.hasNext() )
        {        	
            clone.add( next() );
        }
        return clone;
    }
    
    public void reset()
    /*:
     modifies collection, free
     ensures "collection = {} & free = {}"
     */
    {
    	this.head = null;
    	this.current = null;
    	this.size = 0;
    }
    
    /**
     * Checks whether collections is empty.
     * @return whether collection is empty
     */
    public boolean isEmpty()
    /*:
     ensures "result = (collection = {})"
     */
    {
        return this.size == 0;
    }
}
