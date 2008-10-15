/*
 * Created on Mar 7, 2005
 */

/**
 * Resource collections for Jame.
 * 
 * Provides collections and utility methods for game resources.
 * 
 * @author aragos
 */
public class JameResourceSet
{
    public JameCollection resources; // collection of resources
    // inv "resources ~= null"
    //: public specvar resSet :: "(obj * int) set" 
    //: vardefs "resSet == { p . EX e . e : resources .. JameCollection.collection & p = ( e .. JameResource.name, e .. JameResource.value ) }"
    
    // specvar resUntouched :: "(obj * int) set"
    // vardefs "resUntouched == { p . EX e . e : resources .. JameCollection.free & p = ( e .. JameResource.name, e .. JameResource.value ) }"
    
    // inv "resUntouched <= resSet" 

    // inv "resources..Object.owner = token.JameResourceSet"

    /**
     * Jame resource collection constructor.
     * @param resources a collection of JameResources
     */
    public void initEx( JameResourceSet newResources )
    // TODO get rid of resources reference (is private) 
    /*:
     requires "newResources ~= null & newResources..JameResourceSet.resources ~= null" 
     modifies resSet
     ensures "(this .. JameResourceSet.resSet) = (newResources..JameResourceSet.resSet)"
     */
    // SUCCEEDS
    {
    	JameCollection oldResSet = newResources.resources;
        this.resources = oldResSet.copy(); 
    }
    
    /**
     * Jame empty resource collection constructor.
     */
    public JameResourceSet()
    /*:
     modifies "JameCollection.collection", "JameCollection.free", resSet
     ensures "resSet = {}" 
     */
    // succeeds
    {
        this.resources = new JameCollection();
    }
    
    /**
     * Add a resource to the collections pool and return result
     * @param addRes resources to be added
     * @return new resource value in collection
     */
    public void add( JameResource addRes )
    /*:
     requires "addRes ~= null & addRes..JameResource.name ~= null & this .. JameResourceSet.resource ~= null"
     modifies resSet, "JameCollection.collection", "JameCollection.free"
     ensures "
     	( ( EX y . y : (old resSet) & fst y = addRes..JameResource.name & resSet = ((old resSet) - {y}) Un {(addRes..JameResource.name, (snd y) + addRes..JameResource.value)} )) |
     	(~( EX y . y : (old resSet) & fst y = addRes..JameResource.name) & resSet = (old resSet) Un {(addRes..JameResource.name, addRes..JameResource.value)})"
    */
    // SUCCEEDS
    {
	//: assert "False"
    	JameResource oldRes = find( addRes.name );
    	if( oldRes != null )
    	{
    		// assume "(oldRes..JameResource.name, oldRes..JameResource.value) : resSet"
    		oldRes.add( addRes.value );
    	}
    	else
    	{
    		resources.add( addRes );
    	}        
    }
    
    /**
     * Substract a resource from the collections pool and return result
     * @param subRes resources to be substracted
     * @return new iron store in collection
     */
    public void substract( JameResource subRes )
    /*:
     requires "subRes ~= null & subRes..JameResource.name ~= null & subRes..JameResource.value ~= null & resources ~= null"
     modifies resSet
     ensures "
     	( ( EX y . y : (old resSet) & fst y = subRes..JameResource.name & resSet = ((old resSet) - {y}) Un {(subRes..JameResource.name, (snd y) - subRes..JameResource.value)} )) |
     	(~( EX y . y : (old resSet) & fst y = subRes..JameResource.name) & resSet = (old resSet) Un {(subRes..JameResource.name, 0 - subRes..JameResource.value)})"
    */
    // FAILS
    {
    	JameResource oldRes = find( subRes.name );
    	if( oldRes != null )
    	{
    		//: assume "(oldRes..JameResource.name, oldRes..JameResource.value) : resSet"
    		oldRes.sub( subRes.value );
    	}
    	else
    	{
    		resources.add( new JameResource(subRes.name, 0 - subRes.value ));
    	}
    }
    
    /**
     * Sets resources storage in the collection to given value.
     * @param newRes new resource storage value
     */
    public void setResource( JameResource newRes )
    /*:
     requires "newRes ~= null & newRes..JameResource.name ~= null" 
     modifies resSet, "JameCollection.collection", "JameCollection.free"
     ensures "
     	( ( EX y . y : (old resSet) & fst y = newRes..JameResource.name & resSet = ((old resSet) - {y}) Un {(newRes..JameResource.name, newRes..JameResource.value)} )) |
     	(~( EX y . y : (old resSet) & fst y = newRes..JameResource.name) & resSet = (old resSet) Un {(newRes..JameResource.name, newRes..JameResource.value)})"     
    */    
    // FAILS TIMEOUT (succeeds in no time with vampire)
    {
    	JameResource oldRes = find( newRes.name );
    	if( oldRes != null )
    	{
    		// assume "(oldRes..JameResource.name, oldRes..JameResource.value) : resSet"
    		oldRes.setValue( newRes.value );
    	}
    	else
    	{
    		resources.add( newRes );
    	}
    }
    
    /**      ensures "result = ( EX x . fst x = subRes .. JameResource.name & x : resSet & snd x >= subRes .. JameResource.value )"     
     * Checks whether this collection contains the given resource (at all and amount)
     * @param subRes resource to be checked for
     * @return whether given resource is contained
     */
    public boolean contains( JameResource subRes )
    /*:
     requires "subRes ~= null & subRes..JameResource.name ~= null"
     ensures "False"
     */
    //  
    {
    	JameResource oldRes = find( subRes.name );
    	if (oldRes == null) return false;
    	if (subRes.value <= oldRes.value) return true;
    	return false;
    	// return oldRes != null && oldRes.value >= subRes.value;
    }
    
    public boolean charles()
	/*: requires "a ~= null"
	   ensures "False"
	*/
    {
	return false;
    }

    /**
     * Checks whether the given collection is contained in the calling collection.
     * @param subSet the set to be checked
     * @return whether the given set is contained in the calling set
     */
    public boolean containsSet( JameResourceSet subSet )
    /*:     
     requires "subSet ~= null"
     modifies "subSet..JameResourceSet.resources..JameCollection.free", "resources..JameCollection.free"
     ensures "result = ( subSet .. JameResourceSet.resSet <= resSet )"
     */
    // FAILS
    // TODO reflect amount check
    {
    	JameCollection subRes = subSet.resources;
        subRes.resetIter();
        while

	 //  subSet .. JameResourceSet.resSet - subSet .. JameResourceSet.resUntouched <= resSet
        /*: inv "
         false
         "
         */
        // TODO reflect amount check
        ( subRes.hasNext() )
        {
            if( !contains( (JameResource) subRes.next() ) )
            {
                return false;
            }
        }
        return true;
    }    
    
    /**
     * Substracts the given set from current one and returns result.
     * @param lessSet set to be substracted
     * @return result of substraction
     */    
    public JameResourceSet substractSet( JameResourceSet substractSet )
    /*:
     requires "substractSet ~= null"     
     modifies resSet
     ensures "
     	resSet = { r . 	( EX y n . y : (old resSet) & n : substractSet .. JameResourceSet.resSet & fst n = fst y & fst r = fst y & snd r = (snd y) - (snd n) ) |
     					( EX y n . y : (old resSet) & n ~: substractSet .. JameResourceSet.resSet & fst n = fst y & fst r = fst y & snd r = snd y ) |
     					( EX y n . y ~: (old resSet) & n : substractSet .. JameResourceSet.resSet & fst n = fst y & fst r = fst n & snd r = snd n )
     			 }"
    */ 
    // FAILS
    {
        JameCollection subRes = substractSet.resources;
        subRes.resetIter();
        while 
        /*: inv "
         resSet = { x .	( EX y n . y : (old resSet) & n : substractSet .. JameResourceSet.resUntouched & fst n = fst y & fst x = fst y & snd x = snd y ) |         				
         				( EX y n . y : (old resSet) & n ~: substractSet .. JameResourceSet.resSet & fst n = fst y & fst x = fst y & snd x = snd y ) |	
     					( EX y n . y ~: (old resSet) & n : substractSet .. JameResourceSet.resSet & fst n = fst y & fst x = fst n & snd x = snd n ) |
     					( EX y n c . y ~: (old resSet) & n : substractSet .. JameResourceSet.resSet & c ~: substractSet .. JameResourceSet.resUntouched & fst n = fst y & fst c = fst y & fst x = fst y & snd x = snd n ) |
     					( EX y n c . y : (old resSet) & n : substractSet .. JameResourceSet.resSet & c ~: substractSet .. JameResourceSet.resUntouched & fst n = fst y & fst c = fst y & fst x = fst y & snd x = (snd y) - (snd n) )
     	              }" */     	
        ( subRes.hasNext() )
        {
            this.substract( (JameResource) subRes.next() );
        }
        return this;
    }
    
    /**
     * Adds the given set to the current one and returns result.
     * @param addSet set to be added
     * @return result of addition
     */    
    public JameResourceSet addSet( JameResourceSet addSet )
    /*:     
     requires "addSet ~= null"
     modifies resSet
     ensures "
     	resSet = { r . 	( EX y n . y : (old resSet) & n : addSet .. JameResourceSet.resSet & fst n = fst y & fst r = fst y & snd r = (snd y) + (snd n) ) |
     					( EX y n . y : (old resSet) & n ~: addSet .. JameResourceSet.resSet & fst n = fst y & fst r = fst y & snd r = snd y ) |
     					( EX y n . y ~: (old resSet) & n : addSet .. JameResourceSet.resSet & fst n = fst y & fst r = fst n & snd r = snd n )
     			 }"
    */
    // FAILS
    {
    	JameCollection addRes = addSet.resources;
        addRes.resetIter();
        while
        /*: inv "
         resSet = { x .	( EX y n . y : (old resSet) & n : addSet .. JameResourceSet.resUntouched & fst n = fst y & fst x = fst y & snd x = snd y ) |         				
          				( EX y n . y : (old resSet) & n ~: addSet .. JameResourceSet.resSet & fst n = fst y & fst x = fst y & snd x = snd y ) |	
        				( EX y n . y ~: (old resSet) & n : addSet .. JameResourceSet.resSet & fst n = fst y & fst x = fst n & snd x = snd n ) |
        				( EX y n c . y ~: (old resSet) & n : addSet .. JameResourceSet.resSet & c ~: addSet .. JameResourceSet.resUntouched & fst n = fst y & fst c = fst y & fst x = fst y & snd x = snd n ) |
        				( EX y n c . y : (old resSet) & n : addSet .. JameResourceSet.resSet & c ~: addSet .. JameResourceSet.resUntouched & fst n = fst y & fst c = fst y & fst x = fst y & snd x = (snd y) + (snd n) )
                  }" */	
        ( addRes.hasNext() )
        {
            this.add( (JameResource) addRes.next() );
        }
        return this;
    }

    /**
     * reset current resource set to empty
     */
    public void reset()
    /*:
     modifies resSet, resUntouched
     ensures "resSet = {} & resUntouched = {}"
     */
    {
    	this.resources.reset();
    }    
    
    /**
     * Finds and returns a Jameresource with name key
     * @param key name of resource to be found
     * @return resource or null upon failure
     */
    public JameResource find(String key)
    // TODO: Make modifies clause be more precise
    /*:     
     requires "key ~= null"
     ensures "((result = null & (ALL x . x : resSet --> fst x ~= key)) |
              ((result ~= null) &
               (result .. JameResource.name = key) & 
               ((result .. JameResource.name, result .. JameResource.value) : resSet)) &
               (result : resources..JameCollection.collection))"
     */
    // Viktor is checking...
    {    	
    	resources.resetIter();
        while /*: inv "(ALL x. (x : resources..JameCollection.collection & x ~: resources..JameCollection.free)
                --> x..JameResource.name ~= key) &
		(ALL x. x..resources ~= null) &
                (ALL x. x..resources..Object.owner = token.JameResourceSet) &
                (ALL (x :: obj). (old (x..Object.owner) ~= token.JameResourceSet) --> ((x .. JameCollection.free) = old (x .. JameCollection.free)))" */
        (resources.hasNext())
        {
            /*: assume "ALL x . x : resources .. JameCollection.collection --> 
              x ~= null & x : JameResource" */
            JameResource cRes = (JameResource) resources.next();
	    //: assume "cRes ~= null";
            if (Jame.equals(key, cRes.name))
            {
                return cRes;
            }
        }
        return null;
    }

    
    public JameResource get( String name )
    /*:
     requires "name ~= null"
     modifies "JameCollection.collection", "JameCollection.free"
     ensures "(result = null & (ALL x . x : resSet --> fst x ~= name)) |
              ((result .. JameResource.name = name) & 
               ((result .. JameResource.name, result .. JameResource.value) : resSet))"
     */
    {
    	return find( name );
    }
    

    
    public JameResourceSet copy()
    /*:
     ensures "comment ''copy'' (result .. JameResourceSet.resSet = this .. JameResourceSet.resSet)
     			 & (result : ( alloc.JameResourceSet - ( old alloc.JameResourceSet ) ))
     			 & (ALL x . ( x .. JameResource.name, x .. JameResource.value ) : result..JameResourceSet.resSet --> x : ( alloc.JameResource - ( old alloc.JameResource ) ))"
     */
    {
    	JameResourceSet ret = new JameResourceSet();
    	this.resources.resetIter();
    	while( this.resources.hasNext())
    	{
    		JameResource cRes = (JameResource) this.resources.next();
    		ret.add( new JameResource( cRes.name, cRes.value ) );
    	}
    	return ret;
    }
    
    /*public String toString()
    {
    	String ret = "";
    	resources.resetIter();
    	while( resources.hasNext() )
    	{
    		JameResource cRes = (JameResource)resources.next();
    		ret = ret + cRes.name + ": " + cRes.value + "\n";    		
    	}
    	return ret;
    }*/
}
