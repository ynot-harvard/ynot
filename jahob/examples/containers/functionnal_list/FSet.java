/*
 * Functional set, implemented as a list
 * (previously FuncList.java by Charles Bouillaguet)
 */
public final class FSet
{
   private Object data;
   private FSet next;

   /*: 
    public ghost specvar content :: objset = "({} :: objset)";


    invariant "this = null --> content = {}";
    public ensured invariant "content \<subseteq> Object.alloc";
    
    invariant "this ~= null --> ( content = {data} Un next..content)";
    invariant "this ~= null --> data ~= null";
    
    */

    public static FSet emptyset()
    /*: requires "True"
        ensures "result..content = {} & Object.alloc = (old Object.alloc)"
    */
    {
        return null;
    }
   
    public static FSet insert(Object x, FSet l)
    /*: requires "x ~= null"
        ensures "result..content = l..content Un {x} 
	& Object.alloc = (old Object.alloc) Un {result}"
    */
    {
	FSet r = new FSet();
        r.data = x;
        r.next = l;
        //: "r..content" := "l..content Un {x}";
        return r;
    }

    public static boolean isEmpty(FSet l)
    /*: ensures "result = (l..content = {}) 
      & Object.alloc = old Object.alloc";
    */
    {
        return (l==null);
    }

    public static Object getOne(FSet l)
    /*: requires "comment ''ListMustBeNonempty'' (l..content ~= {})"
        ensures "result : l..content & result ~= null & Object.alloc = old Object.alloc"
    */
    {
        return l.data;
    }

    public static FSet remove(Object x, FSet l)
    /*: requires "True"
        ensures "result..content = l..content - {x}
	       & Object.alloc - (old Object.alloc) \<subseteq> FSet";
    */
    {
	if (l==null) return l;

	if (x == l.data)
	    return remove(x, l.next);
	else
	    return insert(l.data, remove (x, l.next));
    }

    public static boolean member(Object x, FSet l)
    /*: requires "True"
        ensures "result = (x : l..content)";
    */
    {
	if (l == null) {
            return false;
        }
	if (x == l.data) {
	    return true;
        }
	else {            
            // assume "False";
	    return member(x, l.next);
        }
    }
}
