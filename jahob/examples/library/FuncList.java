/*
 * FuncList.java
 *
 * Created on June 24, 2006
 * Functional List
 */
public final class FuncList 
{
   private Object data;
   private FuncList next;

   /*: 
    public ghost specvar content :: objset = "({} :: objset)";


    invariant "this = null --> content = {}";
    public ensured invariant "content \<subseteq> Object.alloc";
    
    invariant "this ~= null --> ( content = {data} Un next..content)";
    invariant "this ~= null --> data ~= null";
    
    */

   public static FuncList nil()
 
   /*: requires "True"
       ensures "result..content = {} & Object.alloc = (old Object.alloc)"
    */
   {
      return null;
   }
   
    public static FuncList cons(Object x, FuncList l)
    /*: requires "x ~= null"
        ensures "result..content = l..content Un {x} 
	& Object.alloc = (old Object.alloc) Un {result}"
    */
    {
	FuncList r = new FuncList();
        r.data = x;
        r.next = l;
        //: "r..content" := "l..content Un {x}";
        return r;
    }

    public static boolean is_nil(FuncList l)
    /*: ensures "result = (l..FuncList.content = {}) 
      & Object.alloc = old Object.alloc";
    */
    {
        return (l==null);
    }

    public static Object head(FuncList l)
    /*: requires "comment ''ListMustBeNonempty'' (l..FuncList.content ~= {})"
        ensures "result : l..FuncList.content & result ~= null & Object.alloc = old Object.alloc"
    */
    {
        return l.data;
    }

    public static FuncList tail(FuncList l)
    /*: requires "l..FuncList.content ~= {}"
        ensures "result..FuncList.content \<subseteq> l..FuncList.content & Object.alloc = old Object.alloc";
    */
    {
        return l.next;
    }    

    public static FuncList remove (Object x, FuncList l)
    /*: requires "True"
        ensures "result..FuncList.content = l..FuncList.content - {x}
	       & Object.alloc - (old Object.alloc) \<subseteq> FuncList";
    */
    {
	if (l==null) return l;

	if (x == l.data)
	    return remove (x, l.next);
	else
	    return cons (l.data, remove (x, l.next));
    }

 public static boolean is_in (Object x, FuncList l)
    /*: requires "True"
        ensures "result = (x : l..FuncList.content)";
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
	    return is_in(x, l.next);
        }
    }

    public static FuncList reverse_append (FuncList l, FuncList acc)
    /*: requires "True"
        ensures "result..content = l..content Un acc..content";
    */
    {
	if (l == null) return acc;
	return reverse_append(l.next, cons(l.data, acc));
    }

    public static FuncList reverse (FuncList l)
    /*: requires "True"
        ensures "result..content = l..content";
    */
    {
	return reverse_append(l, null);
    }
}
