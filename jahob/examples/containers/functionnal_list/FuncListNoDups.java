/*
 * FuncListNoDups.java
 *
 * Created on June 26, 2006
 * Functional List with no Dupplicates
 */
public final class FuncList
{
   private Object data;
   private FuncList next;

   /*: 
    public ghost specvar content :: objset = "({} :: objset)";

    invariant "this = null --> content = {}"
    invariant "this ~= null --> ( content = {data} Un next..content)"
    invariant "this ~= null --> data ~= null"
    invariant "this ~= null --> data ~: next..content"  
    invariant "content \<subseteq> Object.alloc";
   */


   public static FuncList nil() 
   /*: requires "True"
       modifies content 
       ensures "result..content = {}"
    */
   {
      return null;
   }
   
    public static FuncList cons(Object x, FuncList l)
    /*: requires "x ~= null & x ~: l..content"
        ensures "result..content = l..content Un {x}"
    */
    {
	FuncList r = new FuncList();
        r.data = x;
        r.next = l;
        //: "r..content" := "l..content Un {x}";
        return r;
    }

    public static boolean is_nil(FuncList l)
    /*: ensures "result = (l..FuncList.content = {})";
    */
    {
        return (l==null);
    }

    public static Object head(FuncList l)
    /*: requires "l..FuncList.content ~= {}"
        ensures "result : l..FuncList.content & result ~= null"
    */
    {
        return l.data;
    }

    public static FuncList tail(FuncList l)
    /*: requires "l..FuncList.content ~= {}"
        ensures "result..FuncList.content \<subseteq> l..FuncList.content";
    */
    {
        return l.next;
    }    

    public static FuncList remove (Object x, FuncList l)
    /*: requires "x : l..FuncList.content"
        ensures "result..FuncList.content = l..FuncList.content - {x}";
    */
    {
	if (x == l.data)
	    return l.next;
	else
	    return cons (l.data, remove (x, l.next));
    }

    public static boolean is_in (Object x, FuncList l)
    /*: requires "True"
        ensures "result = (x : l..FuncList.content)";
    */
    {
	if (l == null) return false;
	if (x == l.data)
	    return true;
	else
	    return is_in(x, l.next);
    }

    public static FuncList reverse_append (FuncList l, FuncList acc)
    /*: requires "l..content Int acc..content = {}"
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
