/*
 * AssocList.java
 *
 * Created on June 24, 2006
 * Functional List
 */
public final class AssocList 
{
   private Object key;
   private Object data;
   private AssocList next;

   /*: 
    public ghost specvar content :: "(obj * obj) set" = "({} :: (obj * obj) set)";

    invariant "this = null --> content = {}"
    invariant "this ~= null --> ( content = {(key, data)} Un next..content)"
    public ensured invariant "{v. (EX k. (k,v) : content)} \<subseteq> Object.alloc"
    public ensured invariant "{k. (EX v. (k,v) : content)} \<subseteq> Object.alloc"
    */

   public static AssocList nil() 
   /*: requires "True"
       ensures "result..content = {}"
    */
   {
      return null;
   }
   
    public static AssocList cons(Object k, Object v, AssocList l)
    /*: ensures "result..content = l..content Un {(k,v)}"
    */
    {
	AssocList r = new AssocList();
        r.data = v;
	r.key = k;
        r.next = l;
        //: "r..content" := "l..content Un {(k,v)}";

        return r;
    }

    public static boolean is_nil(AssocList l)
    /*: ensures "result = (l..AssocList.content = {})";
    */
    {
        return (l==null);
    }


    public static AssocList remove (Object k, Object v, AssocList l)
    /*: requires "k ~= null & v ~= null"
        ensures "result..AssocList.content = l..AssocList.content - {(k,v)}";
    */
    {
	if (l == null) return null;
	if (k == l.key && v == l.data)
	    return remove(k,v, l.next);
	else
	    return cons (l.key, l.data, remove (k, v, l.next));
    }

    public static Object lookup (Object k, AssocList l)
    /*: requires "k ~= null"
        ensures "result ~= null --> (k,result) : l..content";
    */
    {
	if (l == null) return null;
	if (k == l.key)
	    return l.data;
	else
	    return lookup(k, l.next);
    }

    public static FuncList image (Object x, AssocList l)
    /*: requires "x ~= null"
        ensures "result..FuncList.content = {y. (x,y) : l..AssocList.content}"
    */
    {
	if (l == null) 
	    return FuncList.nil();
	else {
	    if (x == l.key)
		return FuncList.cons(l.data, image(x, l.next));
	    else
		return image(x, l.next);
	}
    }

    public static FuncList inverseImage (Object y, AssocList l)
    /*: requires "y ~= null"
        ensures "result..FuncList.content = {x. (x,y) : l..AssocList.content}"
    */
    {
	if (l == null) 
	    return FuncList.nil();
	else {
	    if (y == l.data)
		return FuncList.cons(l.key, inverseImage(y, l.next));
	    else
		return inverseImage(y, l.next);
	}
    }

    public static FuncList domain (AssocList l)
    /*: 
        ensures "result..FuncList.content = {x. EX y. (x,y) : l..AssocList.content}";
    */
    {
	if (l == null) 
	    return FuncList.nil();
	else {
	    return FuncList.cons(l.key, domain(l.next));
	}
    }
}
