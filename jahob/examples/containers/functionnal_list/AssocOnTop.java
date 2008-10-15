/*
 * AssocOnTop.java
 *
 * Created on June 24, 2006
 * Functional List
 */
class Node {
    public Object key;
    public Object data;
}

public final class AssocOnTop 
{
    private FuncList actual_list;

   /*: 
    public specvar content :: "(obj * obj) set";
    public static ghost specvar outside :: bool = "True";

    vardefs "content == {(x, y). this ~= null & (EX n. n : actual_list..FuncList.content & x=n..Node.key & y=n..Node.data)}"

    invariant "outside --> (ALL this. this : Object.alloc & this : AssocOnTop & this ~= null 
                              --> this..content ~= {})"
    invariant "outside --> (this = null --> this..content = {})"    

    invariant "outside --> (this ~= null --> (ALL n. n : actual_list..FuncList.content --> n..Node.data ~= null))"
    invariant "outside --> (this ~= null --> (ALL n. n : actual_list..FuncList.content --> n : Node))"
   */
   

   public static AssocOnTop nil() 
   /*: requires "True"
       modifies content
       ensures "result..content = {}"
    */
   {
      return null;
   }
   
    public static AssocOnTop cons(Object k, Object v, AssocOnTop l)
    /*: requires "k ~= null & v ~= null & outside"
        ensures "result..content = l..content Un {(k,v)}"
    */
    {
	AssocOnTop r = new AssocOnTop();
	Node n = new Node();
        n.data = v;
	n.key = k;
	
	if (l == null) {
	    //: outside := "False"
	    r.actual_list = FuncList.cons(n, FuncList.nil() );
	    //: outside := "True"
	}
	else {
	    //: outside := "False"
	    r.actual_list = FuncList.cons(n, l.actual_list);
	    // noteThat "r..content ~= {}";
	    //: noteThat "n ~: AssocOnTop & r..actual_list ~: AssocOnTop";
	    //: outside := "True"
	}

	return r;
    }

    public static boolean is_nil(AssocOnTop l)
    /*:
      requires "outside"
      ensures "result = (l..AssocOnTop.content = {})";
    */
    {
        return (l==null);
    }




    public static FuncList remove_helper (Object k, FuncList l)
    /*: requires "k ~= null & (ALL n. n : l..FuncList.content --> n : Node)"
        ensures "result..FuncList.content = l..FuncList.content - {n. n..Node.key=k}
	        & Object.alloc - (old Object.alloc) \<subseteq> (Node Un FuncList)";
    */
    {
	if (FuncList.is_nil(l)) {
	    return FuncList.nil ();
	}
	else {
	    Node n = (Node) FuncList.head(l);
	    if (k == n.key) {
		return remove_helper(k, FuncList.remove(n,l));   // suboptimal : there are no duplicates
	    }
	    else {
		return (FuncList.cons (n, remove_helper (k, FuncList.remove(n, l))));
	    }
	}
    }
    

    public static AssocOnTop remove (Object k, AssocOnTop l)
    /*: requires "k ~= null & outside"
        ensures "result..AssocOnTop.content = l..AssocOnTop.content - {(x,v). x=k}";
    */
    {
	if (l == null) {
	    return null;
	}
	else {
	    boolean b = FuncList.is_nil(l.actual_list);
	    if (b) 
		{ 
		    return null; }
	    else
		{
		    //: outside := "False"

                    FuncList l1 = remove_helper(k, l.actual_list);
                    boolean b1 = FuncList.is_nil(l1);
                    //: outside := "True"
                    if (b1) {
                        return null;
                    } else {
                        AssocOnTop r = new AssocOnTop();
                        r.actual_list = l1;
                        return r;
                    }
		}
	}
    }

    public static Node lookup_helper (Object k, FuncList l)
    /*: requires "k ~= null
                & l..FuncList.content ~= {}
                & (ALL n. n : l..FuncList.content --> n : Node)"

        ensures "(result ~= null --> result : l..FuncList.content & result..Node.key = k)
	       & (result = null --> (ALL n. n : l..FuncList.content --> n..Node.key ~= k))"
    */
    {
	Node h = (Node) FuncList.head(l);
	if (h.key == k)
	    {
		// assume "False"
	    return h;
	    }
	else
	    {
		FuncList tail = FuncList.remove(h, l);
		if (FuncList.is_nil(tail)) {
		    // assume "False"
		    return null;
		    }
		else
		    {
			//noteThat "l..FuncList.content = tail..FuncList.content Un {h}"
			Node n = lookup_helper(k, tail);
			// noteThat "(n ~= null --> n : tail..FuncList.content & n..Node.key = k)"
			// noteThat "(n = null --> (ALL m. m : tail..FuncList.content --> m..Node.key ~= k) )"
			// assume "False"
			return n;
		    }
	    }
    }

 public static Object lookup (Object k, AssocOnTop l)
    /*: requires "k ~= null & outside"
        ensures "((k,result) : l..AssocOnTop.content & result ~= null) | 
	((ALL v. (k,v) ~: l..AssocOnTop.content) & result = null)";
    */
    {
	if (l == null) {
	    return null;
	}
	else {

	    if (FuncList.is_nil(l.actual_list)) {
		return null;
	    }
	    else
		{
		    Node h = lookup_helper(k, l.actual_list);
		    if (h == null) {
			return null;
		    }
		    else {
			return h.data;
		    }
		}
	}
    }

}
