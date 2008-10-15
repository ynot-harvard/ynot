// NOT FINISHED
public final class AssocList 
    /* unsorted global association list with potentially duplicate keys */
{
    private static Node first;

    /*: 
      private static specvar nodes :: objset;
      vardefs
        "nodes == {n. n ~= null & rtrancl_pt (% x y. x..Node.next=y) first n}";

      private static specvar between :: "obj => obj => obj => bool";
      vardefs
        "between == (% a n b. rtrancl_pt (% x y. x..Node.next=y) a n &
                              ~ rtrancl_pt (% x y. x..Node.next=y) b n)";

      invariant "tree [Node.next]";

      public static specvar content :: "(obj * obj) set";
      vardefs 
        "content == {(k,v). (EX n. k = n..Node.key & v = n..Node.value &
                            n : nodes &
                            (ALL (n1::obj). between first n1 n --> n1..Node.key ~= v))}";

//      public specvar ismap :: bool;
//      vardefs
//        "ismap == (ALL k v1 v2. (k,v1) : content & (k,v2) : content --> v1=v2)";
    */

    public static void test()
    {
        // assert "ismap"; // requires reasoning about lists and uninterpreted function symbols
    }

    public static void init()
    //: modifies content ensures "content = {}"
    {
        first = null;
        //: noteThat "nodes = {}";
    }

    public static boolean isEmpty()
    /*: ensures "result = (content = {})";
    */
    {
        return (first==null);
    }

    public static boolean defined(Object key)
    /*: ensures "result = (EX v. (key,v) : content)" */
    {
        Node n = first;
        //: ghost specvar traversed :: objset = "{}";
        while /*: inv "fclosure Node.next first n &
                (traversed = {v. fclosure Node.next first v & ~ fclosure Node.next v n}) &
                (ALL v. v : traversed --> v..Node.key ~= key)"
               */
            (n != null) {
            if (n.key==key) return true;
            n = n.next;
            //: traversed := "traversed - {n}";
        }
        return false;
    }

    public static Object lookup(Object key)
    /*: ensures "(key,result) : content | 
                 (ALL v. (key,v) ~: content)" */
    {
        Node n = first;
        while (n != null) {
            if (n.key==key) return n.value;
            n = n.next;
        }
        return null;
    }

    public static void remove(Object key)
    /*: modifies content
        ensures "content = old content - {(x,y). x=key}"
    */
    {
        // a bit tricky
    }
    
    public static void update(Object key, Object value)
    /*: requires "key ~= null"
        modifies content
        ensures "content = (old content - {(x,y). x=key}) Un {(key,value)}"
    */
    {
	Node n = new Node();
        n.key = key;
        n.value = value;
        n.next = first;
        first = n;
    }

}
