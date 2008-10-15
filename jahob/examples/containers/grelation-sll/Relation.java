class Relation
    // A small example relation, meant to be kept minimal.
{
    private static Node first;

    /*:
      private static specvar reach :: "obj => obj => bool";
      vardefs
        "reach == (% a b. rtrancl_pt (% x y. x..Node.next=y) a b)";

      private static specvar nodes :: objset;
      vardefs
        "nodes == {n. n ~= null & reach first n}";

      public static specvar content :: "(obj * obj) set";
      vardefs 
        "content == {(k,v). EX n. n : nodes & k = n..Node.key & v = n..Node.value}";

      invariant "nodes \<subseteq> Object.alloc";
      invariant "tree [Node.next]";
      invariant "first ~= null --> (ALL n. n..Node.next ~= first)";
    */

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
        boolean b = (first==null);
        //: noteThat "b = (nodes = {})";
        return b;
    }

    public static void add(Object key, Object value)
    /*: modifies content
        ensures "content = old content Un {(key,value)}"
    */
    {
	Node n = new Node();
        n.key = key;
        n.value = value;
        n.next = first;
        first = n;
        //: noteThat "nodes = old nodes Un {n}";
    }
}
