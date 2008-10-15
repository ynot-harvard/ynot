public class List 
{
    private static Node first;

    /*:
      public static specvar content :: objset;
      private vardefs "content == 
           {x. EX n. x = n..Node.data & n ~= null & x ~= null &
                     rtrancl_pt (% x y. x..Node.next = y) first n}";

      invariant "tree [Node.next, Node.data]";

      invariant "first = null | 
                   (first : Object.alloc & (ALL n. n..Node.next ~= first & n..Node.data ~= first))";

      invariant "ALL n. (n ~= null & rtrancl_pt (% x y. x..Node.next = y) first n) --> n..Node.data ~= null";

      invariant "ALL d n. d ~= null & n ~= null & d ~: content --> n..Node.data ~= d";
      invariant "ALL x n. x ~= null & n ~= null & x..Node.next = n --> n : Object.alloc & n : Node";
    */
    
    public static void add(Object o1)
    /*: requires "o1 ~: content & o1 ~= null & o1 ~: Node"
        modifies content
        ensures "comment ''elementInserted'' (content = old content Un {o1})"
    */
    {
	Node n = new Node();
        n.data = o1;
        n.next = first;
        first = n;
    }

    public static boolean empty()
    /*: ensures "result = (ALL x. x ~: content)";
    */
    {
        return (first==null);
    }

    public static Object getOne()
    /*: requires "EX x. x : content"
        ensures "result : content";
    */
    {
        return first.data;
    }

    public static void remove(Object o1)
    /*: requires "o1 : content"
        modifies content
	ensures "content = old content - {o1}"
     */
    {
        //: noteThat "first != null"; // because o1:content
        if (first.data==o1) {
            Node oldfirst = first;
            first = oldfirst.next;
            oldfirst.next = null;
	    oldfirst.data = null;
        } else {
            Node prev = first;
            Node current = first.next;
            while /*: inv "prev..Node.next = current &
                    (rtrancl_pt (% x y. x..Node.next = y) List.first prev) &
                    (ALL n. rtrancl_pt (% x y. x..Node.next = y) List.first n & ~ rtrancl_pt (% x y. x..Node.next = y) current n -->
                            n..Node.data ~= o1)"
                   */
                (current.data!=o1) {
                //: noteThat "current != null"; // because o1:content
                prev = current;
                current = current.next;
            }
            current.data = null;
            prev.next = current.next;
            current.next = null;
        }
    }
}
