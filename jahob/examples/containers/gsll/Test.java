class SortedList
{
    private static Node first;

    /*: 
      private static specvar reach :: "obj => obj => bool";
      vardefs
        "reach == (% a b. rtrancl_pt (% x y. x..Node.next=y) a b)";

      public static specvar content :: objset;
      vardefs
        "content == {n. n ~= null & reach first n}";

      public invariant "content \<subseteq> Object.alloc";

      invariant "tree [Node.next]";

      invariant "first = null | (ALL n. n..Node.next ~= first)";
      
      invariant "ALL x n. x ~= null & n ~= null & x..Node.next = n --> n : content";

    */

    public static void vcadd1(Node nn) // a surprisingly simple invariant suffices
    /*: requires "nn ~= null & nn ~: content"
        modifies content
        ensures "content = old content Un {nn}"
    */
    {
	Node prev = null;
	Node current = first;
	while /*: 
            inv "(prev = null --> current = first) &
                 (prev ~= null --> prev..Node.next = current & reach first prev &
                   prev..Node.key < nn..Node.key)"
              */
          ((current != null) && (current.key < nn.key)) {
	   prev = current;
	   current = current.next;
	}
	nn.next = current;
	if (prev != null){
	   prev.next = nn;
	} else {
	   first = nn;
	}
        //: noteThat "content = old content Un {nn}";
    }

    public static void vcadd2(Node nn) 
    /*: requires "nn ~= null & nn ~: content"
        modifies content
        ensures "content = old content Un {nn}"
    */
    {
	nn.next = first;
        first = nn;
        //: noteThat "content = old content Un {nn}";
    }

    public static void vcadd3() 
    /*: modifies content
        ensures "True"
    */
    {
        Node nn = new Node();
	nn.next = first;
        first = nn;
        //: noteThat "content = old content Un {nn}";
    }

}
