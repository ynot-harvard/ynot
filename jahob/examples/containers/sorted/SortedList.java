class SortedList 
    /* sorted list  */
{
    private static Node first;

    /*: 
      private static specvar reach :: "obj => obj => bool";
      vardefs
        "reach == (% a b. rtrancl_pt (% x y. x..Node.next=y) a b)";

      public static specvar content :: objset;
      vardefs
        "content == {n. n ~= null & reach first n}";

      invariant "tree [Node.next]";

      invariant "first = null | (ALL n. n..Node.next ~= first)";
      
      invariant "ALL x n. x ~= null & n ~= null & x..Node.next = n --> n : content";

      invariant "(ALL n. n : content & n..Node.next ~= null --> n..Node.key <= n..Node.next..Node.key)";
    */

   public static void add2(Node nn)
    /*: requires "nn ~= null & nn ~: content"
        modifies content
        ensures "content = old content Un {nn}"
    */
    {
	Node prev = null;
	Node current = first;
	while ((current != null) && (current.key < nn.key)) {
	   prev = current;
	   current = current.next;                    
	}
	nn.next = current;
	if (prev != null){
	   prev.next = nn;
	} else {
	   first = nn;
	}
    }

   public static void add(Node nn)
      /*: requires "nn ~= null & nn ~: content"
	modifies content
	ensures "content = old content Un {nn}"
      */
   {
      if (first==null) {
	 first = nn;
	 nn.next = null;
	 return;
      } else if (first.key >= nn.key) {
	 nn.next = first;
	 first = nn;
	 return;
      }

      Node prev = first;
      Node current = first.next;
      while ((current != null) && (current.key < nn.key)) {
	 prev = current;
	 current = current.next;                    
      }
      nn.next = current;
      prev.next = nn;
   }
}
