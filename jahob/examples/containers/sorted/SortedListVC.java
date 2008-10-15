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

      private static specvar sortedNodes :: objset;
      vardefs "sortedNodes == {n. n..Node.next ~= null --> n..Node.key <= n..Node.next..Node.key}";

      invariant "comment ''sorted'' (content \<subseteq> sortedNodes)";
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

    public static void vcadd2(Node nn) // vkuncak thought this more complex invariant was needed
    /*: requires "nn ~= null & nn ~: content"
        modifies content
        ensures "content = old content Un {nn}"
    */
    {
        /*:
          private ghost specvar rnodes :: objset;
         */
	Node prev = null;
	Node current = first;
        //: rnodes := "{}";
	while /*: 
            inv "(prev = null --> current = first & rnodes = {}) &
                 (prev ~= null --> prev..Node.next = current & reach first prev &
                   rnodes = {n. reach first n & reach n prev} &
                   rnodes \<subseteq> content &
                   prev : rnodes & current ~: rnodes &
                   (ALL n. n : rnodes --> n..Node.key < nn..Node.key))"
              */
          ((current != null) && (current.key < nn.key)) {
           //: rnodes := "rnodes Un {current}";
	   prev = current;
	   current = current.next;
	}
	nn.next = current;
	if (prev != null){
	   prev.next = nn;
	} else {
	   first = nn;
	}
        //: noteThat "content = rnodes Un (old content \<setminus> rnodes) Un {nn}";
    }
}
