class UniqueSorted
    /* sorted list  */
{
    private static Node first;

    /*: 
      public static specvar content :: objset;
      vardefs
        "content == {n. n ~= null & rtrancl_pt (% x y. x..Node.next=y) first n}";

      invariant "tree [Node.next]";

      invariant "first = null | (ALL n. n..Node.next ~= first)";
      
      invariant "ALL x n. x ~= null & n ~= null & x..Node.next = n --> n : content";

      private static specvar reach :: "obj => obj => bool";
      vardefs
        "reach == (% a b. rtrancl_pt (% x y. x..Node.next=y) a b)";

      invariant "ALL n. n : content & n..Node.next ~= null --> n..Node.key < n..Node.next..Node.key";

    */

    public static void add(Node nn)
    /*: requires "nn ~= null & nn ~: content"
        modifies content
        ensures "(content = old content Un {nn}) | (content = old content)"
    */
    {
        /*:
          private ghost specvar cnodes :: objset;
         */
        if (first==null) {
            first = nn;
            nn.next = null;
        } else {
            if (first.key==nn.key) {
                //: assume "False";
            } else if (first.key < nn.key) {
                Node prev = first;
                Node current = first.next;
                //: cnodes := "{first}";
                while /*: 
                        inv "(cnodes = {n. n ~= null & reach first n & ~ reach current n}) & (prev..Node.key < nn..Node.key) &
                        reach first prev & (prev ~= null) & (prev..Node.next = current) &                        
                        (ALL n. (n : cnodes) --> n..Node.key < nn..Node.key)"
                      */
                    ((current != null) && (current.key < nn.key)) {
                    prev = current;
                    //: cnodes := "cnodes Un {current}";
                    current = current.next;
                }
                nn.next = current;
                prev.next = nn;
                //: noteThat "content = old content Un {nn}";
            } else {
                nn.next = first;
                first = nn;
                //: noteThat "content = old content Un {nn}";
            }
        }
    }
}
