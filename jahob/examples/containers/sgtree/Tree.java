public class Tree
{
   private static Node root;
   
   /*: public static specvar content :: objset;
       private vardefs "content == 
        {x. rtrancl_pt (% x y. x..Node.left = y | x..Node.right = y) root x}";
   
       invariant "tree [Node.left, Node.right]";
   
       invariant "root = null | (ALL n. n..Node.left ~= root & n..Node.right ~= root)";
   
       invariant "ALL x y. x ~= null & y ~= null & (x..Node.right = y | x..Node.left = y) --> y : content";

       //invariant "ALL x y. Node.prev x = y -->
       //              (x ~= null & (EX z. z..Node.next = x) --> y..Node.next = x)
       //	   & (x = null | (ALL z. z..Node.next ~= x) --> y = null)";

   */
    
   public static void add(Node e, int v)
      /*: 
	requires "e ~: content"
	modifies content
	ensures "content = old content Un {e}";
      */
   {
      /*:
	private specvar reach_n :: objset;
	private vardefs "reach_n == {x. rtrancl_pt (% v1 v2. v1..Node.left = v2 | v1..Node.right = v2) n x}";

	private specvar leaf :: objset;
	private vardefs "leaf == {x. x..Node.left = null & x..Node.right = null}";

	private specvar wentleft :: bool;
	private vardefs "wentleft == p ~= null --> (wentLeft & p..Node.left = n) | (~wentLeft & p..Node.right = n)";

	track(leaf);
      */
      e.v = v;
      e.left = null; e.right = null; //e.parent = null;
      Node n = root, p = null;
      boolean wentLeft;
      while 
          /*:
            inv "(p ~= null --> (wentLeft & p..Node.left = n) | (~wentLeft & p..Node.right = n)) &
                 (n ~= null --> n : content)"
           */
          (n != null) {
	 /*:
	   track(leaf);
	   track(reach_n);
	   track(wentleft);
	 */
	 p = n;
	 if (v < n.v) {
	    wentLeft = true;
            n = n.left;
	 } else {
	    wentLeft = false;
	    n = n.right;
	 }
      }
      if (p == null) {
	 root = e;
      } else {
	 //e.parent = p;
	 if (wentLeft) {
            p.left = e;
	 } else {
            p.right = e;
	 }
      }
   }
}
 
