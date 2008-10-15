public class DLL
{
   private static Node root;
   
   /*: public static specvar content :: objset;
       private vardefs "content == 
        {x. rtrancl_pt (% x y. x..Node.next = y) root x}";
   
       invariant "tree [Node.next]";
   
       invariant "root = null | (ALL n. n..Node.next ~= root)";
   
       invariant "ALL x y. x ~= null & y ~= null & x..Node.next = y --> y : content";

       invariant "ALL x y. Node.prev x = y -->
                     (x ~= null & (EX z. z..Node.next = x) --> y..Node.next = x)
		   & (x = null | (ALL z. z..Node.next ~= x) --> y = null)";

   */
    

   public static void addLast(Node p)
      /*: 
	requires "p ~: content"
	modifies content
	ensures "content = old content Un {p}";
      */
   {
      if (root == null) {
        root = p;
        p.next = null; 
        p.prev = null;
        return;
      }

      Node r = root;
      while (r.next != null) {
	 r = r.next;
      }
      r.next = p; 
      p.prev = r;
      p.next = null; 
   }

}
 
