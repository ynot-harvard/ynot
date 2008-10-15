public class Skiplist 
{
   private static Node root;
   
   /*: 
     public static specvar content :: objset;
     
     private static specvar reach :: "obj => obj => bool";
     vardefs "reach == (% a b. rtrancl_pt (% x y. x..Node.next = y) a b)";
 
     private vardefs "content == {x. reach root x}";
   
     invariant "tree [Node.next]";
   
     invariant "ALL x y. Node.nextSub x = y --> ((x = null --> y = null) 
                           & (x ~= null --> reach (Node.next x) y))";

     invariant "ALL x. x ~= null & ~(reach root x) --> 
                  ~(EX y. y ~= null & Node.next y = x) & (Node.next x = null)";

     invariant "root ~= null";
   */
   
   public static void add(Node e) 
      /*: requires "e ~: content"
	modifies content
	ensures "content = old content Un {e}"
      */
   {
      int v = e.v;
      Node sprev = root;
      Node scurrent = root.nextSub;

      while ((scurrent != null) && (scurrent.v < v)) {
	 sprev = scurrent;
	 scurrent = scurrent.nextSub;
      }
      // found place in sublist, now search from
      // sprev to scurrent in list
      Node prev = sprev;
      Node current = sprev.next;
      while ((current != scurrent) && (current.v < v)) {
	 prev = current;
	 current = current.next;
      }
      e.next = current;
      prev.next = e;

      if(v > 0) {
	 sprev.nextSub = e;
	 e.nextSub = scurrent;
      } else {
	 e.nextSub = null;
      }
   }
   
}
