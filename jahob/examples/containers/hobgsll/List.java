public class List 
{
   public static Node first;
   
   /*:
     private static specvar reach :: "obj => obj => bool";
     private vardefs "reach == 
     (% a b. rtrancl_pt (% x y. x..Node.next = y) a b)";

     public static specvar content :: objset;
     private vardefs "content == {x. reach first x}";

   
     invariant "first ~= null --> (ALL n. n..Node.next ~= first)";
   
     invariant "tree [Node.next]";
   */
    
   public static void reverse ()
      /*: modifies content
	ensures "content = old content";
      */
   {
      // assume "ALL x. x : content & x ~= null & x..Node.next ~= null --> x..Node.data <= x..Node.next..Node.data";
      Node t, e;
      e = first;
      first = null;
      while (e != null) {
	 t = first;
	 first = e;
	 e = e.next;
	 first.next = t;
      }
      // assert "ALL x. x : content & x ~= null & x..Node.next ~= null --> x..Node.next..Node.data <= x..Node.data";
   }

   public static void reverse_propagation ()
      /*: modifies content
	ensures "content = old content";
      */
   {
      /*:
	private specvar has_pred :: objset;
	private vardefs "has_pred == {x. ALL n. n..Node.next ~= x}";

	private specvar reach_e :: objset;
	private vardefs "reach_e == {x. reach e x}";

	assume "e = null | ~(reach first e)";

      */
      Node t, e;
      e = null;
      while (first != null) {
	 //: track(reach_e);
	 //: track(has_pred);
	 t = e;
	 e = first;
	 first = first.next;
	 e.next = t;
      }
      first = e;
   }
}
 
