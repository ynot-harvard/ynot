public class Tree
{
   private static Node root;
   
   /*: public static specvar content :: objset;
       private vardefs "content == 
        {x. rtrancl_pt (% x y. x..Node.left = y | x..Node.right = y) root x}";
   
       invariant "tree [Node.left, Node.right]";
   
       invariant "root = null | (ALL n. n..Node.left ~= root & n..Node.right ~= root)";
   
       invariant "ALL x y. x ~= null & y ~= null & (x..Node.right = y | x..Node.left = y) --> y : content";

       //invariant "ALL x y. Node.parent x = y -->
       //              (x ~= null & (EX z. z..Node.left = x | z..Node.right = x) --> (y..Node.left = x | y..Node.right = x))
       //    & (x = null | (ALL z. z..Node.left ~= x & z..Node.right ~= x) --> y = null)";

   */
    
   public static void add(Node e, int v) 
      /*: 
	requires "e ~: content"
	modifies content
	ensures "content = old content Un {e}";
      */
   {
      Node n = root, p = null;
      boolean wentLeft = false;
      while (n != null) {
	 p = n;
	 if (v < n.v) {
	    wentLeft = true;
            n = n.left;
	 } else {
	    wentLeft = false;
	    n = n.right;
	 }
      }
      e.v = v;
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
   
   // The code below is just for debugging
   
   private static void openP() { System.out.print("("); }
   private static void closeP() { System.out.print(")"); }
   private static void println() { System.out.println(); }  
   public static void printFrom(Node n)
   {
     //openP();
     if (n != null) {
       printFrom(n.left);
       System.out.print(n.v + " ");
       printFrom(n.right);
     }
     //closeP();
   }  
   public static void print()
   {
     printFrom(root);
     println();
   }
}
 
