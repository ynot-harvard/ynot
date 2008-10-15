public class DLLIter 
{
   private static Node first, current;
   
   /*: public static specvar content :: objset;
       public static specvar iter :: objset;
       private vardefs "content == 
        {x. x ~= null & rtrancl_pt (% x y. x..Node.next = y) first x}";
   
       private vardefs "iter == 
        {x. x ~= null & rtrancl_pt (% x y. x..Node.next = y) current x}";
   
       public invariant "comment ''iterInCont'' (iter <= content)";
   
       invariant "tree [Node.next]";
   
       invariant "ALL x y. Node.prev x = y --> (x ~= null & (EX z. Node.next z = x) --> Node.next y = x) 
                        & (((ALL z. Node.next z ~= x) | x = null) --> y = null)";
  
   
       invariant "first = null | (ALL n. n..Node.next ~= first)";
   
   
       invariant "ALL x n. x ~= null & n ~= null & x..Node.next = n --> n : content";
   */
    
   public static void add(Node n)
      /*: requires "n ~: content & n ~= null"
        modifies content
        ensures "comment ''elementInserted'' (content = old content Un {n})"
      */
   {
      if (first == null) {
	 first = n;
	 n.next = null;
	 n.prev = null;
      } else {
	 n.next = first;
	 first.prev = n;
	 n.prev = null;
	 first = n;
      }
   }
   
   public static void remove(Node n)
      /*: requires "n : content"
        modifies content, iter
        ensures "comment ''elementRemoved'' (content = old content - {n} & iter = old iter - {n})"
      */
   {
      if (n==current) {
	 current = current.next;
      }
      if (n==first) {
	 first = first.next;
      } else {
	 n.prev.next = n.next;
      }
      if (n.next != null) {
	 n.next.prev = n.prev;
      }
      n.next = null;
      n.prev = null;
   }

   public static void initIter()
      /*: modifies iter 
        ensures "comment ''initIter'' (iter = content)"
      */
   {
      current = first;
   }

   public static Node nextIter()
      /*: requires "EX x. x : iter" 
        modifies iter 
	ensures "comment ''nextIter'' (iter = old iter - {result} & result : old iter)"
      */
    {
      Node n;
      n = current;
      current = current.next;
      return n;
   }

   public static boolean lastIter()
      //: ensures "comment ''iterEmpty'' (result = (iter = {}))"
   {
      return current == null;
   }
}
