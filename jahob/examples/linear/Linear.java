public class Linear {
    private static Node[] nodes;
    private static int numNodes; 

    /*: private static specvar funnyArray :: "int => bool";
        vardefs "funnyArray == (% (m::int).
          (ALL (j::int). (0::int) <= j & (j < m) --> 
              Linear.nodes.[j]..Node.x + 
              Linear.nodes.[j]..Node.y = numNodes))";

      	invariant "ALL k. 0 <= k & k < numNodes --> nodes.[k] ~= null";
	invariant "Array.length nodes = numNodes & numNodes > 0";


    */

    public static void main(String[] args)
    /*: modifies "Node.x", "Node.y", "Array.arrayState"
        ensures "True";
    */
    {
        numNodes = 10;
        nodes = new Node[numNodes];
        
        /* The following loop works because of context-aware loop invariant checking.
           Otherwise larger invariant would be needed.*/
        int i = 0;
        while //: inv "(0::int) <= i & i <= numNodes & comment ''interesting'' (funnyArray i)"
            (i < numNodes) {
            nodes[i] = new Node();
            nodes[i].x = i;
            nodes[i].y = numNodes - i;
            i = i + 1;
        }
        //: assert "funnyArray numNodes";
    }

   public static void noAlloc()
    /*: modifies "Node.x", "Node.y", "Array.arrayState"
      ensures "True";
    */
   {
      /*:
	private specvar numnodes :: bool;
	private vardefs "numnodes == Array.length nodes = numNodes & numNodes > 0";

	private specvar content :: objset;
	private vardefs "content == {n. EX j. j >= 0 & j < numNodes & n = nodes.[j]}";

	private specvar content_i :: objset;
	private vardefs "content_i == {n. EX j. j >= 0 & j < i & n = nodes.[j]}";

	private specvar sum :: objset;
	private vardefs "sum == {n. n..Node.x + n..Node.y = numNodes}";

	private specvar bounds :: bool;
	private vardefs "bounds == 0 <= i & i <= numNodes";

	private specvar nodes_i :: obj;
	private vardefs "nodes_i == nodes.[i]";

	track(content);
	track(numnodes);
      */

      int i = 0;
      while /* inv "0 <= i & i <= numNodes &
	      (ALL k. 0 <= k & k < numNodes --> nodes.[k] ~= null) &
	      (Array.length nodes = numNodes & numNodes > 0) &
	      (ALL n. (EX j. j >= 0 & j < i & nodes.[j] = n) --> n..Node.x + n..Node.y = numNodes)
	      "
	    */
	 (i < numNodes) {
	 /*:
	   track(nodes_i);
	   track(numnodes);
	   track(bounds);
	   track(content);
	   track(content_i);
	   track(sum);
	 */
	 nodes[i].x = i;
	 nodes[i].y = numNodes - i;
	 i = i + 1;
      }
      /*: assert "(ALL (j::int). (0::int) <= j & (j < numNodes) --> 
              Linear.nodes.[j]..Node.x + 
              Linear.nodes.[j]..Node.y = numNodes)";
      */
   }
}
