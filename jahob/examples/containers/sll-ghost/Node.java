public /*: claimedby List */ class Node {
    public Object data;
    public Node next;
    /*: 
      public ghost specvar nodes :: objset = "{} :: objset";

      public invariant ("NodesAlloc") "nodes \<subseteq> Object.alloc";

      public invariant ("NodesNull") "this = null --> nodes = {}";   
      public invariant ("NodesDef") "this ~= null --> 
            (nodes = {this} Un next..nodes) &
            (this ~: next..nodes)";
    */
}
