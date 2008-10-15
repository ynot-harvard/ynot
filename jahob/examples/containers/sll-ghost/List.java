public final class List 
{
   private Node first;

   /*: 
     public specvar content :: objset;
     vardefs "content == {x. EX n. n : first..Node.nodes & x = n..Node.data}";

     public invariant ("ContentAlloc") "content \<subseteq> Object.alloc";

     private static specvar edge :: "obj => obj => bool";
     vardefs "edge == (% x y. (x : Node & y = x..Node.next) | 
                              (x : List & y = x..List.first))";

     invariant ("Inj") "ALL x1 x2 y.  y ~= null & edge x1 y & edge x2 y --> x1=x2";

   */

    public List()
    /*: 
      modifies content 
      ensures "content = {}"
    */
    {
        first = null;
        // "first..Node.nodes" := "{}";
    }

    public void add(Object o1)
    /*: modifies content
        ensures "content = old content Un {o1}"
    */
    {
	Node n = new Node();
        n.data = o1;
        n.next = first;
        //: noteThat "ALL x. ~(edge x n)";
        //: "n..Node.nodes" := "{n} Un first..Node.nodes";
        first = n;
    }

    public boolean isEmpty()
    /*: ensures "result = (content = {})";
    */
    {
        return (first==null);
    }

    public Object getOne()
    /*: requires "content ~= {}"
        ensures "result : content";
    */
    {
        return first.data;
    }

    public boolean member(Object o1)
    //: ensures "result = (o1 : content)";
    {
        Node current = first;
        while /*: inv "current : Object.alloc & current : Node &
                       (current ~= null --> (current..Node.nodes \<subseteq> first..Node.nodes)) & 
                       (ALL n. n : first..Node.nodes & n ~: current..Node.nodes --> n..Node.data ~= o1)"
               */
            (current != null) {
            if (current.data==o1) {
                return true;
            }
            current = current.next;
        }
        return false;
    }

    public void remove_iterative(Object o1)
    /*: modifies content
        ensures "content = old content \<setminus> {o1}";
    */
    {
        Node prev = null;
        Node current = first;
        /*: 
          ghost specvar init_nodes :: objset;
          assume "init_nodes = first..Node.nodes";
          ghost specvar to_remove :: objset;
          assume "to_remove = {n. n : init_nodes & n..Node.data = o1}";
          ghost specvar desired_nodes :: objset;
          assume "desired_nodes = init_nodes \<setminus> to_remove";
        */
        while 
            /*: inv "(current..Node.nodes \<subseteq> init_nodes) & 
                     (prev = null -->
                         first = current & 
                         (desired_nodes \<subseteq> current..Node.nodes)) &
                     (prev ~= null --> 
                         prev..Node.next = current & 
                         first..Node.nodes = desired_nodes) &
                     (ALL n. n : Node & n : Object.alloc & n ~= null & n ~= prev -->
                         n..Node.nodes = {n} Un n..Node.next..Node.nodes) &
                     (null..Node.nodes = {}) &
                     (ALL x1 x2 y.  y ~= null & edge x1 y & edge x2 y --> x1=x2)"
             */
            (current!=null) {

            //: assume "current : Node & current : Object.alloc";
            //: assume "prev : Node & prev : Object.alloc";

            //: assume "current ~= prev";
            //: assume "current ~= first";
            //: assume "prev ~= first";

            /*: "current..Node.nodes" := "desired_nodes"; */
            if (current.data==o1) {
                Node nxt = current.next;
                if (prev==null) {
                    // current should have no predecessors
                    first = nxt;
                } else {
                    prev.next = nxt;
                }
                current.next = null;
                //: "current..Node.nodes" := "{current}";
                current = nxt;
            } else {
                prev = current;
                current = current.next;
            }
        }
        /*:
          noteThat "first..Node.nodes = desired_nodes";
          assume "False";
        */
    }

    private static Node remove_helper(Node n, Object o1)
    /*:
      requires "(ALL n1. n1 : Object.alloc & n1 : Node & n1 ~= null & 
                         n1 : n..Node.nodes --> 
                   (n1..Node.nodes = {n1} Un n1..Node.next..Node.nodes) & 
                   (n1 ~: n1..Node.next..Node.nodes)) &
                null..Node.nodes = {} &
                (ALL x1 x2 y.  y ~= null & edge x1 y & edge x2 y --> x1=x2)"
      modifies "Node.next", "Node.nodes"
      ensures "result..Node.nodes = n..Node.nodes \<setminus> 
                                    {n1. n1..Node.data = o1} &
               (ALL n1. n1 : Object.alloc & n1 : Node & n1 ~= null & 
                         n1 : old (n..Node.nodes) --> 
                   (n1..Node.nodes = {n1} Un n1..Node.next..Node.nodes) & 
                   (n1 ~: n1..Node.next..Node.nodes)) &
                null..Node.nodes = {} &
                (ALL x1 x2 y.  y ~= null & edge x1 y & edge x2 y --> x1=x2) &
                (ALL n1. n : old Object.alloc & n ~: n..Node.nodes -->
                         Node.next n1 = (old Node.next) n1)"
     */
    {
        if (n==null) {
            return null;
        } else {
            Node nxt = n.next;
            if (n.data==o1) {
                n.next = null;
                //: "n..Node.nodes" := "{n}";
                return remove_helper(nxt, o1);
            } else {
                //: "n..Node.nodes" := "{n} Un nxt..Node.nodes";
                n.next = remove_helper(nxt, o1);
                return n;
            }
        }
    }

    public void remove(Object o1) // recursive
    /*: modifies content
        ensures "content = old content \<setminus> {o1}";
    */
    {
        first = remove_helper(first, o1);
    }

    public static void main(String[] args)
    {
        List l = new List();
        Object o1 = new Object();
        Object o2 = new Object();
        Object o3 = new Object();
        Object o4 = new Object();
        l.add(o1);
        l.add(o2);
        l.add(o3);
        l.add(o4);
        l.remove(o2);
        l.remove(o4);
        l.remove(o1);
        l.remove(o1);
        if (l.isEmpty()) {
            System.out.println("Oops, the list is empty but should have one element.");
        } else {
            System.out.println("ok1.");
        }
        l.remove(o3);
        if (!l.isEmpty()) {
            System.out.println("Oops, the list is not empty but should be.");
        } else {
            System.out.println("ok2.");
        }
    }
}
