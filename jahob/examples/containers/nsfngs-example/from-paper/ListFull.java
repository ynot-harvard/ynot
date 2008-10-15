public class List 
{
    private Node first;

    /*:
      // list of representation nodes:
      private static specvar nodes :: objset;
      private vardefs "nodes = { n. n ~= null & 
                                 rtrancl_pt (% x y. x..Node.next = y) first n};

      // list content:
      public static specvar content :: objset;
      private vardefs "content == {x. EX n. x = n..Node.data & n : nodes}";

      // next is acyclic and unshared:
      invariant "tree [List.first, Node.next]";

      // 'first' is the beginning of the list:
      invariant "first = null | 
                (first : Object.alloc & 
                 (ALL n. n..Node.next ~= first & n..Node.first ~= first))";

      // data is non-null:
      invariant "ALL n. n : nodes --> n..Node.data ~= null";

      // no sharing of data:
      invariant "ALL n1 n2. n1 : nodes & n2 : nodes & n1..data = n2..data
                        --> n1=n2";

    */

    public List()
    /*: 
      modifies content 
      ensures "content = {}"
    */
    {
    }

    public void add(Object o1)
    /*: requires "o1 ~: content & 
                  o1 ~= null"
        modifies content
        ensures "content = old content Un {o1}"
    */
    {
	Node n = new Node();
        n.data = o1;
        n.next = first;
        first = n;
    }

    public boolean empty()
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
        return first;
    }

    public void remove (Object o1)
    /*: requires "o1 : content"
        modifies content
	ensures "content = old content - {o1}"
     */
    {
        if (first!=null) {
            if (first.data==o1) {
                first = first.next;
            } else {
                Node prev = first;
                Node current = first.next;
		boolean go = true;
                while (go && (current!=null)) {
                    if (current.data==o1) {
                        prev.next = current.next;
                        go = false;
                    }
                    current = current.next;
                }
            }
        }
    }
}
