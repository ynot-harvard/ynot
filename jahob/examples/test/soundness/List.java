public class List 
{
    private Node first;

    /*:
      // list of representation nodes:
      specvar nodes :: objset;
      private vardefs "nodes == { n. n ~= null & 
                                  rtrancl_pt (% x y. x..Node.next = y) first n}";

      // list content:
      public specvar content :: objset;
      private vardefs "content == {x. EX n. x = n..Node.data & n : nodes}";

      // 'first' is the beginning of the list:
      invariant "first = null | 
                (first : Object.alloc & 
                 (ALL n. n..Node.next ~= first & 
                         (n ~= this --> n..List.first ~= first)))";

      // next is acyclic and unshared:
      invariant "tree [List.first, Node.next]";

      // no sharing of data:
      invariant "ALL n1 n2. n1 : nodes & n2 : nodes & n1..Node.data = n2..Node.data
                        --> n1=n2";
    */

    public List()
    /*:
      modifies content
      ensures "content = {}"
    */
    {
        first=null;
    }
    
    public void add(Object o1)
    /*: requires "o1 ~: content"
        modifies content
        ensures "content = old content Un {o1}"
    */
    {
	Node n = new Node();
        n.next = first;
        first = n;
        n.data = o1;
    }

    public boolean empty()
    /*: ensures "result = (content={})"
    */
    {
        return (first==null);
    }

    public Object getOne()
    /*: requires "content ~= {}"
        ensures "result : content"
    */
    {
        return first.data;
    }

    public void remove (Object o1)
    /*: requires "o1 : content"
        modifies content
	ensures "content = old content \<setminus> {o1}"
     */
    {
        if (first.data==o1) {
            Node oldfirst = first;
            first = oldfirst.next;
            oldfirst.next = null;
        } else {
            Node prev = first;
            Node current = first.next;
            while (current.data!=o1) {
                prev = current;
                current = current.next;
            }
            prev.next = current.next;
            current.next = null;
        }
    }
}
