public final class List 
{
   private Node first;
   /*: 
     public static specvar fclosure :: "(obj => obj) => obj => obj => bool";
     public vardefs "fclosure == (% (f :: obj => obj). rtrancl_pt (% x y. f x = y))"

     private specvar inlist :: objset;
     vardefs "inlist == {n. fclosure Node.next first n & n ~= null}";

     public specvar content :: objset;
     vardefs "content == {x. x ~= null & (EX n. x = n..Node.data & n : inlist)}";
				
     invariant "tree [List.first, Node.next]";
   */

   public void init()
   //: modifies content ensures "ALL x. x ~: content"
   {
      first = null;
   }

    public void add(Object o1)
    /*: requires "o1 ~= null"
        modifies content
        ensures "content = old content Un {o1}"
    */
    {
	Node n = new Node();
        n.data = o1;
        n.next = first;
        first = n;
	//: noteThat "inlist = old inlist Un {n}";
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
