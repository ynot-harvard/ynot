public final class List 
{
    private Node first;

    //: specvar content :: objset
    //: invariant "tree [Node.next]"
    //: vardefs "content == fg Node.data `` rtrancl (fg Node.next) `` {first}" 

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
    }

    public boolean isEmpty()
    /*: ensures "result = (EX x. x : result)";
     */
    {
        return first == null;
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
