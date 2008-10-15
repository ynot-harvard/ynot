public /*: claimedby Map */ class List 
{
    private static Node first;
    private static Node current;

    //: public static specvar content :: objset
    //: invariant "acyclic_list (fg Node.next)"
    //: private vardefs "content == fg Node.data `` acyclic_list_content first (fg Node.next)"

    //: public static specvar iter :: objset
    //: private vardefs "iter == fg Node.data `` acyclic_list_content current (fg Node.next)"

    public static void add(Object o1)
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

    public static boolean empty()
    /*: ensures "result = (content = {})";
    */
    {
        return (first==null);
    }

    public static Object getOne()
    /*: requires "content ~= {}"
        ensures "result : content";
    */
    {
        return first;
    }

    public static void remove (Object o1)
    /*: requires "o1 : content"
        modifies content
	ensures "content = old content - {o1}"
     */
    {
        if (current != null && current.data==o1) {
            current = current.next;
        }
        if (first.data==o1) {
            first = first.next;
        } else {
            Node prev = first;
            Node current = first.next;
            boolean go = true;
            while (go && (current!=null)) {
                    if (current.data==o1) {
                        prev.next = current.next;
                        go = false; // must remove all ocurrences? or elems distinct
                    }
                    current = current.next;
            }
        }
    }

    public static void initIter()
    /*: modifies "List.iter" 
        ensures "List.iter = List.content"
    */
    {
        current = first;
    }

    public static Object nextIter()
    /*: 
      requires "iter ~= {}"
      modifies iter 
      ensures "result : old iter &
               iter = old iter - {result}"
    */
    {
        Object res = current.data;
        current = current.next;
        return res;
    }

    public static boolean isLastIter()
    //: ensures "result = (iter = {})"
    {
        return (current == null);
    }
}
