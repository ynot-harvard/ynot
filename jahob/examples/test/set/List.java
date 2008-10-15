public final class List implements IterSet 
{

    private Node first;
    private Node iter;

    public void add(Object o1) 
    /*: requires "o1 ~= null"
        modifies content
        ensures "(content this = ((old content) this \<union> {o1}))
	         ALL x. x ~= o1 --> content x = (old content) x";
    */
    {
	Node n = new Node();
        n.content = o1;
        n.next = first;
        first = n;
    }

    public void remove (Object o) {
        if (first!=null) {
            if (first.content==o) {
                if (iter==first) {
                    iter = iter.next;
                }
                first = first.next;
            } else {
                Node prev = first;
                Node current = first.next;
		boolean go = true;
                while (go && (current!=null)) {
                    if (current.content==o) {
                        if (iter==current) {
                            iter = iter.next;
                        }
                        prev.next = current.next;
                        go = false;
                    }
                    current = current.next;
                }
            }
        }
    }

    public void initIter() {
        iter = first;
    }

    public Object next() {
        if (iter!=null) {
            Node current = iter;
            iter = iter.next;
            return current.content;
        } else {
            return null;
        }
    }

    public static fakeInit() 
    /*: 
        modifies content
        ensures "content = {}";
    */
    {
    }

    public static fakeAdd(Object o1) 
    /*: 
        modifies content
        ensures "content = (old content) \<union> {o1}";
    */
    {
    }

    public static void main()
    /*: 
      requires "content = {}"
      ensures "content = (2::nat)";
    */
    {
	
    }
}
