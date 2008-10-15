public final class List implements IterSet 
{

    private Node first;
    private Node iter;

    public void add(Object o1) //: requires "o1 ~= null";
    {
	Node n = new Node();
        n.content = o1;
        n.next = first;
        first = n;
    }

    public void remove (Object o1) {
        if (first!=null) {
            if (first.content==o1) {
                if (iter==first) {
                    iter = iter.next;
                }
                first = first.next;
            } else {
                Node prev = first;
                Node current = first.next;
		boolean go = true;
                while (go && (current!=null)) {
                    if (current.content==o1) {
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

    public static void main() {
	List list;
	list = new List();
	//	list.add(list);
	new List().add(list);
	// List.main();
    }
}
