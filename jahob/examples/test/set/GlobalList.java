public final class GlobalList implements GlobalSet
{

    private static Node first;
    public static int size;

    public void init()
    {
	first = null;
    }

    public void add(Object o1) 
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

    public static void testaddremove()
    /*:
        requires "size = card GlobalSet.setContent & 
	          alloc.Object Int GlobalSet.setContent = {}"
	modifies "GlobalSet.setContent", "size"
	ensures "size = (old size) + 1 & 
	         size = card GlobalSet.setContent"
     */
    {	
	GlobalSet s = new GlobalList();
	Object o1 = new Object();
	s.add(o1);
	size = size + 1;
	Object o2 = new Object();
	s.add(o2);
	size = size + 1;
	s.remove(o1);
	size = size - 1;
    }

    public static void testadd()
    /*:
        requires "size = card GlobalSet.setContent & 
	          alloc.Object Int GlobalSet.setContent = {}"
	modifies "GlobalSet.setContent", "size"
	ensures "size = (old size) + 2 & 
	         size = card GlobalSet.setContent"
     */
    {	
	GlobalSet s = new GlobalList();
	Object o1 = new Object();
	s.add(o1);
	Object o2 = new Object();
	s.add(o2);
	size = size + 2;
    }
}
