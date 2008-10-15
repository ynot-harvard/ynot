/* Problems:

-resolving List.first in requires clause etc.

TODO:
  -incorporate assumptions and make them be on-demand
  -fine-grained modifies

*/

public final class List 
    // List with 0,1, or 2 elements.
{
    private Node first;

    //: specvar content :: objset;
    //: vardefs "content == { n. n ~= null & (n = Node.data first | n = Node.data (Node.next first)) }";

    public void add(Object o1)
    // This method fails, because of Isabelle limitation, the condition can be proved manually
    /*: requires "o1 ~= null & 
                  (List.first this = null | 
                  (List.first this : alloc.Node &
                   Node.data (List.first this) : alloc.Object & Node.next (List.first this) = null))"
        modifies "content"
        ensures "List.content this = old (List.content this) Un {o1}"
    */
    {
        // This is not needed because it inserts at the beginning: 
        //   assume "ALL n. n : alloc.List & n ~= this --> List.first n ~= List.first this"
	Node n = new Node();
        n.data = o1;
        n.next = first;
        first = n;
    }

    public void add5(Object o1)
    // This method fails, because of Isabelle limitation, the condition can be proved manually
    /*: requires "o1 ~= null & 
                  (List.first this = null | 
                  (List.first this : alloc.Node &
                   Node.data (List.first this) : alloc.Object & Node.next (List.first this) = null))"
        modifies content
        ensures "List.content this = old (List.content this) Un {o1} &
                 (ALL n. n : alloc.List  & n ~= null & n ~= this --> List.content n = old (List.content n))"
    */
    {
        // This is not needed because it inserts at the beginning: 
        //   assume "ALL n. n : alloc.List & n ~= this --> List.first n ~= List.first this"
	Node n = new Node();
        n.data = o1;
        n.next = first;
        first = n;
    }

    public void add4(Object o1)
    /*: requires "o1 ~= null
                  & List.next (List.first this) = null"
        modifies content
        ensures "List.content this = old (List.content this) Un {o1} &
                 (ALL n. n : alloc.List & n ~= this --> List.content n = old (List.content n))"
    */
    {
	Node n = new Node();
        n.data = o1;
        n.next = first;
        first = n;
    }

    public void add3(Object o1)
    /*: requires "o1 ~= null & 
                  (List.first this = null | 
                  (List.first this : alloc.Node &
                   Node.data (List.first this) : alloc.Object & Node.next (List.first this) = null))"
        modifies content
        ensures "List.content this = old (List.content this) Un {o1} &
                 (ALL n. n : alloc.List & n ~= this --> List.content n = old (List.content n))"
    */
    {
        // This is not needed because it inserts at the beginning: 
        //   assume "ALL n. n : alloc.List & n ~= this --> List.first n ~= List.first this"
	Node n = new Node();
        n.data = o1;
        n.next = first;
        first = n;
    }

    public void add2(Object o1)
    /*: requires "o1 ~= null & 
                  List.first this : alloc.Node & 
                  Node.data (List.first this) : alloc.Object & 
                  Node.next (List.first this) = null"
        modifies content
        ensures "content = old content Un {o1}"
    */
    {
	Node n = new Node();
        n.data = o1;
        n.next = first;
        first = n;
    }

    public void add1(Object o1) //  | Node.next first = null)
    /*: requires "o1 ~= null & List.first this=null"
        modifies content
        ensures "content = old content Un {o1}"
    */
    {
        //: assume "null ~: alloc.Node";
        //: assume "ALL x. Node.next null = null";
        //: assume "ALL x. Node.data null = null";
	Node n = new Node();
        n.data = o1;
        n.next = first;
        first = n;
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
