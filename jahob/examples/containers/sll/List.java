public final class List 
{
   private Node first;

   /*: 
     private specvar inlist :: objset;
     private vardefs "inlist == {n. rtrancl_pt (% x y. Node.next x = y) first n & n ~= null}";

     public specvar content :: objset;
     vardefs "content == {x. x ~= null & (EX n. x = n..Node.data & n : inlist)}";

     // Type invariants
     invariant "ALL n. n ~: List --> n..List.first = null";
     invariant "ALL n. n ~: Node --> n..Node.next = null & n..Node.data = null";

     // Alloc invariant
     invariant "ALL n. n : Object.alloc  --> n..List.first : Object.alloc & n..Node.next : Object.alloc & n..Node.data : Object.alloc";

     invariant "ALL n. n : inlist --> n..Node.data ~= null";

     invariant "tree [List.first, Node.next]";
   */

    public List()
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
	//: noteThat "comment ''thisInlistInserted'' (inlist = old inlist Un {n})";
	//: noteThat "comment ''otherInlistSame''  (ALL (x::obj). x : Object.alloc & x : List & x ~= this --> x..List.inlist = old (x..List.inlist))";
	//: noteThat "comment ''nNotInOtherInlist'' (ALL (x::obj). x : Object.alloc & x : List & x ~= this --> n ~: (x..List.inlist))";
    }

    public void add1(Object o1)
    /*: requires "o1 ~= null"
        modifies content
        ensures "content = old content Un {o1}"
    */
    {
        // assume "ALL (n::obj). n : Object.alloc & n : List --> n..List.content \<subseteq> Object.alloc";
	Node n = new Node();
        n.data = o1;
        n.next = first;
        first = n;
	//: noteThat "comment ''thisContentInserted'' (inlist = old inlist Un {n})";
	//: noteThat "comment ''otherInlistSame''  (ALL (x::obj). x : Object.alloc & x : List & x ~= this --> x..List.inlist = old (x..List.inlist))";
	//: noteThat "comment ''nNotInOtherInlist'' (ALL (x::obj). x : Object.alloc & x : List & x ~= this --> n ~: (x..List.inlist))";
        //: noteThat "comment ''otherContentSame'' (ALL (x::obj). x : Object.alloc & x : List & x ~= this --> x..List.content = old (x..List.content))";
        //: assume "False";
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
