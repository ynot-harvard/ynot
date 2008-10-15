// Instantitable set details

class Node {
    public /*: claimedby List */ Object data;  
    public /*: claimedby List */ Node next;
}

class Set {
    private Node first;

    //: public specvar content :: "obj set";
    //: invariant "acyclic_list Node.next";
    /*: vardefs "content == {x. EX n. x = n..Node.data & 
                                fclosure Node.next first n}" */

    public Set()
    /*: modifies content 
        ensures "content = {}"
    */
    { ... }

    public void add(Object o1)
    /*: requires "o1 ~= null"
        modifies content
        ensures "content = old content Un {o1}"
    */
    { ... }

    public Object getOne()
    /*: requires "content ~= {}"
        ensures "result : content";  
    */
    { ... }

    public void remove (Object o1)
    /*: requires "o1 : content"
        modifies content
	ensures "content = old content - {o1}"
    */
    { ... }


    public boolean isEmpty()
    //: ensures "result = (content = {})";
    { ... }
}
