// Instantitable set
class Set {
    //: public specvar content :: "obj set";
    //: public invariant "ALL x. (x : alloc.Object | x : alloc.Set) --> x..Object.owner ~= token.Set";

    public Set()
    /*: modifies content 
        ensures "content = {}"
    */
    {  }

    public void add(Object o1)
    /*: modifies content
        ensures "content = old content Un {o1}"
    */
    {  }

    public Object getOne()
    /*: requires "content ~= {}"
        ensures "result : content";  
    */
    {  }

    public void remove (Object o1)
    /*: requires "o1 : content"
        modifies content
	ensures "content = old content - {o1}"
    */
    {  }

    public boolean isEmpty()
    //: ensures "result = (content = {})";
    {  }

}
