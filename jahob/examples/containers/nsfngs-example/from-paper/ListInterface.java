class List 
{
    //: public static specvar content :: objset;

    public List()
    /*: 
      modifies content 
      ensures "content = {}"
    */
    {}

    public void add(Object o1)
    /*: 
      requires "o1 ~: content"
      modifies content
      ensures "content = old content Un {o1}"
    */
    {}

    public boolean empty()
    /*:
      ensures "result = (content = {})"
    */
    {}

    public Object getOne()
    /*: 
      requires "content ~= {}"
      ensures "result : content"
    */
    {}

    public void remove (Object o1)
    /*: 
      requires "o1 : content"
      modifies content
      ensures "content = old content - {o1}"
    */
    {}
}
