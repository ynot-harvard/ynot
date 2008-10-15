public class Set {
    /* Interface of a bounded set of objects.

       Please ignore the implementation, this is just an inteface.*/

    /*: 
      public specvar content :: objset;
      public ghost specvar init :: bool;
      vardefs "content == {}";
    */

    public Set() 
    /*:
      modifies init, content
      ensures "init & content = {}";
     */
    {
    }

    public boolean isEmpty()
    /*:
      requires "init"
      ensures "result = (content = {})";
     */
    {
        return false;
    }

    public void insert(Object x)
    /*:
      requires "init & x ~= null & x ~: content"
      modifies content
      ensures "content = old content Un {x}";
     */
    {
    }

    public Object extract()
    /*:
      requires "init & content ~= {}"
      modifies content
      ensures "result : content & content = old content - {result}";
     */
    {
        return null;
    }
}
