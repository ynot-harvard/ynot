class Relation {
    /* Interface of an instantiatable relation.

       Please ignore the implementation, this is just an interface.
     */

    /*: 
      public ghost specvar init :: bool;
      public specvar content :: "(obj * obj) set";
      vardefs "content == {}";
    */

    public Relation()
    /*:
      modifies content
      ensures "init & (content = {})"
     */
    {
    }
    
    public void add(Object x, Object y)
    /*:
      requires "init & x ~= null & y ~= null"
      modifies content
      ensures "content = old content Un {(x,y)}";
     */
    {
    }

    public void remove(Object x, Object y)
    /*:
      requires "init & x ~= null & y ~= null"
      modifies content
      ensures "content = old content \<setminus> {(x,y)}";
     */
    {
    }

    public Set image(Object x)
    /*:
      requires "init & x ~= null"
      ensures "result ~= null & result..Set.content = {y. (x,y) : content}";
     */
    {
        return null;
    }

    public Set inverseImage(Object y)
    /*:
      requires "init & y ~= null"
      ensures "result ~= null & result..Set.content = {x. (x,y) : content}";
     */
    {
        return null;
    }

    public Set domain()
    /*:
      requires "init"
      ensures "result ~= null & result..Set.content = {x. EX y. (x,y) : content}";
    */
    {
        return null;
    }
}
