class Relation {
    /* Instantiatable relation. */

    private AssocList assoc;

    /*: 
      public specvar content :: "(obj * obj) set";
      vardefs "content == assoc..AssocList.content";

      public ensured invariant "ALL x y. (x,y) : content --> x : Object.alloc & y : Object.alloc";
    */

    public Relation()
    /*:
      modifies content
      ensures "content = {}"
     */
    {
        assoc = AssocList.nil();
    }
    
    public void add(Object x, Object y)
    /*:
      requires "x ~= null & y ~= null"
      modifies content
      ensures "content = old content Un {(x,y)}";
     */
    {
        assoc = AssocList.cons(x, y, assoc);
    }

    public void remove(Object x, Object y)
    /*:
      requires "x ~= null & y ~= null"
      modifies content
      ensures "content = old content \<setminus> {(x,y)}";
     */
    {
        assoc = AssocList.remove(x, y, assoc);
    }

    public Set image(Object x)
    /*:
      requires "x ~= null"
      ensures "result ~= null & result..Set.content = {y. (x,y) : content} &
               result ~: old Object.alloc";
     */
    {
        return Set.setOfFuncList(AssocList.image(x, assoc));
    }

    public Set inverseImage(Object y)
    /*:
      requires "y ~= null"
      ensures "result ~= null & result..Set.content = {x. (x,y) : content} &
               result ~: old Object.alloc";
     */
    {
        return Set.setOfFuncList(AssocList.inverseImage(y, assoc));
    }

    public Set domain()
    /*:
      ensures "result ~= null & result..Set.content = {x. EX y. (x,y) : content} &
               result ~: old Object.alloc";
    */
    {
        return Set.setOfFuncList(AssocList.domain(assoc));
    }
}
