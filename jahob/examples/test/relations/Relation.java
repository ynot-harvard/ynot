class Relation {
    //: public specvar r :: "(obj * obj) set" = "{}";

    public void add(Object x, Object y)
    /*: requires "True"
        modifies r
        ensures r = (old r) Un {(x,y)};
     */
    {
    }

    public void remove(Object x, Object y)
    /*: requires "True"
        modifies r
        ensures r = (old r) - {(x,y)};
     */
    {
    }

    public Object getOne(Object x)
    /*: requires "EX y. (x,y) : r"
        ensures "result ~= null & (x,result) : r";
    */
    {
        return null;
    }

    public void removeFrom(Object x)
    /*: requires "True"
        modifies r
        ensures r = (old r) - {p. EX y. p=(x,y)};
     */
    {
    }

}
