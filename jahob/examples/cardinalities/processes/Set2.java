public /*: claimedby Test */ class Set2
{
    //: static specvar content :: objset = "{}";

    public static void add(Object o1)
    /*: requires "o1 ~= null"
        modifies content
        ensures "content = old content Un {o1}"
    */
    {
    }

    public static void remove (Object o1)
    /*: requires "o1 : content"
        modifies content
	ensures "content = old content - {o1}"
     */
    {
    }
}
