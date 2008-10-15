/* The use of ghost variables.
*/

public class Ghost {
    //: public static ghost specvar S :: objset;
    //: public static ghost specvar A :: objset;
    //: public static ghost specvar B :: objset;

    //: public ghost specvar content :: objset;

    // invariant "S = A Un B";

    public static void addA(Object o1) 
    /*: requires "True"
        modifies A
        ensures "A = (old A) Un {o1}";
     */
    {
        //: A := "A Un {o1}";
    }

    public void addContent(Object o1)
    /*: requires "True"
        modifies "content"
        ensures "content = (old content) Un {o1}";
     */
    {
        //: content := "content  Un {o1}";
    }
}
