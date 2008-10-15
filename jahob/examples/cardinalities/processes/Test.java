class Test {
  
    //: public static specvar total :: objset = "{}";
    //: public static specvar twosize :: int = "0";

    /*: vardefs 
          "total == Set1.content Un Set2.content";
          "twosize == card Set2.content";
    */

    public static void add1(Object o1) 
    /*: requires "o1 ~= null"
        modifies total
        ensures "total = old total Un {o1}";
    */
    {
        Set1.add(o1);
    }

    public static void add2(Object o1) 
    /*: requires "o1 ~= null"
        modifies total
        ensures "total = old total Un {o1} &
                 twosize = old twosize + 1";
    */
    {
        Set2.add(o1);
    }
}
