class Init {
    private static Object a[];
    private static int numNodes;

    public static void init(Object x) // initialize the array
    /*:
      requires "x ~= null"
      modifies "Array.arrayState"
      ensures "True";
     */
    {
        /*:
          private specvar bounds :: bool;
          private vardefs "bounds == (0 <= i) & (i <= numNodes) & (numNodes = a..Array.length)";

          private specvar content :: objset;
          private vardefs "content == {n. EX j. j >= 0 & j < numNodes & n = a.[j]}";

          private specvar content_i :: objset;
          private vardefs "content_i == {n. EX j. j >= 0 & j < i & n = a.[j]}";

          private specvar a_i :: obj;
          private vardefs "a_i == a.[i]";

          private specvar notnulls :: objset;
          private vardefs "notnulls == {n. n ~= null}";

          track(bounds);
          track(content);
         */
        numNodes = 100;
        // a = new Object[numNodes];
        //: assume "a ~= null & a..Array.length = numNodes";
        int i = 0;
        while /*: inv "0 <= i & i <= numNodes & 
                  (ALL k. 0 <= k & k < i --> a.[k] ~= null)" */
            (i < numNodes) {
            /*:
               track(bounds);
               track(content_i);
               track(content);
               track(a_i);
               track(notnulls);
             */
            a[i] = x;
            i = i + 1;
        }
        //: assert "ALL (k::int). 0 <= k & k < numNodes --> a.[k] ~= null";
    }
}
