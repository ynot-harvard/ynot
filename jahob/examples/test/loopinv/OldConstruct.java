class Test {
    static int x;
    static int y; 

    public static void foo()
    /*: 
      requires "x >= 0"
      modifies x, y
      ensures "y = old (x + y)  &  x = 0";
    */
    {
        while //: inv "x + y = old (x + y) & x >= 0"
            (x > 0) {
            x = x - 1;
            y = y + 1;
        }        
    }

    public static void bar()
    /*: 
      requires "x >= 0 & y = 0"
      modifies x, y
      ensures "y = old x & x = 0";
    */
    {
        while
            (x > 0) {
            x = x - 1;
            y = y + 1;
        }        
    }
}
