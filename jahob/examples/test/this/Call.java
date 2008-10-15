class Call {
    int x;
    A a1;

    public void foo(Call c) 
    //: requires "c ~= null" modifies "c..x" ensures "c..x=7"
    { 
        c.x = 7;
    }

    public void test1() 
    //: modifies x ensures "x=7"
    {
        foo(this);
    }

    public void test(int y) 
    /*: 
      requires "a1 ~= null" 
      modifies "a1..A.aha" 
      ensures "a1..A.aha = old (a1..A.aha) + y"
    */
    {
        a1.change(y);
    }
}
