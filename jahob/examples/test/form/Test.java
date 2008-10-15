/* Testing formulas */

class Test {
    boolean ok;

    /*:
      invariant "ok --> (let x = 3 in (let y = 1 in x < y + x))"
     */

    public static void test() 
    /*:
      requires "~ ok"
      modifies ok
      ensures "ok"
    */
    {
	ok = true;
    }
}
