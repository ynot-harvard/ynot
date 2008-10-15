class Abst {
    private static int value = 0;
    /*: specstatic oddity : "bool" = "false" */
    /*: vardefs "oddity == (value mod 2 = 0::int)" */


    public static void inc()
    /*: 
      requires "True"
      modifies oddity
      ensures "oddity = ~ (old oddity)"
    */
    {
	value = value + 1;
    }
}
