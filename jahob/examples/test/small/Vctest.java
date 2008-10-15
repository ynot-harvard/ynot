/* This was originally written to test vc generator 
   with dependent variable tracking and selective substitution.
 */
class Vctest {
    public static int x;
    public static int y;
    public static int z;
    
    /*:
      public static specvar sum :: int;
      vardefs "sum == x + y";

      public static specvar S :: "int set";
      vardefs "S == {x, y}";
     */

    public static void main()
    //: modifies sum, S ensures "sum > 0";
    {
        x = 3;
        y = x + 6;
        //: assert "sum = 12";
    }

    public static void init()
    //: modifies S, sum ensures "S = {0}";
    {
        x = 0;
        y = 0;
    }

    public static void first()
    //: requires "S = {0}" modifies S, sum ensures "S = {1,3}";
    {
        x = x + 1;
        y = x + 2;
    }

    public static void unreachable()
    //: ensures "True";
    {
        if (x == 1) return;
        //: assert "x ~= 1";
    }

    public static void reachable()
    //: ensures "True";
    {
        if (x == 1) {};
        //: assert "x ~= 1";
    }

 public static int caller()
    /*: 
	ensures "result = sum"; */
    {
	List l = new List();
	Integer i = new Integer(x);
	Integer j = new Integer(y);
	l.add(i);
	l.add(j);


	Integer k1 = (Integer) l.getOne();
        l.remove(k1);

	Integer k2 = (Integer) l.getOne();
	l.remove(k2);

        //: noteThat "False";

	//: assert "l..List.content = {}"
	
	return (k1.intValue()+k2.intValue());
    }

}
