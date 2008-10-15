/* This was originally written to test vc generator 
   with dependent variable tracking and selective substitution.
*/
class Integer {
    private int n;
    
    //: public specvar nbr :: int;
    //:  vardefs "nbr == n";

 /*:
      public ghost specvar init :: bool;
      
      invariant "init --> n = nbr";
    */

    public Integer(int k)
    /*: modifies nbr, init
      ensures "init & nbr = k" */
    {
	n = k;        
	//: init := "fieldWrite init this True";

    }

    public int intValue()
     /*: requires "init"
         ensures "result = nbr" */
    {
	return n;
    }

}

