class Soundness {
    public static List a, b;

    /*:
      public static ghost specvar init :: bool;
      
      invariant "init --> a ~= null & b ~= null & a ~= b 
               & a : Object.alloc & b : Object.alloc";
    */

    public Soundness()
    /*: 
      modifies "List.content" 
      ensures "init"
    */
    {
        a = new List();
        b = new List();
        Object x = new Object(); a.add(x);
        Object y = new Object(); a.add(y);
        //: init := "True";
    }

    // supposed to succeed
    public static void test0() 
	/*: 
	  requires "init" 
	  ensures "False"
	*/
    {
    }

    // supposed to succeed
    public static void test1() 
    /*: 
      requires "init" 
      modifies "Node.next" 
      ensures "True"
    */
    {
	Node n = new Node();
	if (1+1 ==2) 
	    n.next = null;
	else
	    n.next = n;
	//: noteThat "n..Node.next = null | n..Node.next = n"
    }


    // supposed to fail
    public static void test2() 
    /*: 
      requires "init" 
      modifies "Node.next" 
      ensures "True"
    */
    {
	Node n = new Node();
	if (1+1==3) 
	    n.next = null;
	else
	    n.next = n;

	//: noteThat "n..Node.next = null & n..Node.next = n"
    }

    
    // supposed to succeed
    public static void test3(Node n) 
	/*: 
	  requires "init & n ~= null" 
	  modifies "Node.next" 
	  ensures " n..Node.next = n | 1+1=3"
	*/
    {
	if (n == null) 
	    n.next = null;
	else
	    n.next = n;
    }

 // supposed to fail
    public static void test4(Node n) 
	/*: 
	  requires "init & n ~= null" 
	  modifies "Node.next" 
	  ensures " n..Node.next = n & 1+1=2"
	*/
    {
	if (n == null) 
	    n.next = null;
	else
	    n.next = n;
    }

    // supposed to fail
    public static void test5() 
    /*: 
      requires "init" 
      ensures "True"
    */
    {
	//: assume "1+1 = 2*3"
	Node n = new Node();
	//: assert "n=null"
    }

    // supposed to succeed
    public static void test6() 
    /*: 
      requires "init" 
      ensures "True"
    */
    {
	//: assume "1+1 = 2*3"
	Node n = new Node();
	//: assert "n~=null"
    }


    // supposed to succeed
    public static void test7() 
    /*: 
      requires "init" 
      ensures "True"
    */
    {
	Node n = new Node();
	//: assert "n ~: a..List.content"
    }

   // supposed to succeed : exercices function symbols
    public static void test8() 
    /*: 
      requires "init" 
      modifies "Node.next" 
      ensures "True"
    */
    {
	//: ghost specvar f :: "obj => obj"
	Node n = new Node();
	//: assume "n = (f n)"

	n.next = n;

	//: assert "(f (n..Node.next)) = n..Node.next"
    }

 // supposed to fail : exercices function symbols
    public static void test9() 
    /*: 
      requires "init" 
      modifies "Node.next" 
      ensures "True"
    */
    {
	//: ghost specvar f :: "obj => obj"
	Node n = new Node();
	//: assume "n = (f n)"

	n.next = null;

	//: assert "(f (n..Node.next)) = n"
    }

    // supposed to succeed : exercices pairs
    public static void test10() 
    /*: 
      requires "init" 
      modifies "Node.next" 
      ensures "True"
    */
    {
	//: ghost specvar g :: "obj * obj"
	Node n = new Node();
	//: assume "g = (n,null)"

	n.next = null;

	//: assert "fst g = n & snd g = null"
    }

    // supposed to fail : exercices pairs
    public static void test11() 
    /*: 
      requires "init" 
      modifies "Node.next" 
      ensures "True"
    */
    {
	//: ghost specvar g :: "obj * obj"
	Node n = new Node();
	//: assume "g = (n,null)"

	n = n.next;

	//: assert "fst g = n & snd g = null"
    }

    // exercises arrays. Supposed to succeed.
    public static void test12() 
    /*:
        requires "True"
        modifies "Array.arrayState"
        ensures "True"
    */
    {	
	int[] bar1 = new int[30];

        bar1[7] = 2;
        //: assert "bar1.[7] = 2";
    }

 // exercises arrays. Supposed to fail.
    public static void test13() 
    /*:
        requires "True"
        modifies "Array.arrayState"
        ensures "True"
    */
    {	
	Object[] bar1 = new Object[30];

        bar1[7] = null;
        //: assert "bar1.[7] ~= null";
    }

  // exercises set comprehension. Supposed to succeed.
    public static void test14() 
    /*:
        requires "True"
        modifies "Array.arrayState"
        ensures "True"
    */
    {	
	Node n = new Node();

        //: assert "{x. n = null} = {}";
    }

 // exercises set comprehension. Supposed to succeed.
    public static void test15() 
    /*:
        requires "True"
        modifies "Array.arrayState"
        ensures "True"
    */
    {	
	Node n1 = new Node();
	Node n2 = new Node();

        //: assert "{n1, n2} \<subseteq> {x. x..Node.next = null}";
    }

 // exercises set comprehension. Supposed to fail.
    public static void test16() 
    /*:
        requires "True"
        modifies "Array.arrayState"
        ensures "True"
    */
    {	
	Node n1 = new Node();
	Node n2 = new Node();
	n2.next = n1;

        //: assert "{n1, n2} \<subseteq> {x. x..Node.next = null}";
    }


// exercises integers. Supposed to succeed.
    public static void test17() 
    /*:
        requires "True"
        modifies "Array.arrayState"
        ensures "True"
    */
    {	
	Node n1 = new Node();
	Node n2 = new Node();

        //: assert "3 < 5";
    }

// exercises integers. Supposed to succeed.
    public static void test18(int a, int b, int c) 
    /*:
        requires "True"
        modifies "Array.arrayState"
        ensures "True"
    */
    {	
	int d = a; 
	int e;
	if (b > a) d = b; // d=max(a,b)
	if (c > a && c > b) 
	    e = c;
	else
	    e = d;
	
        //: assert "e >= a & e >= b";
    }


}
