class Client {
    public static List a, b;

    /*:
      public static ghost specvar init :: bool;
      
      invariant "init --> a ~= null & b ~= null & a ~= b 
               & a : Object.alloc & b : Object.alloc"
	       
    */

    public Client()
    /*: 
      modifies "List.content", init 
      ensures "init"
    */
    {
        a = new List();
        b = new List();
        Object x = new Object(); a.add(x);
        Object y = new Object(); a.add(y);
        //: init := "True";
    }

    public static void move() 
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
	//: noteThat "n..Node.next = null & n..Node.next = n"
    }

    public static void moveAll() 
    /*: 
      requires "init & b..List.content = {}" 
      modifies "List.content" 
      ensures "a..List.content = {} & b..List.content = old (a..List.content)"
    */
    {
     
   while /*: inv "init & a..List.content Un b..List.content = old (a..List.content)
	               & a..List.content Int b..List.content = {}" */ 
       (!a.empty()) {
       Object oa = a.getOne();
       a.remove(oa);
       b.add(oa);
     }
    }


 public static void partition(List p) 
 /*: 
      requires "init & b..List.content = {} & a..List.content = {} & p ~= null & p ~= a & p~= b 
                     " 
      modifies "List.content" 
      ensures "a..List.content Un b..List.content = old (p..List.content) 
             & a..List.content Int b..List.content = {}"
    */
    {
	boolean which = false;
	while /*: inv "init & a..List.content Int b..List.content = {}
		     & (a..List.content Un p..List.content) Un b..List.content = old (p..List.content)
		     & a..List.content Int p..List.content = {}
		     & b..List.content Int p..List.content = {}
	      " */ (!p.empty()) 
	    {
		Object oa = p.getOne();
		p.remove(oa);
		

		if (which) b.add(oa); 
		else a.add(oa);
		
		which = !which;
	    }
    }

    public static void main(String[] args)
    {
        Client c = new Client();
        c.move();
    }
}
