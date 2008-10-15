class Client {
    List a, b;

    /*:
      public ghost specvar init :: bool;
      
      invariant "init --> 
                   a ~= null & b ~= null &
                   a..List.content Int b..List.content = {}";
    */

    public Client()
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

    public void move() 
    /*: 
      requires "init" 
      modifies "List.content" 
      ensures "a..List.content = {}"
    */
    {
        while (!a.empty()) {
            Object oa = a.getOne();
            a.remove(oa);
            b.add(oa);
        }
    }

    public static void main(String[] args)
    {
        Client c = new Client();
        c.move();
    }
}
