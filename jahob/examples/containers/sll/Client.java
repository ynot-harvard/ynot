class Client {
    public static void test() 
    /*: 
      modifies "List.content" 
      ensures "True";
    */
    {
        List l1 = new List();
        Object o1 = new Object();
        l1.add(o1);
        Object o2 = new Object();
        l1.add(o2);
        while //: inv "l1 ~= null"
         (!l1.empty()) {
            Object oa = l1.getOne();
            l1.remove(oa);
        }
        //: assert "l1..List.content = {}";
    }

    public static void test1() 
    /*: 
      modifies "List.content"
      ensures "True"
    */
    {
        List l1 = new List();
        Object o1 = new Object();
        l1.add(o1);
        Object o2 = new Object();
        l1.add(o2);
        //: ghost specvar oldL1 :: objset = "l1..List.content";
        List l2 = new List();
        while //: inv "l1..List.content Un l2..List.content = oldL1 & l1 ~= null"
         (!l1.empty()) {
            Object oa = l1.getOne();
            l1.remove(oa);
            l2.add(oa);
        }
        //: assert "l2..List.content = oldL1";
    }
}
