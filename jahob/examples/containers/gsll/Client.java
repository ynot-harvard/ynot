class Client {
    public static void test() 
    /*: 
      requires "List.content = {}"
      modifies "List.content" 
      ensures "True"
    */
    {
        Object o1 = new Object();
        //: assume "o1 ~: Node";
        List.add(o1);
        Object o2 = new Object();
        //: assume "o2 ~: Node";
        List.add(o2);
        while //: inv "True"
         (!List.empty()) {
            Object oa = List.getOne();
            List.remove(oa);
        }
    }
}
