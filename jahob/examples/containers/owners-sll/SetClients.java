class SetClients {
    public static void move()
    //: modifies "Set.content"
    {
        //: assume "token.NoOwner ~= token.Set";
        Set s1 = new Set();

        Object o1 = new Object(); s1.add(o1);
        Object o2 = new Object(); s1.add(o2);

        Set s2 = new Set();

        //: specvar oldS1 :: objset = "s1..Set.content"
        while /*: inv "s1 ~= null & s2 ~= null & s1 ~= s2 &
                       s1 : alloc.Set & s2 : alloc.Set &
                       (ALL x. x..Object.owner = old (x..Object.owner)) &
                       (ALL x. (x : alloc.Object | x : alloc.Set) --> x..Object.owner ~= token.Set) &                       
                       (s1 .. Object.owner ~= token.Set) &
                       (s2 .. Object.owner ~= token.Set) &
                       token.NoOwner ~= token.Set &
                       s1..Set.content Un s2..Set.content = oldS1" */
         (!s1.isEmpty()) {
            Object obj = s1.getOne();
            //: specvar cA :: objset = "s2..Set.content";
            s1.remove(obj);
            //: noteThat "s2..Set.content = cA";
            //: specvar cB :: objset = "s1..Set.content";
            s2.add(obj);
            //: noteThat "s1..Set.content = cB";
        }
    }
}
