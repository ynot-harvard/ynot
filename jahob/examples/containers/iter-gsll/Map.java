class Map {
    //: invariant "List.content <= alloc.Pair1"

    //: public static specvar map :: "(obj * obj) set"

    /***** alternative syntax
     vardefs "map == 
      {(x,y). EX n. n : List.content & x = n..Pair1.key & y = n..Pair1.value}" */

    /*: vardefs "map == 
      {p. EX n. n : List.content & p = (n..Pair1.key, n..Pair1.value)}" */
    
    /***** public invariant "ALL k v1 v2. 
      (k,v1) : map & (k,v2) : map --> v1=v2" */

    /*: invariant "ALL n1 n2. 
      n1 : List.content & n2 : List.content & n1..Pair1.key = n2..Pair1.key
      --> n1=n2" */

    //: invariant "List.iter <= List.content"

    //: invariant "null ~: List.content"

    public static void update(Object key, Object value)
    /*:
      requires "key ~= null & value ~= null"
      modifies map
      ensures "(key,value) : map &
               (ALL k v. k ~= key --> ((k,v) : map) = ((k,v) : old map))"
    */
    {
        List.initIter();
        while /*: inv "(List.content = old List.content) &
                       (List.iter <= List.content) &
                       (null ~: List.content) &
                       (List.content <= alloc.Pair1) &
                       (Pair1.key = old Pair1.key) &
                       (Pair1.value = old Pair1.value) &
(ALL n1 n2. 
   n1 : List.content & n2 : List.content & n1..Pair1.key = n2..Pair1.key
    --> n1=n2) &
                       (ALL n. n : (List.content - List.iter) --> 
                       n..Pair1.key ~= key)" */
            (!List.isLastIter()) {
            Pair1 pair1 = (Pair1) List.nextIter();
            if (pair1.key==key) {
                pair1.value = value;
                return;
            }
        }
        Pair1 pair2 = new Pair1();
        pair2.key = key;
        pair2.value = value;
        List.add(pair2);
    }
}
