public class MapArray {
    /* This map implements a functional relation from keys to non-null values */

    /* This is simplified implementation where keys are not sorted and
       removal requires shifting all elements. */

    public /*: readonly */ int size;

    private Node[] a;

    /*: 
      public specvar map :: "(obj * obj) set";
      public specvar maxSize :: int;

      vardefs "maxSize == a..Array.length";
      vardefs "map == {(k,v). EX (i::int) (n::obj). 
                 0 <= i & i < size & n = a.[i] & n ~= null &
                   k = n..Node.key & v = n..Node.value}";

      public invariant "size <= maxSize";
      public invariant "ALL k v. (k,v) : map --> k ~= null & v ~= null";

      invariant "comment ''noDuplicates''
        (ALL (this::obj) (i::int) (j::int) (ni::obj) (nj::obj).
          this : MapArray & this : Object.alloc &
          0 <= i & i < this..size & 0 <= j & j < this..size &
          ni = this..a.[i] & nj = this..a.[j] &
          ni..Node.key = nj..Node.key --> i=j)";

      invariant "comment ''arraysDisjoint''
        (ALL ma1 ma2 n1 i j. (ma1 : Object.alloc) & (ma2 : Object.alloc) &
          (ma1 : MapArray) & (ma2 : MapArray) &
          0 <= i & i < ma1..size &
          0 <= j & j < ma2..size &
          n1 = ma1..a.[i] & n1 ~= null & n1 = ma2..a.[j] 
       --> ma1 = ma2)";

      invariant "comment ''valuesNonNull''
        (ALL (this::obj) (i::int) (n::obj).
           this : MapArray & this : Object.alloc &
           0 <= i & i < this..size & n = this..a.[i] --> 
             n ~= null & n..Node.key ~= null & n..Node.value ~= null)";

      invariant "a ~= null & rep a";
    */
    
    public MapArray(int s) 
    /*:
      modifies map, size, maxSize
      ensures "maxSize = s & size = 0";
     */
    {
        //: assume "ALL ma. ma : Object.alloc --> ma..a : Object.alloc";
        a = new Node[s];
        //: incorporate(a);
        size = 0;
        /*:
          assert "comment ''sizeSet'' (maxSize = s)";
          assert "comment ''sizeZero'' (size = 0)";
        */
        //: noteThat "comment ''otherASame'' (ALL tt. tt : MapArray & tt : Object.alloc & tt ~= this --> tt..a = old (tt..a))";
        //: noteThat "comment ''otherAElemSame'' (ALL tt i. tt : MapArray & tt : Object.alloc & tt ~= this --> tt..a.[i] = old (tt..a.[i]))";
        //: noteThat "comment ''othersSame'' (ALL tt. tt : MapArray & tt : Object.alloc & tt ~= this --> tt..map = old (tt..map))";
    }

    public Object lookup(Object key)
    /*:
      requires "key ~= null"
      ensures "(result ~= null --> (key,result) : map) &
               (result = null --> (ALL value. (key,value) ~: map))";
     */
    {
        int i = 0;
        while /*: inv "0 <= i & (ALL j. 0 <= j & j < i --> a.[j]..Node.key ~= key)" */
            (i < size) {
            if (a[i].key==key) {
                return a[i].value;
            }
            i = i + 1;
        }
        return null;
    }

    public void update(Object key, Object value)
    /*:
      requires "key ~= null & value ~= null & 
                ((key,value) ~: map --> size < maxSize)"
      ensures "map = (old map \<setminus> {(k,v). k=key}) 
                     Un {(key,value)}";
     */
    {
        int i = 0;
        while /*: inv "0 <= i & (ALL j. 0 <= j & j < i --> a.[j]..Node.key ~= key)" */
            (i < size) {
            if (a[i].key==key) {
                a[i].value = value;
                return;
            }
            i = i + 1;
        }
        a[size] = new Node();
        a[size].key = key;
        a[size].value = value;
        size = size + 1;
    }

    public static void main(String[] args) {
        MapArray ma = new MapArray(10);
        String charles = "Charles";
        ma.update(charles, new Integer(22));
        String viktor = "Viktor";
        ma.update(viktor, new Integer(29));
        String karen = "Karen";
        ma.update(karen, new Integer(25));
        if (((Integer)(ma.lookup(viktor))).intValue()==29) {
            System.out.println("Viktor's age is correct (for now).");
        } else {
            System.out.println("Viktor's age is wrong.");
        }        
    }
}
