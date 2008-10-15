public class SetIterBoundedArray {
    /* Implementation of a bounded set of objects */

    public /*: readonly */ int size;

    private Object[] a;

    /*: 
      public specvar content :: objset;
      public specvar maxSize :: int;
      public ghost specvar init :: bool;

      vardefs "maxSize == a..Array.length";
      vardefs "content == {n. EX i. 0 <= i & i < size & n = a.[i]}";

      public invariant "comment ''BasicIntegrity'' (init --> (0 <= size & size <= maxSize & null ~: content))";
      // When we add BAPA:
      // public invariant "init --> size = icard content";

      invariant "comment ''noDuplicates''
        (ALL this i j.
          this : SetIterBoundedArray & this : Object.alloc & this..init &
          0 <= i & i < j & j < this..size -->
          this..a.[i] ~= this..a.[j])";

      invariant "comment ''arraysDisjoint''
        (ALL ma1 ma2. (ma1 : Object.alloc) & (ma2 : Object.alloc) &
          (ma1 : SetIterBoundedArray) & (ma2 : SetIterBoundedArray) &
          ma1 ~= ma2 & ma1..a ~= null --> ma1..a ~= ma2..a)";
    */
    /*:
      invariant "comment ''valuesNonNull''
        (ALL this i.
           this : SetIterBoundedArray & this : Object.alloc & this..init &
           0 <= i & i < this..size --> this..a.[i] ~= null)";

      // invariant "ALL this. this..init --> (this..a ~= null & rep (this..a))";
    */

    public SetIterBoundedArray(int s) 
    /*:
      requires "0 < s"
      modifies init, content, size, maxSize
      ensures "maxSize = s & size = 0 & init";
     */
    {
        //: assume "ALL ma. ma : Object.alloc --> ma..a : Object.alloc";
        a = new Object[s];
        size = 0;
        //: init := "fieldWrite init this True";
        /*
          assert "comment ''sizeSet'' (maxSize = s)";
          assert "comment ''sizeZero'' (size = 0)";
        */
        // noteThat "comment ''otherASame'' (ALL tt. tt : SetIterBoundedArray & tt : Object.alloc & tt ~= this --> tt..a = old (tt..a))";
        // noteThat "comment ''otherAElemSame'' (ALL tt i. tt : SetIterBoundedArray & tt : Object.alloc & tt ~= this --> tt..a.[i] = old (tt..a.[i]))";
        // noteThat "comment ''othersSame'' (ALL tt. tt : SetIterBoundedArray & tt : Object.alloc & tt ~= this --> tt..content = old (tt..content))";
    }

    public void insert(Object x)
    /*:
      requires "init & x ~= null & x ~: content & (size < maxSize)"
      modifies content, size
      ensures "content = old content Un {x} & size = old size + 1";
     */
    {
        a[size] = x;
        size = size + 1;
        // assert "content \<subseteq> (old content Un {x})";
        // assert "(old content Un {x}) \<subseteq> content";
        //: noteThat "ALL ma. ma ~= this --> ma..a = old (ma..a) & ma..size = old (ma..size)";
        //: noteThat "ALL i. 0 <= i & i < size - 1 --> a.[i] ~= x";
        //: noteThat "ALL i j. 0 <= i & i < j & j < size --> a.[i] ~= a.[j]"
        //: noteThat "ALL ma i j. ma : Object.alloc & ma : SetIterBoundedArray & ma ~= this --> 0 <= i & i < j & j < ma..size --> ma..a.[i] ~= ma..a.[j]"
        //: noteThat "(old content Un {x}) = content";
        // assume "False";
    }

    public Object extract()
    /*:
      requires "init & 0 < size"
      modifies content, size
      ensures "result : content & content = old content - {result} & size = old size - 1";
     */
    {
        size = size - 1;
        return a[size];
    }
}
