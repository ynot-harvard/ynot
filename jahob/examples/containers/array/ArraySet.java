class ArraySet {
    private static Object[] a;
    public  static int size;

    /*:
      public static ghost specvar init :: bool;

      public static specvar content :: objset;
      vardefs
        "content == {n. EX j. n = a.[j] & 0 <= j & j < size}";

      invariant "init --> a ~= null & 0 < a..Array.length & 
          0 <= size & size <= a..Array.length";

      invariant ("a is part of private rep") "init --> a : hidden"
    */

    public static void initialize() 
    /*:
      modifies init, content
      ensures "init & content = {}";
    */
    {
        a = new /*: hidden */ Object[100];
        size = 0;
        //: init := "True";
    }

    public static void add(Object x)
    /*:
      requires "init & x ~: content"
      modifies content, "Array.arrayState"
      ensures "(content = old content Un {x})"
    */
    {
        if (size < a.length) {
            a[size] = x;
            size = size + 1;
        } else {
            //: assume "False" 
	    Object[] b = new Object[2 * a.length];
            int i = 0;
            while (i < a.length) {
                b[i] = a[i];
                i = i + 1;
            }
            b[size] = x;
            size = size + 1;
            a = b;
        }
    }

    public static boolean contains(Object x)
    /*:
      requires "init & x ~= null"
      ensures "result = (x : content)";
     */
    {
       /*: private specvar content_i :: objset;
	 private vardefs "content_i == {n. EX j. j >= 0 & j < i & n = a.[j]}";

	 private specvar bounds :: bool;
	 private vardefs "bounds == 0 <= i & i <= size";

	 private specvar a_i :: obj;
	 private vardefs "a_i == a.[i]";

	 track(content);
       */
        int i = 0;
        while (i < size) {
	   /*:
	     track(bounds);
	     track(content);
	     track(content_i);
	     track(a_i);
	    */
            if (a[i] == x) {
                return true;
            } else {
                i = i + 1;
            }
        }
        return false;
    }

    public static boolean containsVC(Object x)
    /*:
      requires "init & x ~= null"
      ensures "result = (x : content)";
     */
    {
	// private vardefs "content_i == {n. EX j. j >= 0 & j < i & n = a.[j]}";
	/*: private static ghost specvar content_i :: objset;

	 private specvar bounds :: bool;
	 private vardefs "bounds == 0 <= i & i <= size";

	 private specvar a_i :: obj;
	 private vardefs "a_i == a.[i]";

	 track(content);
       */
        int i = 0;
        //: content_i := "{}";
        while /*: inv "0 <= i & i <= size &
                 (content_i = {n. EX j. n = a.[j] & 0 <= j & j < i }) &
                 (x ~: content_i)" */
            (i < size) {
            if (a[i] == x) {
                return true;
            } else {
                //: content_i := "content_i Un {a.[i]}";
                i = i + 1;
            }
        }
        //: noteThat "i = size";
        //: noteThat "content_i = content";
        return false;
    }
}
