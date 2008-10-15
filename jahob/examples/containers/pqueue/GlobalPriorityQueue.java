import java.util.Random;

public class GlobalPriorityQueue
{
    private static Element[] queue;
    public /*: readonly */ static int length;

    /*: 
      public static ghost specvar init :: bool = "False";

      public static specvar content :: "(obj * obj) set"
      vardefs "content == 
         {(k,v). EX j. 1 <= j & j <= length & 
                  (EX e. e = queue.[j] & 
                   p = (e..Element.key, e..Element.value))}";

      public static specvar maxlen :: int;
      vardefs "maxlen == queue..Array.length - 1";

      invariant "init --> 0 <= length";
      invariant "init --> length <= maxlen";
      invariant "init --> queue ~= null";
      invariant "init --> (ALL i. 0 < i & i <= length --> queue.[i] ~= null)";

     */

    public static void init(int len)
    /*: requires "0 <= len"
        modifies content, maxlen, length, "Array.arrayState", init
	ensures "content = {} & maxlen = len & length = 0 & init"
    */
    {
	queue = new Element[len];
	length = 0; // the queue is initially empty
        //: "GlobalPriorityQueue.init" := "True";
    }

    public static int maxLengthBuggy()
    /*: 
      requires "init"
      ensures "result = maxlen"
    */
    {
	return queue.length;
    }   
    
    public static int maxLength()
    /*: 
      requires "init"
      ensures "result = maxlen"
    */
    {
	return queue.length - 1;
    }

    public static boolean isEmpty()
    /*: 
      requires "init"
      ensures "result = (length = 0)"
    */
    {
	return (length == 0);
    }

    public static boolean isFullBuggy()
    /*: 
      requires "init"
      ensures "result = (length = maxlen)"
    */
    {
	return (length == queue.length);
    }
   
    public static boolean isFull()
    /*: 
      requires "init"
      ensures "result = (length = maxlen)"
    */
    {
	return (length + 1 == queue.length);
    }
   
    private static int parent(int i)
    {
	return i/2;
    }

    private static int left(int i)
    {
	return 2*i;
    }

    private static int right(int i)
    {
	return 2*i + 1;
    }

    private static int code(Object ob)
    //: ensures "result >= 0"
    {
	return 0;
    }

    public static void insert(Object key, Object value)
    /*: requires "init & length < maxlen"
        modifies content, length, "Array.arrayState"
	ensures "content = old content Un {(key, value)} & 
                 length = old length + 1"
    */
    {
        length = length + 1;
        int i = length;
        while /*: inv "1 <= i & i <= length & 
                       old content = {(k,v). EX j. 1 <= j & j <= length & j ~= i & 
                                             (EX e. e = queue.[j] & 
                                             k = e..Element.key & v = e..Element.value)}";
               */
            (i > 1 && code(queue[i/2].key) < code(key)) {
            queue[i] = queue[i/2];	
            i = i/2;
        }
        Element e = new Element();
        e.key = key;
        e.value = value;
        queue[i] = e;
    }


    /*
    public static void main(String[] args)
    {
	int size = 64;
	Random generator = new Random();
        init(size);

	System.out.println("Inserting...");
	int r = generator.nextInt(size);
	int max = r;
	while(!isFull()) {
	    if (r > max) max = r;
	    insert(new Integer(r), r);
            System.out.println(r);
            if (((Integer)findMax()).intValue() != max)
		System.err.println("There is a bug!");
	    r = generator.nextInt(size);
	}

	System.out.println("\nExtracting...");
	while(!isEmpty())
	{
	    Integer s = (Integer)extractMax();
	    System.out.println(s);
	}
    }
    */
}
