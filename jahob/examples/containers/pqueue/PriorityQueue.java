import java.util.Random;

public class PriorityQueue
{
    private PriorityQueueElement[] queue;
    private int length;

    //: public specvar spqueue :: "(obj * int) set"
    //: public specvar smaxlen :: int
    //: public specvar slength :: int

    /*: vardefs "spqueue == 
         { p. EX i. 0 <= i & i < length & 
              (EX n. n = queue.[i] & 
              p = (n..PriorityQueueElement.ob, n..PriorityQueueElement.key))}" */
    //: vardefs "smaxlen == queue..Array.length"
    //: vardefs "slength == length"

    //: invariant "this ~= null --> queue ~= null"
    //: invariant "this ~= null --> 0 <= length"
    //: invariant "this ~= null --> length <= smaxlen"
    /*: invariant "this ~= null --> (ALL i. 0 <= i & i < length --> queue.[i]..PriorityQueueElement.ob ~= null)" */
    /*: invariant "this ~= null --> (ALL i. 0 <= i & i < length --> 0 <= queue.[i]..PriorityQueueElement.key)" */

    public PriorityQueue(int len)
    /*: requires "0 <= len"
        modifies spqueue, smaxlen, slength, "Array.arrayState"
	ensures "spqueue = {} & smaxlen = len & slength = 0"
    */
    {
	this.queue = new PriorityQueueElement[len];
	this.length = 0; // the queue is initially empty
    }

    public int currLength()
    //: ensures "result = slength"
    {
	return this.length;
    }
    
    public int maxLength()
    //: ensures "result = smaxlen"
    {
	return queue.length;
    }
    
    public boolean isEmpty()
    //: ensures "result = (slength = 0)"
    {
	return (this.length == 0);
    }

    public boolean isFull()
    //: ensures "result = (slength = smaxlen)"
    {
	return (this.length == queue.length);
    }
   
    private static int parent(int i)
    {
	return (i-1)/2;
    }

    private static int left(int i)
    {
	return (2*i + 1);
    }

    private static int right(int i)
    {
	return (2*i + 2);
    }

    public void insert(Object ob, int key)
    /*: requires "ob ~= null & key >= 0 & slength < smaxlen"
        modifies spqueue, slength
	ensures "spqueue = old spqueue Un {(ob, key)} & 
                 (slength = (old slength) + 1)"
    */
    {
	int i = this.length;
	this.length = this.length + 1;
       
	while(i > 0 && queue[parent(i)].key < key)
	{
	    queue[i] = queue[parent(i)];	

	    i = parent(i);
	}
	
        PriorityQueueElement e = new PriorityQueueElement();
	queue[i] = e;
        e.ob = ob;
        e.key = key;
    }

    public Object findMax()
    /*: ensures "(old slength = 0 --> result = null) &
                 (old slength > 0 --> 
                   (EX p1. (result, p1) : spqueue & 
                     (ALL o2 p2. (o2, p2) : spqueue --> p2 <= p1)))"
    */
    {
	if (this.isEmpty()) return null; // queue is empty
	return queue[0].ob;
    }

    public Object extractMax()
    /*: modifies spqueue, slength
        ensures  "(old slength = 0 --> result = null & spqueue = old spqueue & slength = old slength) &
                  (old slength > 0 -->
                    slength = old slength - 1 &
                    (EX (p1::int). 
                       (result,p1) : spqueue &
                       spqueue = old spqueue \<setminus> {(result,p1)} &
                       (ALL (o2::obj) (p2::int). (o2, p2) : spqueue --> p2 <= p1)))"
    */
    {
	if (this.isEmpty()) return null; // queue is empty
	Object result = queue[0].ob;
	
	this.length = this.length - 1;
	queue[0] = queue[this.length];
	heapify(0);
	return result;
    }

    private void heapify(int i)
    {
	int l = left(i);
	int m;
	if (l < this.length && queue[l].key > queue[i].key)
	    m = l;
	else
	    m = i;
	int r = right(i);
	if (r < this.length && queue[r].key > queue[m].key)
	    m = r;
	if (m != i)
	{
	    PriorityQueueElement p = queue[m];
	    queue[m] = queue[i];
	    queue[i] = p;
	    heapify(m);
	}
    }

    /*
    public static void main(String[] args)
    {
	int size = 32;
	Random generator = new Random();
	PriorityQueue pq = new PriorityQueue(size);

	System.out.println("Inserting...");
	int r = generator.nextInt(size);
	int max = r;
	while(!pq.isFull())
        {
	    if (r > max) max = r;
	    pq.insert(new Integer(r), r);
	    System.out.println(r);
	    if (((Integer)pq.findMax()).intValue() != max)
		System.err.println("There is a bug!");
	    r = generator.nextInt(size);
	}

	System.out.println("\nExtracting...");
	while(!pq.isEmpty())
	{
	    Integer s = (Integer)pq.extractMax();
	    System.out.println(s);
	}
    }
    */
}
