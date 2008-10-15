public /*: claimedby BufferCache */ class BufferPool {
    //: public static specvar contents :: objset = "{}";
    //: public invariant "contents <= Buffer"
    
    //: public static specvar remaining :: objset = "{}";
    //: public invariant "contents <= Buffer"
    
    public static final int POOL_SIZE = 100;
   
    private static Buffer[] buffers;
    private static int index;
    
    
    static void init () 
    /*:
      requires "True"
      modifies contents
      ensures "contents ~= {} & (ALL b. b:contents & b..Buffer.blkid = 0 & ~b..Buffer.isLocked)"
    */
    {                
        buffers = new Buffer[POOL_SIZE];
        
	int i = 0;
	while (i < buffers.length) {
            Buffer buf = new Buffer(1024);
            buffers[i] = buf;
	    i = i + 1;
        }
    }
    
    public static void initIterator()
    /*:
        requires "True"
        modifies remaining 
        ensures "remaining = contents"
     */
    {
        index = 0;
    }
    
    public static boolean hasNext()
    /*:
        requires "True"
        ensures "result = (remaining ~= {})"
     */
    {
        return index <= buffers.length - 1;
    }
    
    public static Buffer next ()
    /*:
        requires "remaining ~= {}"
        modifies remaining
        ensures "remaining = old(remaining) - { result } & result : remaining"
     */
    {
        Buffer b = buffers[index];
        index = index + 1;
        return b;
    }
    
}
