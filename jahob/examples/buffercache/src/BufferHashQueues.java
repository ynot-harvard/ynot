public /* claimedby BufferCache */ class BufferHashQueues {    
    //: public static specvar contents :: objset = "{}";
    //: public invariant "contents <= Buffer"
    
    private static final int QUEUE_COUNT = 10;        
    private static BufferList[] queues;
            
    static void init () 
    /*:
         requires "True"
         modifies contents
         ensures "contents = {}"
    */
    {                
        queues = new BufferList[QUEUE_COUNT];
        
	int i = 0;
        while (i < queues.length) {
            queues[i] = new BufferList();
	    i = i + 1;
	}
    }    
    
    static Buffer get(int blkid)
    /*:
        requires "True"
        ensures "({ b . b : contents & b..Buffer.blkid = blkid } ~= {} --> result : { b . b : contents & b..Buffer.blkid = blkid }) &
                ({ b . b : contents & b..Buffer.blkid = blkid } = {} --> result = null)"
     */
    {
        if (blkid <= 0)
            return null;
        
        int index = blkid % queues.length;
        
        BufferList list = queues[index];
        
        BufferNode node = list.get(blkid);
        if (node != null)
            return (Buffer) node.buffer;
        else
            return null;
    }
    
    static void add(Buffer buffer)
     /*:
        requires "buffer ~= null & buffer ~: contents"
        modifies contents
        ensures "contents = old(contents) Un {buffer}"
     */
    {
        BufferNode node = buffer.hashqueueNode;
        
        int blkid = buffer.blkid;
        int index = blkid % queues.length;        
        queues[index].add(node);
    }
        
    static void remove(Buffer buffer)
   /*:
        requires "EX b . b:contents & b..Buffer.blkid = buffer..Buffer.blkid"
        modifies contents
        ensures "contents = old(contents) - {b . b:contents & b..Buffer.blkid = buffer..Buffer.blkid}"
     */
    {    
        int index = buffer.blkid % queues.length;
        BufferList list = queues[index];
        list.remove(buffer.hashqueueNode);        
    }
}
