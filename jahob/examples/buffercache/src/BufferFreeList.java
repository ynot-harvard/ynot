public /*: claimedby BufferCache */ class BufferFreeList  {
    //: public static specvar contents :: objset = "{}";
    //: public invariant "contents <= Buffer"
    
    private static BufferList list;
    
    static void init()
    /*:
        requires "True"
        modifies contents
        ensures "contents = {}"
     */
    {
        list = new BufferList();
    }
    
    static void remove(Buffer buffer)
    /*:
        requires "buffer ~= null & buffer : contents"
        modifies contents
        ensures "(contents = old(contents) - {buffer})"
     */
    {
        BufferNode node = buffer.freelistNode;        
        list.remove (node);
    }
        
    static Buffer pop()
    /*:
        requires "contents ~= {}"
        modifies contents
        ensures "(contents = old(contents) - {result}) & result : contents"
     */
    {
        BufferNode node = list.pop();
        return node.buffer;
    }
    
    static void push(Buffer buffer)
    /*:
        requires "buffer ~= null & buffer ~: contents"
        modifies contents
        ensures "(contents = old(contents) Un {buffer})"
     */
    {        
        list.push (buffer.freelistNode);
    }
    
    static void add(Buffer buffer) 
     /*:
        requires "buffer ~= null & buffer ~: contents"
        modifies contents
        ensures "(contents = old(contents) Un {buffer})"
     */
    {
        list.add(buffer.freelistNode);
    }
    
    static boolean isEmpty()
    /*:
        requires "True"
        ensures "result = (contents = {})"
     */
    {
        return list.isEmpty();
    }        
                
    static Buffer get(int blkid)
    /*:
        requires "True"
        ensures "let bufs = { b . b : contents & b..Buffer.blkid = blkid } in 
                            (bufs = {} --> result = null & bufs ~= {} --> result:bufs)"
     */
    {
        BufferNode node = list.get(blkid);
        return node == null ? null : node.buffer;
    }    
}
