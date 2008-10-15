/* BufferCache main class, written by Suhabe Bugrara, MIT, May 2005. */
public class BufferCache {
    // contents is has injective multiplicity constraint
    
    public static boolean inv_hold;
    
    //: public static specvar contents :: objset;
    //: vardefs "contents == {b. b : Buffer & 0 < b..Buffer.blkid & b..Buffer.blkid < Disk.BLOCK_COUNT}"
    
    //: public static specvar locked :: objset = "{}";
    //: vardefs "locked == {buf. buf : BufferPool.contents & buf..Buffer.isLocked}"
    
    //: public static specvar valid :: objset = "{}";
    //: vardefs "valid == {buf. buf : BufferPool.contents & buf..Buffer.blkid != 0}"
    
    //solved invariants
    //: invariant "inv_hold --> (BufferCache.locked Int BufferFreeList.contents = {})"
    //: invariant "inv_hold --> locked <= BufferPool.contents"
    //: invariant "inv_hold --> (BufferHashQueues.contents <= BufferPool.contents)"
    //: invariant "inv_hold --> (BufferFreeList.contents <= BufferPool.contents)"
    //: invariant "inv_hold --> (locked <= valid)"
    //: invariant "inv_hold --> (valid = BufferHashQueues.contents)"
    //: invariant "inv_hold --> (valid <= contents)"
    //: invariant "inv_hold --> (valid <= BufferPool.contents)"
    //: invariant "inv_hold --> ((BufferPool.contents - valid) Int contents = {})"
    
    /* A consequence is: 
       "inv_hold --> ((valid = BufferPool.contents) --> (BufferHashQueues.contents = BufferPool.contents))"
    */

    //: invariant "inv_hold --> (ALL bufa bufb. (bufa : valid & bufb : valid & bufa ~= bufb) --> (bufa..Buffer.blkid ~= bufb..Buffer.blkid))"
    
    //: invariant "inv_hold --> (BufferFreeList.contents = BufferPool.contents - locked)"
    
    public static void init()
    /*:
        requires "~inv_hold"
        modifies inv_hold
        ensures "inv_hold"
     */
    {        
        BufferFreeList.init();
        Disk.init();
        BufferHashQueues.init();
        BufferPool.init();                
        initFreeList();                      
        inv_hold = true;        
    }
    
    private static void initFreeList()
    /*:
        requires "~inv_hold & BufferFreeList.contents = {}"
        ensures "BufferFreeList.contents = BufferPool.contents"
     */
    {
        BufferPool.initIterator();
        
        while
        /*:
            inv "BufferFreeList.contents = BufferPool.contents - BufferPool.remaining"
         */
                (BufferPool.hasNext()) {
            Buffer buf = BufferPool.next();
            BufferFreeList.add(buf);
        }
    }        
    
    public static void brelse(Buffer buffer)
    /*:
        requires "inv_hold & buffer ~= null & buffer..Buffer.isLocked & buffer : BufferPool.contents"
        modifies "buffer..Buffer.isLocked"
        ensures "~buffer..Buffer.isLocked"
     */
    {
        inv_hold = false;
        buffer.unlock();
        BufferFreeList.add(buffer);
        inv_hold = true;
        
        /*
         
         assert "locked = old(locked) - {buffer} &
                 BufferFreeList.contents = old(BufferFreeList.contents) + {buffer}"
         */
    }
    
    public static Buffer balloc(int blkid)
    /*:
        requires "inv_hold"
        ensures "result ~= null --> (result : contents & result..Buffer.blkid = blkid & result..Buffer.isLocked)"
     */          
    {
        inv_hold = false;
        
        if (blkid <= 0 || blkid >= Disk.BLOCK_COUNT) {
            inv_hold = true;
            return null;
        }
                
        Buffer buffer = BufferHashQueues.get(blkid);
                
        
        if (buffer != null) {
            if (buffer.isLocked) {
                inv_hold = true;
                return null;
            }
            
            BufferFreeList.remove(buffer);
            
        } else {
            
            if (BufferFreeList.isEmpty()) {
                inv_hold = true;
                return null;
            }
            
            buffer = BufferFreeList.pop();
            
            if (buffer.blkid != 0)
                BufferHashQueues.remove(buffer);
            
            buffer.blkid = blkid;
            BufferHashQueues.add(buffer);
        }
        
        buffer.lock();
        
        inv_hold = true;
        
        return buffer;
    }    
}
