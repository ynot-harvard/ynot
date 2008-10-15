package filesystem.buffercache;

import filesystem.disk.*;
import filesystem.*;

/**
 *
 *
 * change pool..contents -> pool..BufferPool.contents
 *
 */

public class BufferCache {
    // contents is has injective multiplicity constraint

    //: specfield contents : "(int * object) set"
    //: vardefs "contents == {p. EX (i::int). EX (b::object). p=(i, b) & i > 0 & i < diskBlockCount & b:Buffer & b.blkid = i}"
    //: invariant "single_valued contents"
    
    //: specfield locked : "object set"
    //: vardefs "locked == {buf. buf : pool..contents & buf.isLocked}"

    // perhaps check that Jahob can infer invariants like this:
    //: invariant "locked <= Buffer"

    //: specfield valid : "object set"
    //: vardefs "valid == {buf. buf : pool..contents & buf.blkid != 0}"
    
    //: invariant "locked <= valid"
    //: invariant "freelist..contents = pool..BufferPool.contents - locked"
    //: invariant "valid = hashqueues..contents"
    //: invariant "valid <= Range contents"
    //: invariant "valid <= pool..contents"
    //: invariant "(pool..contents - valid) Int Range contents = {}"
    //: invariant "(valid = pool..contents) --> (hashqueues..contents = pool..contents)"
    //: invariant "hashqueues..contents <= pool..contents"
    //: invariant "freelist..contents <= pool.contents"
    
    //use injectivity constraint to avoid using set comprehension
    //: invariant "ALL bufa bufb. (bufa : valid & bufb : valid & bufa ~= bufb) --> (bufa..blkid ~= bufb..blkid)"
    
    private BufferPool pool;
    private BufferFreeList freelist;
    private BufferHashQueues hashqueues;
    
    private static final int diskBlockCount = 1024;
    
    public BufferCache(int bufferCount)
    /*:
        requires "0 < bufferCount"
        modifies contents, locked, valid
        ensures "locked = {} & valid = {}"
     */
    {
        this.pool = new BufferPool(bufferCount);
        this.freelist = new BufferList();
        this.hashqueues = new BufferHashQueues(bufferCount / 10);
        
	int i = 0;
	while (i < pool.buffers.length) {
            freelist.add(pool.buffers[i].freelistNode);
	    i = i + 1;
        }
    }

    public void brelse(Buffer buffer)
    /*:
        requires "buffer : locked"
        modifies locked
        ensures "buffer ~: locked"
     */
    {
        buffer.unlock();
        freelist.add(buffer.freelistNode);        
    }
    
    
    public Buffer bread(int blkid)
    /*:
        requires "blkid : Domain contents & elemImage blkid contents Int locked = {}"
        modifies locked
        ensures "(blkid,result) : contents & result : locked"
     */
    {
        Buffer buf = balloc(blkid);
        FileSystem.disk.read(blkid, 0, buf.data, 0, buf.data.length);
        return buf;
    }
    
    public void bwrite(Buffer buf)
    /*:
        requires "buf : valid"
     */
    {
        FileSystem.disk.write(buf.blkid, 0, buf.data, 0, buf.data.length);
    }
    
    public Buffer balloc(int blkid)
    /*:
        requires "blkid : Domain contents & elemImage blkid contents Int locked = {}"
        modifies locked
	ensures "(blkid,result) : contents & result : locked"
     */
    {
        System.out.println("[BufferCache.getBlock] blkid = " + blkid);
        
        if (blkid <= 0 || blkid >= diskBlockCount)
            return null;
        
        Buffer buffer = hashqueues.get(blkid);
        
        if (buffer != null) {
            if (buffer.isLocked) {
                //call sleep until this buffer becomes free
                System.out.println("waiting until this buffer becomes free");                
                return null;
            }
            
            //invariant temporarily violated here
            //a buffer is on the freelist iff it is free
            freelist.remove(buffer.freelistNode);                        
            
        } else {
            if (freelist.isEmpty()) {
                //call sleep until any buffer becomes free
                System.out.println("waiting until any buffer becomes free");
                return null;
            }
            
            buffer = freelist.pop().buffer;            
            //invariant temporarily violated here
            //all buffers appear somewhere on the hashqueues
            
            //effectively, checking whether its on the hashqueue
            //interesting because don't have to search for it to know if its there if we assume the invariant
            if (buffer.blkid != 0)
                hashqueues.remove(buffer.blkid);
            
            buffer.blkid = blkid;
            hashqueues.add(buffer.hashqueueNode);                        
        }
        
        buffer.lock();    
        
        return buffer;
    }
}
