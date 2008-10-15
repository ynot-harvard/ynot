package filesystem.buffercache;

public class Buffer {       
    
    public int blkid;    
    public final byte[] data; //size must be greater than disk block size
       
    public /*readonly*/ boolean isLocked;    
    
    final BufferNode freelistNode;
    final BufferNode hashqueueNode;
    
    Buffer(int byteCount) 
    /*: 
     	requires "byteCount > 0"
     	modifies blkid, isLocked, data
     	ensures "blkid = 0 & ~isLocked & freelistnode != null & hashqueuenode != null & data != null"
     */
    {
        this.blkid = 0;
        this.data = new byte[byteCount];        
        this.isLocked = false;        
        
        freelistNode = new BufferNode(this);        
        hashqueueNode = new BufferNode(this);         
    }
                
    void lock ()
    /*:
     	requires "~isLocked"
     	modifies isLocked
     	ensures "isLocked"
     */
    {
        isLocked = true;
    }
    
    void unlock ()
    /*:
     	requires "isLocked"
     	modifies isLocked
     	ensures "~isLocked"
     */
    {
        isLocked = false;
    }
}
