public class Buffer {       
    
    public int blkid;    
    public final byte[] data; //size must be greater than disk block size
       
    public /*readonly*/ boolean isLocked;
    
    final BufferNode freelistNode;
    // public invariant "freelistNode ~= null"

    final BufferNode hashqueueNode;


    // public invariant "freelistNode..BufferNode.buffer = this"
    // public invariant "hashqueueNode..BufferNode.buffer = this"
    
    
    Buffer(int byteCount) 
    /*: 
     	requires "byteCount > 0"
     	modifies blkid, isLocked
     	ensures "blkid = 0 & ~isLocked & freelistNode : BufferNode & hashqueueNode : BufferNode"
     */
    {
        this.blkid = 0;
        this.data = new byte[byteCount];        
        this.isLocked = false;        
        
        freelistNode = new BufferNode(this);        
        hashqueueNode = new BufferNode(this);         
    }
                
    // & (ALL (b::obj). b ~= this --> (b..isLocked = old (b..isLocked)))"
    void lock ()
    /*:
     	requires "~isLocked"
     	modifies isLocked
     	ensures "isLocked & (ALL (b::obj). b ~= this --> (b..isLocked = old (b..isLocked)))"
     */
    {
        isLocked = true;
    }
    
    void unlock ()
    /*:
     	requires "isLocked"
     	modifies isLocked
     	ensures "~ isLocked & (ALL (b::obj). b ~= this --> (b..isLocked = old (b..isLocked)))"
     */
    {
        isLocked = false;
    }
}
