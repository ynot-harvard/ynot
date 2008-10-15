package filesystem.buffercache;

class BufferNode {	
    BufferNode prev;
    BufferNode next;
    
    final Buffer buffer;
    
    BufferNode (Buffer buf)
    /*:
     	requires "buf != null"
     	ensures "buffer = buf"
     */
    {
    	buffer = buf;
    }

}
