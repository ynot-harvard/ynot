public /*: claimedby BufferCache */ class BufferNode {	
    BufferNode prev;
    BufferNode next;
    
    final Buffer buffer;
    
    // public invariant "buffer ~= null"
    
    BufferNode (Buffer buf)
    /*:
     	requires "buf != null"
        modifies buffer
     	ensures "buffer = buf"
     */
    {
    	buffer = buf;
    }

}
