class BufferList  {
    // specfield nodes : "obj set"
    // public invariant "nodes <= BufferNode"
    
    // "(first = null) = (last = null)"
    // "(card nodes = 0) = (first = null)"

    private BufferNode first;
    private BufferNode last;
    
    BufferList()
    /*
        requires "True"
        modifies nodes
        ensures "nodes = {}"
     */
    {
        first = null;
        last = null;
    }
    
    BufferNode getFirst()
    /*
        requires "True"
        ensures "nodes = {} --> result = null & 
                    nodes ~= {} --> result : nodes"
     */
    {
        return first;
    }
    
    
    BufferNode getLast()
    /*
        requires "True"
        ensures "nodes = {} --> result = null & 
                    nodes ~= {} --> result : nodes"
     */
    {
        return last;
    }
    
    void remove(BufferNode node)
    /*
        requires "node : nodes"
        modifies nodes
        ensures "nodes = old(nodes) - {node}"
     */
    {
        if (first == node && last ==  node) {
            first = null;
            last = null;
        } else if (first == node) {
            first = first.next;
        } else if (last == node) {
            last = last.prev;
        }
        
        if (node.prev != null)
            node.prev.next = node.next;
        
        if (node.next != null)
            node.next.prev = node.prev;
        
        node.prev = null;
        node.next = null;
        
    }
        
    BufferNode pop()
    /*
        requires "nodes ~= {}"
        modifies nodes
        ensures "nodes = old(nodes) - {result} & result : nodes"
     */
    {
        BufferNode popped = first;
        
        if (first == last) {
            first = null;
            last = null;
        } else {
            first = first.next;
        }
        
        remove(popped);
        
        return popped;
    }
    
    void push(BufferNode node)
    /*
        requires "node ~= null & (ALL n . n:nodes & n..BufferNode.buffer..Buffer.blkid ~= node..BufferNode.buffer..Buffer.blkid)"
        modifies nodes
        ensures "nodes = old(nodes) Un {node}"
     */
    {
        
        if (isEmpty()) {
            first = node;
            last = node;
        } else {
            first.prev = node;
            node.next = first;
            first = node;
        }
    }
    
    void add(BufferNode node)
    /*
        requires "node ~= null & (ALL n . n:nodes & n..BufferNode.buffer..Buffer.blkid ~= node..BufferNode.buffer..Buffer.blkid)"
        modifies nodes
        ensures "nodes = old(nodes) Un {node}"
     */
    {
        if (isEmpty()) {
            first = node;
            last = node;
        } else {
            last.next = node;
            node.prev = last;
            last = node;
        }
    }
    
    boolean isEmpty()
    /*
        requires "True"
        ensures "result = (nodes ~= {})"
     */
    {
        return first == null && last == null;
    }     
    
        /*    */
        
    BufferNode get(int blkid)
    /*
        requires "True"
        ensures "let bufs = { b . b:(fg BufferNode.buffer) `` nodes & b..Buffer.blkid = blkid } in                
                    (blkid ~: (fgint Buffer.blkid) `` bufs --> result = null) &
                    (blkid : (fgint Buffer.blkid) `` bufs --> result : bufs)"
     */
    {
        BufferNode current = getFirst();
        
        while (current != null) {
            Buffer buf = (Buffer) current.buffer;
            
            if (buf.blkid == blkid) {
                return current;
            }
            
            current = current.next;
        }
        
        return null;
    }    
}
