package filesystem.buffercache;

class BufferList  {
    //: specfield nodes : "BufferNode set"
        
    //: invariant "{b. EX n. b=n..buffer & n:nodes } = contents & card contents = card nodes"
    
    //: invariant "(first = null) = (last = null)"
    // invariant "card nodes = 0 <--> first = null"

    private BufferNode first;
    private BufferNode last;
    
    BufferList()
    /*:
        requires "True"
        modifies contents, nodes
        ensures "contents = {} & nodes = {}"
     */
    {
        first = null;
        last = null;
    }
    
    BufferNode getFirst()
    /*:
        requires "True"
        ensures "card nodes = 0 --> result = null & 
                    card nodes > 0 --> result : nodes"
     */
    {
        return first;
    }
    
    
    BufferNode getLast()
    /*:
        requires "True"
        ensures "card nodes = 0 --> result = null & 
                    card nodes > 0 --> result : nodes"
     */
    {
        return last;
    }
    
    void remove(BufferNode node)
    /*:
        requires "node != null & node : nodes"
        modifies contents, nodes
        ensures "(contents = old(contents) - {node..buffer}) & 
                    (nodes = old(nodes) - {node})"
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
    /*:
        requires "card nodes > 0"
        modifies content, nodes
        ensures "(contents = old(contents) - {result..buffer}) & 
                    (nodes = old(nodes) - {result}) &
                    result : nodes"
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
    /*:
        requires "node != null & node ~: nodes & node..buffer ~: contents"
        modifies contents, nodes
        ensures "(contents = old(contents) Un {node..buffer}) &
                                        (nodes = old(nodes) Un {node})"
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
    /*:
        requires "node != null & node ~: nodes & node..buffer ~: contents"
        modifies contents, nodes
        ensures "(contents = old(contents) Un {node..buffer}) &
                                        (nodes = old(nodes) Un {node})"
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
    /*:
        requires "True"
        ensures "result = (card contents > 0)"
     */
    {
        return first == null && last == null;
    }         
        
    //TODO: might want to rewrite the ensures clause more elegantly
    BufferNode get(int blkid)
    /*:
        requires "True"
        ensures "((card { n . n : nodes & n..buffer..blkid = blkid } = 0 --> result = null) &
                          (card { n . n : nodes & n..buffer..blkid = blkid } > 0 --> result : { n . n : nodes & n..buffer..blkid = blkid }))"
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
