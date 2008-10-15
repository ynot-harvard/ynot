package filesystem.buffercache;

/**
 * Each blkid must appear at most once in the hash queues
 *
 *
 */

class BufferHashQueues {
    //:	specfield contents :  "Buffer set"
    //: specfield nodes : "BufferNode set"
    
    //: invariant "{ n..buffer . n:nodes } = contents & card contents = card nodes"
    
    private int queueCount;
    private BufferList[] queues;
        
    BufferHashQueues(int queueCount)
    /*:
         requires "queueCount > 0"
         modifies content, nodes
         ensures "content = {} & nodes {}"
     */
    {
        this.queueCount = queueCount;
        queues = new BufferList[queueCount];
	int i = 0;
        while (i < queueCount) {
            queues[i] = new BufferList();
	    i = i + 1;
	}
    }
    
    Buffer get(int blkid)
    /*:
        requires "True"
        ensures "(card { buf . buf : contents & buf.blkid = blkid } = 0 --> result = null) &
                         (card { buf . buf : contents & buf.blkid = blkid } > 0 --> result : { buf . buf : contents & buf.blkid = blkid })"
     
     */
    {
        if (blkid < 0)
            return null;
        
        int index = blkid % queueCount;
        
        BufferList list = queues[index];
        
        BufferNode node = list.get(blkid);
        if (node != null)
            return (Buffer) node.buffer;
        else
            return null;
    }
    
    void add(BufferNode node)
    /*:
        requires "node != null & node ~: nodes & node.buffer ~: contents"
        modifies contents, nodes
        ensures "contents = old(contents) Un {node..buffer} &
                    nodes = old(nodes) Un {node}"
     */
    {
        int blkid = node.buffer.blkid;
        int index = blkid % queueCount;
        
        queues[index].add(node);
    }
        
    void remove(int blkid)
    /*:
        requires "card { n . n : nodes & n.buffer.blkid = blkid } > 0"
        modifies contents, nodes
        ensures "nodes = old(nodes) - { n . n : nodes & n.buffer.blkid = blkid } &
                    contents = old(contents) - { buf . buf : contents & buf.blkid = blkid }"
     */
    {    
        int index = blkid % queueCount;
        BufferList list = queues[index];
        BufferNode node = list.get(blkid);
        list.remove(node);        
    }
}
