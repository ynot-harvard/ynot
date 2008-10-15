package filesystem.inode;

public class InodeHashQueues {
	//:	specfield contents :  "Inode set"
	//: specfield nodes : "InodeNode set"
	
	//: invariant "{ n..inode . n:nodes } = contents & card contents = card nodes"
	
    private int queueCount; 
    private InodeList[] queues;
    
    
    public InodeHashQueues(int queueCount) 
    /*:
         requires "queueCount > 0"
         modifies content, nodes
         ensures "content = {} & nodes {}"
     */
    {    	
        this.queueCount = queueCount; 
        queues = new InodeList[queueCount];
        for (int i = 0; i < queueCount; i++) 
        	queues[i] = new InodeList();
        
    }
    
    /*
	ensures "let s = { n . n : contents & n.inode.id = inodeid } in 
     				((card s = 0 --> result = null) & (card s > 0 --> result : s)) "*/
            
    public Inode get (int inodeid) 
    /*:
     	requires "True"
     	ensures "(card { inode . inode : contents & inode.id = inodeid } = 0 --> result = null) & 
     			 (card { inode . inode : contents & inode.id = inodeid } > 0 --> result : { inode . inode : contents & inode.id = inodeid })" 
     			
     */
    {
    	if (inodeid < 0)
    		return null;
    	
    	int index = inodeid % queueCount;    	
    	    	
    	InodeList list = queues[index];
    	
    	InodeNode node = list.get(inodeid);    	
    	if (node != null)
    		return (Inode) node.inode;
    	else
    		return null;
    }
    
    public void add (InodeNode node)
    /*:
     	requires "node ~= null & node ~: nodes & node.inode ~: contents"
		modifies contents, nodes
		ensures "contents = old(contents) Un {node..inode} &
				 nodes = old(nodes) Un {node}"  				
	*/
    {
    	int inodeid = node.inode.id;
    	int index = inodeid % queueCount;
    	
        queues[index].add(node);    	
    }
    
    public boolean contains (int inodeid)
    /*:
 		requires "True"
 		ensures "result = (card { inode . inode : contents & inode.id = inodeid } > 0)"     			
 	*/
    {
    	return get(inodeid) == null;
    }

    public void remove (int inodeid)
    /*:
  		requires "card { n . n : nodes & n.inode.id = inodeid } > 0"
  		modifies contents, nodes
  		ensures "nodes = old(nodes) - { n . n : nodes & n.inode.id = inodeid } &
  				 contents = old(contents) - { inode . inode : contents & inode.id = inodeid }"	      
  	*/
    {    	    	
    	int index = inodeid % queueCount;
    	
    	if (index >= 0 && index < queueCount) {
    		InodeList list = queues[index];    		
    		InodeNode node = list.get(inodeid);
    		if (node != null)
    			list.remove(node);    		
    	}    	
    }            
}
