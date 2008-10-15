package filesystem.inode;

public class InodeList  {
	//: specfield contents: "Inode set"
	//: specfield nodes : "BufferNode set"
	
	//: invariant "{ n..inode . n:nodes } = contents & card contents = card nodes"
	//: invariant "first = null <--> last = null"
	
    private InodeNode first;
    private InodeNode last;    
	
    public InodeList()
	/*:
 		requires "True"
 		modifies contents, nodes
 		ensures "contents = {} & nodes = {}"	 
 	*/
    {
        first = null;
        last = null;
    }
	        
    public InodeNode getFirst()
    /*:
 		requires "True"
 		ensures "result : nodes"
 	*/
    {
        return first;
    }
    

    public InodeNode getLast()
    /*:
		requires "True"
		ensures "result : nodes"
	*/
    {
        return last;
    }
    
    public void remove (InodeNode node) 
    /*:
      	requires "node ~= null & node : node"
      	modifies contents, nodes
      	ensures "(contents = old(contents) - {node..inode}) & 
      				(nodes = old(nodes) - {node})"	      
     */
    {
    	if (first == node && last ==  node) { 
    		first = null;
    		last = null;
    	}
    	else if (first == node) {
    		first = first.next;
    	}
    	else if (last == node) {
    		last = last.prev;
    	}
    		
    	if (node.prev != null) 
    		node.prev.next = node.next;    		    	
    	
    	if (node.next != null)     		
    		node.next.prev = node.prev;
    	
    	node.prev = null;
    	node.next = null;    	
    	
    }
    
        
    public InodeNode pop () 
    /*:
     	requires "card nodes > 0"
        modifies content, nodes
        ensures "(contents = old(contents) - {result..inode}) &
        			(nodes = old(nodes) - {result}) &
        			result : nodes"
     */    
    {
    	InodeNode popped = first;
    	
    	if (first == last) {
    		first = null;
    		last = null;
    	}
    	else {
    	   	first = first.next;
    	}
    	
    	remove(popped);
    	
        return popped;
    }          
        
    public void push(InodeNode node)
    /*:
  		requires "node ~= null & node ~: nodes & node..inode ~: contents"
  		modifies contents, nodes
  		ensures "(contents = old(contents) Un {node..inode}) &
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
    
    public void add(InodeNode node)
    /*:
		requires "node ~= null & node ~: nodes & node..inode ~: contents"
		modifies contents, nodes
		ensures "(contents = old(contents) Un {node..inode}) &
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
        
    public boolean isEmpty() 
    /*:
      	requires "True"
        ensures "result = (card contents > 0)"
     */
    {
        return first == null && last == null;
    }
    
    /*
    ensures "let s = { n . n : contents & n.inode.id = id } in 
		((card s = 0 --> result = null) & (card s > 0 --> result : s))*/
    
    public InodeNode get(int id)    
    /*:
     	requires "True"
     	ensures "((card { n . n : nodes & n..inode..id = id } = 0 --> result = null) & 
     			  (card { n . n : nodes & n..inode..id = id } > 0 --> result : { n . n : nodes & n..inode..id = id }))"     			
     */
    {
    	InodeNode current = getFirst();   	
    	
    	while (current != null) {    		
    		Inode inode = (Inode) current.inode;
    		
    		if (inode.id == id) {    			
    			return current;
    		}
    			
    		current = current.next;
    	}
    	
    	return null;
    }
    
    public boolean contains (int id)     
    /*:
     	requires "True"
     	ensures "result = (card { n . n : nodes & n..inode..id = id } > 0)"     			
     */
    {
    	return get(id) == null;
    }
    
}
