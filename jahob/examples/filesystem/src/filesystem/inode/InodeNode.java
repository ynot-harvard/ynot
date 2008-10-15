package filesystem.inode;

public class InodeNode {	
    public InodeNode prev;
    public InodeNode next;
    public final Inode inode;
    
    public InodeNode (Inode i)
    /*:
     	requires "inode != null"
     	ensures "inode = i"
     */
    {
    	inode = i;
    }

}
