package filesystem.inode;

public class InodePool {
    //: specfield contents : "Buffer set"
    
    public Inode[] inodes;
    
    public InodePool(int poolSize)
        /*:
                requires "poolSize > 0 & bufferSize > 0"
                modifies contents
                ensures "contents <= Buffer & card contents = poolSize"
         */
    {
        inodes = new Inode[poolSize];
        
        for (int i = 0; i < inodes.length; i++) {
            Inode buf = new Inode();
            inodes[i] = buf;
        }
    }

}
