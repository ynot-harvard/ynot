package filesystem.inode;

import filesystem.buffercache.*;
import filesystem.*;


public class BlockIterator /*should implement iterator */ {
    private BlockTable bt;
    private int curlogblknum;
    private int seensofar;
    
    /** Creates a new instance of DataBlockIterator */
    public BlockIterator(BlockTable bt) {
        this.bt = bt; 
        this.curlogblknum = -1; 
        this.seensofar = 0;
    }
        
    //returns blkid of next logical blk. 0 if doesn't exist
    public int next() {
        curlogblknum++;
        
        int blkid = bt.map(curlogblknum);
        if (blkid != 0)
            seensofar++;
        
        return blkid;
    }
    
    public boolean hasNext() {
        return seensofar < bt.blockCount;
    }
    
}
