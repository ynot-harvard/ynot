package filesystem.subsystem;

import filesystem.inode.*;
import filesystem.buffercache.*;
import filesystem.util.*;
import filesystem.*;

public class Ialloc {
 
    //returns locked inode
    public static Inode ialloc () {
        SuperBlock superBlock = FileSystem.superBlock;
        
        while (true) {
            if (superBlock.isLocked) {
                //sleep until it becomes unlocked
                superBlock.isLocked = false;
                continue;
            }
            
            if (!superBlock.freeInodeSet.hasNext()) {
                return null;
            }
            
            int inodeid = superBlock.freeInodeSet.next();
            Inode inode = FileSystem.inodeCache.iget(inodeid);
            //potential race condition 
            //need transaction-like semantics to avoid races (i.e. next should return a "potential" inode only)
            
            inode.fileType = Inode.REGULAR;
            FileSystem.inodeCache.iwrite(inode);
            
            return inode;
        }
    }
   
    
}
