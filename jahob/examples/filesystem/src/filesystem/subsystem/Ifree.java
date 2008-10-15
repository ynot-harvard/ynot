package filesystem.subsystem;

import filesystem.inode.*;
import filesystem.buffercache.*;
import filesystem.util.*;
import filesystem.*;

public class Ifree {
 
    public static void ifree (int inodeid) {
        Inode inode = FileSystem.inodeCache.iget(inodeid);
        inode.fileType = Inode.FREE;
        
        FileSystem.superBlock.freeInodeSet.cache(inodeid);
    }   
    
}
