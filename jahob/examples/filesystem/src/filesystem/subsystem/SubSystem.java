package filesystem.subsystem;

import filesystem.*;
import filesystem.buffercache.*;
import filesystem.util.*;
import filesystem.inode.*;

public class SubSystem {
        
    public SubSystem() {
    }
    
    public Inode namei (String pathname) {
        return Namei.namei(pathname);
    }
    
    
    public void ifree (int inodeid) {
        Ifree.ifree(inodeid);
    }
    
    public static int alloc () {
        return FileSystem.superBlock.freeBlockSet.alloc();
    }
    
    //if blkid is 0, ignore it
    public static void free (int blkid) {
        if (blkid == 0)
            return;
        
        FileSystem.superBlock.freeBlockSet.add(blkid);
    }
    
    public Inode ialloc () {
        return Ialloc.ialloc();
    }
}
