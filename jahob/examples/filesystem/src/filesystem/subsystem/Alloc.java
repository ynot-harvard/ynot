package filesystem.subsystem;

import filesystem.inode.*;
import filesystem.buffercache.*;
import filesystem.util.*;
import filesystem.*;

public class Alloc {
     
    public static Buffer alloc () {
        SuperBlock sp = FileSystem.superBlock;
        
        while (sp.isLocked) 
            //should sleep here
            sp.isLocked = false;
        
        if (!sp.freeBlockSet.hasNext())
            return null;
        
        
        int blkid = sp.freeBlockSet.next();        
        Buffer buf = FileSystem.bufferCache.getblk(blkid);
        ByteArrayOperation.mzero(buf.data);
        sp.hasBeenModified = true;
        return buf;
    }
   
    
}
