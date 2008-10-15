package filesystem.systemcall;

import filesystem.*;
import filesystem.buffercache.*;

public class SubSystem {
    
    public static int alloc () {
        return FileSystem.superBlock.freeBlockSet.alloc();
    }
    
    public static void free (int blkid) {
        FileSystem.superBlock.freeBlockSet.add(blkid);
    }
    
}
