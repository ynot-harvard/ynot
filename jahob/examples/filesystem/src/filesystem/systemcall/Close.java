package filesystem.systemcall;


import filesystem.*;
import filesystem.inode.*;
import filesystem.buffercache.*;
import filesystem.util.*;

public class Close {
    
    
    public static void close (FileDescriptor fd) {
        if (fd.fileTableEntry.refCount > 1) {
            fd.fileTableEntry.refCount--;
        }
        else {
            FileSystem.inodeCache.iput(fd.fileTableEntry.inode);
            fd.fileTableEntry.clear();
            
        }
        
        fd.clear();
    } 
}
