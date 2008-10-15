package filesystem.systemcall;

import filesystem.util.*;
import filesystem.inode.*;
import filesystem.subsystem.*;
import filesystem.*;

public class Open {
    
    public static FileDescriptor open (String pathname) {
        Inode inode = Namei.namei(pathname);
        if (inode == null)
            return null;
        
        FileTableEntry fte = FileSystem.globalFileTable.alloc();
        fte.inode = inode;
        fte.offset = 0;
        
        FileDescriptor ufti = FileSystem.userFileTable.alloc();
        ufti.fileTableEntry = fte;
        fte.refCount++;
        
        inode.isLocked = false;   
        
        return ufti;
    }
    
}
