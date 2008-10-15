package filesystem.systemcall;

import filesystem.*;
import filesystem.inode.*;
import filesystem.buffercache.*;
import filesystem.util.*;
import filesystem.subsystem.*;

public class Ls {
    
    public static void ls (String dirname) {
        Inode inode = Namei.namei(dirname);
        if (inode.fileType != Inode.DIRECTORY)
            throw new RuntimeException();
        
        Directory dir = new Directory(inode);
        DirectoryIterator di = dir.iterator();
        
        while (di.hasNext()) {
            DirectoryEntry de = (DirectoryEntry) di.next();
            if (de == null) continue;
            System.out.println(de.filename);            
        }            
    }
    
}
