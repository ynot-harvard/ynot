package filesystem.systemcall;

import filesystem.*;
import filesystem.inode.*;
import filesystem.buffercache.*;
import filesystem.util.*;
import filesystem.subsystem.*;

public class Mkdir {
    
    public static void mkdir(String pathname) {
        Inode inode = Namei.namei(pathname);
        boolean previouslyExisted = inode != null;
        
        if (previouslyExisted) {
            throw new RuntimeException();
        }
        
        inode = Ialloc.ialloc();
        inode.fileType = Inode.DIRECTORY;
        String dirname = dirname(pathname);
        Inode parent = Namei.namei(dirname);
        Directory dir = new Directory(parent);
        dir.add(new DirectoryEntry(inode.id, filename(pathname)));                        
    }
    
        
    private static String dirname(String pathname) {
        if (!pathname.startsWith("/"))
            throw new RuntimeException();
        
        String str = "";
        String parent = "/";
        StringTokenizer st = new StringTokenizer(pathname, "/");
        while (st.hasNext()) {
            parent += str;            
            str = st.next();            
        }
        
        return parent;
    }
    
    private static String filename(String pathname) {
        if (!pathname.startsWith("/"))
            throw new RuntimeException();
        
        String str = "/";
        String parent = null;
        StringTokenizer st = new StringTokenizer(pathname, "/");
        while (st.hasNext()) {
            parent = str;
            str = st.next();
        }
        
        return str;
    }
}
