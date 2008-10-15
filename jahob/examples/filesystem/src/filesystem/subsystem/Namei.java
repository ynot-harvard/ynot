package filesystem.subsystem;

import filesystem.util.*;
import filesystem.inode.*;
import filesystem.*;
import filesystem.buffercache.*;

public class Namei {
    
    //pathname start with "/"
    //returns locked inode
    public static Inode namei(String pathname) {
        if (pathname.charAt(0) != '/')
            throw new RuntimeException();
        
        Inode root = FileSystem.inodeCache.iget(FileSystem.superBlock.rootInodeId);
        Inode curi = root;
        
        StringTokenizer st = new StringTokenizer(pathname, "/");
        String token = st.next(); //remove initial "/"
        
        while (st.hasNext()) {
            //assert curi.fileType == Inode.DIRECTORY
            
            token = st.next();
            if (root == curi && token.equals(".."))
                continue;
            
            boolean found = false;
            DirectoryIterator deiter = new Directory(curi).iterator();
            while (deiter.hasNext()) {
                DirectoryEntry de = deiter.next();
                if (de.filename.equals(token)) {
                    curi = FileSystem.inodeCache.iget(de.inodeid);
                    found = true;
                    break;
                }
            }
              
            if (!found) return null;            
        }
        
        curi.isLocked = true;
        return curi;
    }
}
