/*
 * Ialloc.java
 *
 * Created on April 17, 2005, 2:39 PM
 */

package filesystem.subsystem;

import filesystem.inode.*;
import filesystem.buffercache.*;
import filesystem.util.*;
import filesystem.*;

public class Free {
 
    
    public static void free (int blkid) {
        SuperBlock sp = FileSystem.superBlock;
        
        sp.freeBlockSet.add(blkid);
    }
   
    
}
