package filesystem.subsystem;

/**
 * only implemented in a single block
 * requires that freeInodeCount is accurate
 */

import filesystem.util.*;
import filesystem.inode.*;
import filesystem.*;
import filesystem.buffercache.*;

public class FreeInodeSet /*implements Iterator (but need generics) */ {
    
    public int freeInodeCount;
    public int[] freeInodes;
    public int nextFreeInodeIndex;
    
    public boolean isLocked;
    
    public FreeInodeSet() {
        freeInodes = new int[FileSystem.BLOCK_SIZE / 4];
        freeInodeCount = 0;
        nextFreeInodeIndex = -1;        
        isLocked = false;
    }
    
    public boolean hasNext() {
        return freeInodeCount > 0;
    }
    
    //requires hasNext()
    public int next() {
        int inodeid = freeInodes[nextFreeInodeIndex];
        nextFreeInodeIndex--;
        freeInodeCount--;
        
        if (nextFreeInodeIndex < 0) {
            //have to search through the disk for free inodes and return the one at index o
            harvest();
        }
        
        return inodeid;
    }
    
    public void harvest() {
        int inodesperblock = FileSystem.BLOCK_SIZE / FileSystem.superBlock.inodeSize;
        int start = FileSystem.superBlock.inodeListStart;
        int end = start + FileSystem.superBlock.inodeCount / inodesperblock;
        
        for (int i = start; i < end && nextFreeInodeIndex < freeInodes.length; i++) {
            Buffer buf = FileSystem.bufferCache.bread(i);
            
            Inode tmp = new Inode();
            for (int j = 0; j < inodesperblock && nextFreeInodeIndex < freeInodes.length; j++) {
                tmp.unserialize(buf.data, j * FileSystem.superBlock.inodeSize);
                tmp.id = i * inodesperblock + j;
                
                if (tmp.fileType == Inode.FREE) {
                    nextFreeInodeIndex++;
                    freeInodes[nextFreeInodeIndex] = tmp.id;
                }
            }
            
            FileSystem.bufferCache.brelse(buf);
        }
    }
    
    public void cache(int inodeid) {
        freeInodeCount++;
        
        if (nextFreeInodeIndex < freeInodes.length - 1) {
            nextFreeInodeIndex++;
            freeInodes[nextFreeInodeIndex] = inodeid;
        }
    }
}
