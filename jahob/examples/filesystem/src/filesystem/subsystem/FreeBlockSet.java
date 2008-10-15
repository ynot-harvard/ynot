package filesystem.subsystem;

/**
 * Assign blocks from the beginning of arrays.
 * Link block appears at end of array
 *
 * might need locking here
 *
 */

import filesystem.*;
import filesystem.buffercache.*;
import filesystem.util.*;

public class FreeBlockSet /*implements Iterator (need generics) */ {    
    
    public /*readonly*/ int freeBlockCount;
    public /*readonly*/ int[] firstFreeBlocks;
    public /*readonly*/ int nextFreeBlockIndex;
    
    public boolean isLocked;
    
    public FreeBlockSet() {        
        firstFreeBlocks = new int[FileSystem.BLOCK_SIZE / 4];
        freeBlockCount = 0;
        nextFreeBlockIndex = -1;
        
        isLocked = false;
    }
    
    public boolean hasNext() {
        return freeBlockCount > 0;
    }
    
    //requires hasNext()
    public int alloc() {
        freeBlockCount--;
        
        if (nextFreeBlockIndex == 0) {
            int blkid = firstFreeBlocks[0];
            
            Buffer buffer = FileSystem.bufferCache.bread(blkid);            
            ByteArrayOperation.convertToIntArray(buffer.data, 0, firstFreeBlocks);
            ByteArrayOperation.mzero(buffer.data);
            FileSystem.bufferCache.bwrite(buffer);
            FileSystem.bufferCache.brelse(buffer);
            nextFreeBlockIndex = firstFreeBlocks.length - 1;
            
            return blkid;
        }
        else {
            nextFreeBlockIndex--;
            return firstFreeBlocks[nextFreeBlockIndex + 1];
        }
        
    }
    
    //requires blkid not in blocks originally
    public void add(int blkid) {
        freeBlockCount++;
        
        if (nextFreeBlockIndex < firstFreeBlocks.length - 1) {            
            nextFreeBlockIndex++;
            firstFreeBlocks[nextFreeBlockIndex] = blkid;
        }
        else {
            Buffer buffer = FileSystem.bufferCache.bread(blkid);            
            ByteArrayOperation.convertToBytes(firstFreeBlocks, buffer.data, 0);
            FileSystem.bufferCache.bwrite(buffer);
            FileSystem.bufferCache.brelse(buffer);
            firstFreeBlocks[0] = blkid;
            nextFreeBlockIndex = 0;
            //FileSystem.superBlock.write();
        }
    }
    
}
