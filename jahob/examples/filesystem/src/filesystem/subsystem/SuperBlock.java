package filesystem.subsystem;

import filesystem.*;
import filesystem.util.*;

public class SuperBlock {        
    
    public final FreeBlockSet freeBlockSet;
    public final FreeInodeSet freeInodeSet;
    
    public int fileSystemSize; 
    public int inodeListStart;
    public int freeBlocksStart;
    public int freeInodesStart;
    public int inodeSize;    
    public int inodeCount;
    public int rootInodeId;
    
    public boolean isLocked;    
    public boolean hasBeenModified;
    
    public SuperBlock() {        
        freeBlockSet = new FreeBlockSet();
        freeInodeSet = new FreeInodeSet();
        
        fileSystemSize = 0;       
        isLocked = false;        
        hasBeenModified = false;
    }
    
    public void unserialize (byte[] data, int start) {        
        int oldstart = start;
        
        fileSystemSize = ByteArrayOperation.convertToInt(data, start); start += 4;
        inodeListStart = ByteArrayOperation.convertToInt(data, start); start += 4;
        freeBlocksStart = ByteArrayOperation.convertToInt(data, start); start += 4;
        freeInodesStart = ByteArrayOperation.convertToInt(data, start);start += 4;
        inodeSize = ByteArrayOperation.convertToInt(data, start); start += 4;
        inodeCount = ByteArrayOperation.convertToInt(data, start); start += 4;
        rootInodeId = ByteArrayOperation.convertToInt(data, start); start += 4;
        
        freeBlockSet.freeBlockCount = ByteArrayOperation.convertToInt(data, start); start += 4;
        freeBlockSet.nextFreeBlockIndex  = ByteArrayOperation.convertToInt(data, start); start += 4;        
        freeInodeSet.freeInodeCount = ByteArrayOperation.convertToInt(data, start); start += 4;
        freeInodeSet.nextFreeInodeIndex = ByteArrayOperation.convertToInt(data, start); start += 4;
        
        System.out.println("data.length=" + data.length);
        System.out.println("oldstart=" + start);
        System.out.println("freeBlockSet.firstFreeBlocks.length=" + freeBlockSet.firstFreeBlocks.length);
        System.out.println("freeInodeSet.freeInodes.length=" + freeInodeSet.freeInodes.length);
        
        ByteArrayOperation.convertToIntArray(data, oldstart + 1 * FileSystem.BLOCK_SIZE, freeBlockSet.firstFreeBlocks); 
        ByteArrayOperation.convertToIntArray(data, oldstart + 2 * FileSystem.BLOCK_SIZE, freeInodeSet.freeInodes);
    }
    
    public void serialize (byte[] data, int start)  {
        int oldstart = start;
        
        ByteArrayOperation.convertToBytes(fileSystemSize, data, start); start += 4;
        ByteArrayOperation.convertToBytes(inodeListStart, data, start); start += 4;
        ByteArrayOperation.convertToBytes(freeBlocksStart, data, start); start += 4;
        ByteArrayOperation.convertToBytes(freeInodesStart, data, start);start += 4;
        ByteArrayOperation.convertToBytes(inodeSize, data, start); start += 4;
        ByteArrayOperation.convertToBytes(inodeCount, data, start); start += 4;
        ByteArrayOperation.convertToBytes(rootInodeId, data, start); start += 4;
        
        ByteArrayOperation.convertToBytes(freeBlockSet.freeBlockCount, data, start); start += 4;
        ByteArrayOperation.convertToBytes(freeBlockSet.nextFreeBlockIndex, data, start); start += 4;        
        ByteArrayOperation.convertToBytes(freeInodeSet.freeInodeCount, data, start); start += 4;
        ByteArrayOperation.convertToBytes(freeInodeSet.nextFreeInodeIndex, data, start); start += 4;
        
        System.out.println("data.length=" + data.length);
        System.out.println("freeBlocksStart=" + freeBlocksStart);
        System.out.println("freeInodesStart=" + freeInodesStart);
        ByteArrayOperation.convertToBytes(freeBlockSet.firstFreeBlocks, data, oldstart + 1 * FileSystem.BLOCK_SIZE); 
        ByteArrayOperation.convertToBytes(freeInodeSet.freeInodes, data, oldstart + 2 * FileSystem.BLOCK_SIZE);
    }
    
}
