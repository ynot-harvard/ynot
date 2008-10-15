package filesystem.subsystem;

import filesystem.inode.*;
import filesystem.*;
import filesystem.buffercache.*;

public class DirectoryIterator {
    private Inode inode;
    private BlockIterator bi;
    private int logblkid;
    private boolean hasNext;
    private DirectoryEntry entry;
    private DirectoryEntry[] curblock;
    private int curblocki;
    
    public DirectoryIterator(Directory dir) {
        this.inode = dir.inode;
        this.bi = inode.blockTable.iterator();
        this.curblocki = -1;
        this.curblock = new DirectoryEntry[FileSystem.BLOCK_SIZE / DirectoryBlock.DIRENTRY_SIZE];
    }
    
    
    public boolean hasNext() {
        if (curblocki != -1)
            return true;
        
        int blkid;
        while (true) {
            if (!bi.hasNext())
                return false;
            
            blkid = bi.next();
            if (blkid != 0)
                break;
        }
        
        curblocki = 0;
        Buffer buf = FileSystem.bufferCache.bread(blkid);
        
        DirectoryBlock db = new DirectoryBlock(buf.data, buf.data.length);
        
        for (int i = 0; i < db.entryCount; i++) {
            curblock[i] = db.get(i);
        }
        
        FileSystem.bufferCache.brelse(buf);
        
        return true;
    }
    
    //could return null, curblocki should never be -1 on entry
    public DirectoryEntry next() {
        DirectoryEntry de = curblock[curblocki];
        
        if (curblocki == FileSystem.BLOCK_SIZE / DirectoryBlock.DIRENTRY_SIZE - 1)
            curblocki = -1;
        else
            curblocki++;
        
        return de;                
    }
    
}
