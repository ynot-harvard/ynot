package filesystem.subsystem;

import filesystem.disk.*;
import filesystem.inode.*;
import filesystem.*;
import filesystem.util.*;
import filesystem.buffercache.*;

public class Directory {
    public Inode inode;
    
    public Directory(Inode inode) {
        this.inode = inode;
    }
    
    public void add(DirectoryEntry de) {
        //linear search through blocks for free entry: entry is free if inode = 0 (root shouldn't be in any directory)
        BlockIterator bi = inode.blockTable.iterator();
        
        int logblkid = 0;
        while (bi.hasNext()) {
            int blkid = bi.next();
            if (blkid == 0) {
                blkid = inode.blockTable.alloc(logblkid);
            }
            
            Buffer buf = FileSystem.bufferCache.bread(blkid);
            DirectoryBlock db = new DirectoryBlock(buf.data, buf.data.length);
            for (int i = 0; i < db.entryCount; i++) {
                DirectoryEntry e = db.get(i);
                if (e.inodeid == 0) {
                    db.put(de, i);
                    FileSystem.bufferCache.bwrite(buf);
                    FileSystem.bufferCache.brelse(buf);
                    return;
                }
            }
                        
            FileSystem.bufferCache.brelse(buf);            
            logblkid++;            
        }
        
        //need to last block
        int blkid = inode.blockTable.alloc(logblkid);
        Buffer buf = FileSystem.bufferCache.bread(blkid);
        DirectoryBlock db = new DirectoryBlock(buf.data, buf.data.length);
        db.put(de, 0);
        FileSystem.bufferCache.bwrite(buf);
        FileSystem.bufferCache.brelse(buf);
        FileSystem.inodeCache.iwrite(inode);
    }
    
    public DirectoryIterator iterator() {
        return new DirectoryIterator(this);
    }
}
