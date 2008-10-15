package filesystem.systemcall;

import filesystem.*;
import filesystem.inode.*;
import filesystem.buffercache.*;
import filesystem.util.*;

public class Write {
    
    
    public static int write (FileDescriptor fd, byte[] data, int count) {
        FileTableEntry fte = fd.fileTableEntry;
        Inode inode = fte.inode;
        inode.isLocked = true;
        
        int totalwritten = 0;
        while (totalwritten != count) {
            int logblkid = (fte.offset + totalwritten) / FileSystem.BLOCK_SIZE;
            int blkid = inode.blockTable.map(logblkid);
            int blkoffset = (fte.offset + totalwritten) % FileSystem.BLOCK_SIZE;
            
            if (blkid == 0) {
                blkid = inode.blockTable.alloc((fte.offset + totalwritten) / FileSystem.BLOCK_SIZE * FileSystem.BLOCK_SIZE);
            }
            
            int towrite = count - totalwritten > FileSystem.BLOCK_SIZE - blkoffset ? 
                            FileSystem.BLOCK_SIZE - blkoffset : 
                            count - totalwritten ;
            
            Buffer buf = FileSystem.bufferCache.bread(blkid);
            ByteArrayOperation.mcopy(data, totalwritten, buf.data, blkoffset, towrite);            
            FileSystem.bufferCache.bwrite (buf);
            FileSystem.bufferCache.brelse(buf);
            totalwritten += towrite;
        }
        
        inode.isLocked = false;
        fte.offset += totalwritten;
        return totalwritten;
    }
    
}
