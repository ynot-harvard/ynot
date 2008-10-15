package filesystem.systemcall;

import filesystem.*;
import filesystem.inode.*;
import filesystem.buffercache.*;
import filesystem.util.*;

public class Read {
    
    public static int read (FileDescriptor fd, byte[] data, int count) {
        FileTableEntry fte = fd.fileTableEntry;
        Inode inode = fte.inode;
        inode.isLocked = true;
        
        int totalread = 0;
        while (totalread != count) {
            int logblkid = (fte.offset + totalread) / FileSystem.BLOCK_SIZE;
            int blkid = inode.blockTable.map(logblkid);
            int blkoffset = (fte.offset + totalread) % FileSystem.BLOCK_SIZE;
            
            if (blkid == 0)
                break;
            
            int toread = count - totalread > FileSystem.BLOCK_SIZE - blkoffset ? 
                            FileSystem.BLOCK_SIZE - blkoffset : 
                            count - totalread ;
            
            Buffer buf = FileSystem.bufferCache.bread(blkid);
            ByteArrayOperation.mcopy(buf.data, blkoffset, data, totalread, toread);            
            FileSystem.bufferCache.brelse (buf);
            totalread += toread;
        }
        
        inode.isLocked = false;
        fte.offset += totalread;
        return totalread;
    }
}
