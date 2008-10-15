/*
 * Bmap.java
 *
 * Created on April 17, 2005, 1:48 PM
 */

package filesystem.inode;

import filesystem.buffercache.*;
import filesystem.*;
import filesystem.util.*;

public class Bmap {
            
     //This algorithm needs to take advantage of more OOP abstraction to reduce 
    //complexity and increase verifiability
    //returns blkid
    //requries offset does not exceed maximum file size (tripleindirectlimit)
    public static int bmap (Inode inode, int offset) {
        BufferCache bufferCache = FileSystem.bufferCache;
        
        BlockTable bt = inode.blockTable;
        
        int logblkid = offset / FileSystem.BLOCK_SIZE;
        int entriesperblock = FileSystem.BLOCK_SIZE / 4;
        
        int directlimit =  bt.direct.length;
        int singleindirectlimit = directlimit + entriesperblock;
        int doubleindirectlimit = singleindirectlimit + entriesperblock * entriesperblock;
        int tripleindirectlimit = doubleindirectlimit + entriesperblock * entriesperblock * entriesperblock;
        
        if (logblkid < directlimit) {
            return bt.direct[logblkid];            
        }
        else if (logblkid < singleindirectlimit) {
            Buffer buf = bufferCache.bread(bt.singleIndirect);
            int wordindex = (logblkid - directlimit) * 4;
            return ByteArrayOperation.convertToInt(buf.data, wordindex);
        }
        else if (logblkid < doubleindirectlimit) {                        
            Buffer buf = bufferCache.bread(bt.doubleIndirect);
            int wordindex1 = (logblkid - singleindirectlimit) / entriesperblock * 4;
            buf = bufferCache.bread(ByteArrayOperation.convertToInt(buf.data, wordindex1));
            int wordindex2 = (logblkid - singleindirectlimit) % entriesperblock * 4;
            //bug: have to index buf and release bufs
            return wordindex2;
        }
        else if (logblkid < tripleindirectlimit) {
            Buffer buf = bufferCache.bread(bt.tripleIndirect);
            int wordindex1 = (logblkid - doubleindirectlimit) / entriesperblock / entriesperblock * 4;
            buf = bufferCache.bread(ByteArrayOperation.convertToInt(buf.data, wordindex1));
            int wordindex2 = (logblkid - doubleindirectlimit) / entriesperblock % entriesperblock * 4;
            buf = bufferCache.bread(ByteArrayOperation.convertToInt(buf.data, wordindex2));
            int wordindex3 = (logblkid - doubleindirectlimit) % (entriesperblock * entriesperblock) * 4;
            //bug: have to index buf and release bufs
            return wordindex3;
        }        
        else {
            return -1; //should never happen
        }
    }
    
}
