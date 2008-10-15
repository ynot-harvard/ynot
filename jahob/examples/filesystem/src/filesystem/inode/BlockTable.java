package filesystem.inode;

import filesystem.buffercache.*;
import filesystem.*;
import filesystem.util.*;

public class BlockTable {
    //the abstraction is an injective function in LogicalBlockIds -> RealBlockIds
    
    public static final int DIRECT_BLOCK_COUNT = 9;
    public static final int ONDISK_SIZE = (DIRECT_BLOCK_COUNT + 4) * 4;
    
    //contains 0 for empty slots
    private final int[] direct;
    private int singleIndirect;
    private int doubleIndirect;
    private int tripleIndirect;    
    public /*readonly*/ int blockCount;
    
    public BlockTable() {
        this.direct = new int[DIRECT_BLOCK_COUNT];
    }
        
    public BlockIterator iterator() {
        return new BlockIterator(this);
    }
    
    public void clear () {
        blockCount = 0;
        for (int i = 0; i < direct.length; i++) {
            direct[i] = 0;
        }
        
        singleIndirect = 0;
        doubleIndirect = 0;
        tripleIndirect = 0;
    }
    
    //BLOCK IS ZEROED!
    //does not overwrite any blocks
    //returns logblkid's real blk id
    public int alloc(int logblkid) {
        int blkidsperblock = FileSystem.BLOCK_SIZE / 4;
        int numdirect = direct.length;
        int numsingle = blkidsperblock;
        int numdouble = blkidsperblock * blkidsperblock;
        int numtriple = blkidsperblock * blkidsperblock * blkidsperblock;
        
        if (level(logblkid) == 0) {
            int curblkid = direct[logblkid];
            if (curblkid == 0) {
                curblkid = ballocz();
                direct[logblkid] = curblkid;   
                blockCount++;
            }
            
            return curblkid;            
        } else if (level(logblkid) == 1) {
            if (singleIndirect == 0) {
                singleIndirect = ballocz();                
            }
                        
            int level1_index = logblkid - numdirect;
            int level2_blkid = index(singleIndirect, level1_index);
            if (level2_blkid == 0) {
                level2_blkid = ballocz();
                set(singleIndirect, level1_index, level2_blkid); 
                blockCount++;
            }
                
            return level2_blkid;
        } else if (level(logblkid) == 2) {
            if (doubleIndirect == 0) {
                doubleIndirect = ballocz();                
            }
            
            int level3_localblknum = logblkid - numsingle - numdirect;
            int level2_localblknum = level3_localblknum / blkidsperblock;
            
            int level1_index = level2_localblknum;
            int level2_blkid = index(doubleIndirect, level1_index);
            if (level2_blkid == 0) {
                level2_blkid = ballocz();
                set(doubleIndirect, level1_index, level2_blkid);                
            }
            
            int level2_index = level3_localblknum % blkidsperblock;
            int level3_blkid = index(level2_blkid, level2_index);
            if (level3_blkid == 0) {
                level3_blkid = ballocz();
                set(level2_blkid, level2_index, level3_blkid);    
                blockCount++;
            }
          
            return level3_blkid;
        } else if (level(logblkid) == 3) {
            if (tripleIndirect == 0)
                return 0;
            
            int level4_localblknum = logblkid - numdouble - numsingle - numdirect;
            int level3_localblknum = level4_localblknum / blkidsperblock / blkidsperblock;
            int level2_localblknum = level3_localblknum / blkidsperblock;
            
            int level1_index = level2_localblknum;
            int level2_blkid = index(tripleIndirect, level1_index);
            if (level2_blkid == 0) {                
                level2_blkid = ballocz();
                set(doubleIndirect, level1_index, level2_blkid);                
            }
            
            int level2_index = level3_localblknum % blkidsperblock;
            int level3_blkid = index(level2_blkid, level2_index);
            if (level3_blkid == 0) {
                level3_blkid = ballocz();
                set(level2_blkid, level2_index, level3_blkid);                  
            }
            
            int level3_index = level4_localblknum % blkidsperblock;
            int level4_blkid = index(level3_blkid, level3_index);
            if (level4_blkid == 0) {
                level4_blkid = ballocz();
                set(level3_blkid, level3_index, level4_blkid);         
                blockCount++;
            }
            
            return level4_blkid;
        } else {
            return 0;
        }
    }
    
    public void free(int logblkid) {
        int blkidsperblock = FileSystem.BLOCK_SIZE / 4;
        int numdirect = direct.length;
        int numsingle = blkidsperblock;
        int numdouble = blkidsperblock * blkidsperblock;
        int numtriple = blkidsperblock * blkidsperblock * blkidsperblock;
        
        if (level(logblkid) == 0) {
            bfree (direct[logblkid]);
            direct[logblkid] = 0;
            
            return;
            
        } else if (level(logblkid) == 1) {
            if (singleIndirect == 0)
                return;
            
            int local_logblkid = logblkid - numdirect;            
            int level2_blkid = index(singleIndirect, local_logblkid);
            bfree(level2_blkid);
            set(singleIndirect, local_logblkid, 0);
            blockCount--;
            
            if (bempty(singleIndirect)) {
                bfree(singleIndirect);
                singleIndirect = 0;
            }
            
            return;
            
        } else if (level(logblkid) == 2) {
            if (doubleIndirect == 0)
                return;
            
            int level3_localblknum = logblkid - numsingle - numdirect;
            int level2_localblknum = level3_localblknum / blkidsperblock;
            
            int level1_index = level2_localblknum;
            
            int level2_blkid = index(doubleIndirect, level1_index);
            if (level2_blkid == 0)
                return;
            
            int level2_index = level3_localblknum % blkidsperblock;
            int level3_blkid = index(level2_blkid, level2_index);
            bfree(level3_blkid);
            set (level2_blkid, level2_index, 0);
            blockCount--;
            
            if (bempty(level2_blkid)) {
                bfree(level2_blkid);
                set(doubleIndirect, level1_index, 0);
                
                if (bempty(doubleIndirect)) {
                    bfree(doubleIndirect);
                    doubleIndirect = 0;
                }
            }                     
            
            return;
            
        } else if (level(logblkid) == 3) {
            if (tripleIndirect == 0)
                return;
            
            int level4_localblknum = logblkid - numdouble - numsingle - numdirect;
            int level3_localblknum = level4_localblknum / blkidsperblock / blkidsperblock;
            int level2_localblknum = level3_localblknum / blkidsperblock;
            
            int level1_index = level2_localblknum;
            int level2_blkid = index(tripleIndirect, level1_index);            
            if (level2_blkid == 0)
                return;
            
            int level2_index = level3_localblknum % blkidsperblock;
            int level3_blkid = index(level2_blkid, level2_index);
            if (level3_blkid == 0)
                return;
            
            int level3_index = level4_localblknum % blkidsperblock;
            int level4_blkid = index(level3_blkid, level3_index);
            bfree(level4_blkid);
            set(level3_blkid, level3_index, 0);
            blockCount--;
            
            if (bempty(level3_blkid)) {
                bfree(level3_blkid);
                set (level2_blkid, level2_index, 0);
                
                if (bempty(level2_blkid)) {
                    bfree(level2_blkid);
                    set (tripleIndirect, level1_index, 0);
                    
                    if (bempty(tripleIndirect)) {
                        bfree(tripleIndirect);
                        tripleIndirect = 0;
                    }
                }
            }
            
            return;
        } 
        
        return;
    }
    
    public int ballocz() {
        int blkid = FileSystem.subSystem.alloc();
        Buffer buf = FileSystem.bufferCache.bread(blkid);
        ByteArrayOperation.mzero(buf.data);
        FileSystem.bufferCache.bwrite(buf);
        FileSystem.bufferCache.brelse(buf);        
        return blkid;
    }
    
    public void bfree (int blkid) {
        if (blkid == 0)
            return;
        
        FileSystem.subSystem.free(blkid);
    }
    
    public boolean bempty (int blkid) {        
        Buffer buf = FileSystem.bufferCache.bread(blkid);
        boolean ans = ByteArrayOperation.iszero(buf.data);        
        FileSystem.bufferCache.brelse(buf);
        return ans;
    }
    
    //returns 0 if logblkid not mapped
    public int map(int logblkid) {
        int blkidsperblock = FileSystem.BLOCK_SIZE / 4;
        int numdirect = direct.length;
        int numsingle = blkidsperblock;
        int numdouble = blkidsperblock * blkidsperblock;
        int numtriple = blkidsperblock * blkidsperblock * blkidsperblock;
        
        if (level(logblkid) == 0) {
            return direct[logblkid];
        } else if (level(logblkid) == 1) {
            if (singleIndirect == 0)
                return 0;
            
            int local_logblkid = logblkid - numdirect;
            
            return index(singleIndirect, local_logblkid);
        } else if (level(logblkid) == 2) {
            if (doubleIndirect == 0)
                return 0;
            
            int level3_localblknum = logblkid - numsingle - numdirect;
            int level2_localblknum = level3_localblknum / blkidsperblock;
            
            int level1_index = level2_localblknum;
            
            int level2_blkid = index(doubleIndirect, level1_index);
            if (level2_blkid == 0)
                return 0;
            
            int level2_index = level3_localblknum % blkidsperblock;
            int level3_blkid = index(level2_blkid, level2_index);
            
            return level3_blkid;
        } else if (level(logblkid) == 3) {
            if (tripleIndirect == 0)
                return 0;
            
            int level4_localblknum = logblkid - numdouble - numsingle - numdirect;
            int level3_localblknum = level4_localblknum / blkidsperblock / blkidsperblock;
            int level2_localblknum = level3_localblknum / blkidsperblock;
            
            int level1_index = level2_localblknum;
            int level2_blkid = index(tripleIndirect, level1_index);
            if (level2_blkid == 0)
                return 0;
            
            int level2_index = level3_localblknum % blkidsperblock;
            int level3_blkid = index(level2_blkid, level2_index);
            if (level3_blkid == 0)
                return 0;
            
            int level3_index = level4_localblknum % blkidsperblock;
            int level4_blkid = index(level3_blkid, level3_index);
            
            return level4_blkid;
        } else {
            return 0;
        }
    }
    
    private void set(int blkid, int index, int val) {
        Buffer buf = FileSystem.bufferCache.bread(blkid);
        int addr = ByteArrayOperation.convertToInt(buf.data, index * 4);
        ByteArrayOperation.convertToBytes(val, buf.data, index * 4);
        FileSystem.bufferCache.bwrite(buf);
        FileSystem.bufferCache.brelse(buf);
    }
    
    private int index(int blkid, int index) {
        Buffer buf = FileSystem.bufferCache.bread(blkid);
        int addr = ByteArrayOperation.convertToInt(buf.data, index * 4);
        FileSystem.bufferCache.brelse(buf);
        return addr;
    }
    
    private int level(int logblkid) {
        int blkidsperblock = FileSystem.BLOCK_SIZE / 4;
        int numdirect = direct.length;
        int numsingle = blkidsperblock;
        int numdouble = blkidsperblock * blkidsperblock;
        int numtriple = blkidsperblock * blkidsperblock * blkidsperblock;
        
        
        if (logblkid >= 0 && logblkid < numdirect)
            return 0;
        else if (logblkid >= numdirect && logblkid < numsingle + numdirect)
            return 1;
        else if (logblkid >= numsingle + numdirect && logblkid < numdouble + numsingle + numdirect)
            return 2;
        else if (logblkid >= numdouble + numsingle + numdirect && logblkid < numtriple + numdouble + numsingle + numdirect)
            return 3;
        else
            return -1;
    }
    
    public void serialize(byte[] buffer, int start) {
        int i;
        for (i = 0; i < direct.length; i++) {
            ByteArrayOperation.convertToBytes(direct[i], buffer, start + i * 4);
        }
        
        ByteArrayOperation.convertToBytes(singleIndirect, buffer, start + i * 4);
        ByteArrayOperation.convertToBytes(doubleIndirect, buffer, start + i * 4 + 4);
        ByteArrayOperation.convertToBytes(tripleIndirect, buffer, start + i * 4 + 8);
        ByteArrayOperation.convertToBytes(blockCount, buffer, start + i * 4 + 12);
    }
    
    public void unserialize(byte[] buffer, int start) {
        int i;
        for (i = 0; i < direct.length; i++) {
            direct[i] = ByteArrayOperation.convertToInt(buffer, start + i * 4);
        }
                
        singleIndirect = ByteArrayOperation.convertToInt(buffer, start + i * 4);
        doubleIndirect = ByteArrayOperation.convertToInt(buffer, start + i * 4 + 4);
        tripleIndirect = ByteArrayOperation.convertToInt(buffer, start + i * 4 + 8);
        blockCount = ByteArrayOperation.convertToInt(buffer, start + i * 4 + 12);
    }
}