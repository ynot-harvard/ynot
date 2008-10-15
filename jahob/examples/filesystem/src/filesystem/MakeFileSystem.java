package filesystem;

import filesystem.inode.*;
import filesystem.disk.*;
import filesystem.buffercache.*;
import filesystem.subsystem.*;

public class MakeFileSystem {
    
    /*DISK ARGUMENTS*/    
    static final int DISK_SIZE = 4096 * 4096;
    
    
    /*CONFIGURATION ARGUMENTS*/
    
    //include invariants for these values
    private static final int BOOTBLOCK = 0;
    private static final int SUPERBLOCK = 1;
    private static final int FREEBLOCKS_LIST = 2;
    private static final int FREEINODES_LIST = 3;
    private static final int INODELIST_START = 4;
    private static final int FILESYSTEM_SIZE = DISK_SIZE;
    private static final int INODE_COUNT = 100;    
    private static final int INODE_SIZE = 9 * 4 + BlockTable.ONDISK_SIZE; //bytes       
    
    
    
    /* create root inode
     * initialize super block
     *
     */
    public static void make(BlockedDisk disk) {
        FileSystem.init(disk);
        
        Inode root = new Inode();
        root.fileType = Inode.DIRECTORY;
        
        byte[] inode = new byte[INODE_SIZE];
        root.serialize(inode, 0);
        disk.write(INODELIST_START * FileSystem.BLOCK_SIZE, inode, 0, inode.length);
        
        SuperBlock superBlock = FileSystem.superBlock;          
        superBlock.freeBlocksStart = FREEBLOCKS_LIST;
        superBlock.freeInodesStart = FREEINODES_LIST;
        superBlock.inodeCount = INODE_COUNT;
        superBlock.inodeListStart = INODELIST_START;
        superBlock.inodeSize = INODE_SIZE;
        superBlock.fileSystemSize = DISK_SIZE;
        superBlock.rootInodeId = 0;
                
        superBlock.freeInodeSet.freeInodeCount = INODE_COUNT - 1; //exclude the root
        superBlock.freeInodeSet.harvest();                        
        
        int block_count = FILESYSTEM_SIZE / FileSystem.BLOCK_SIZE;        
        int freeblock_start = INODELIST_START + INODE_COUNT;
                        
        superBlock.freeBlockSet.freeBlockCount = 0;
        for (int i = freeblock_start; i < block_count; i++) {
            superBlock.freeBlockSet.add(i);
        }                
        
        byte[] block = new byte[FileSystem.BLOCK_SIZE * 3];
        superBlock.serialize(block, 0);
        disk.write(SUPERBLOCK * FileSystem.BLOCK_SIZE, block, 0, FileSystem.BLOCK_SIZE * 3);
    }
    
}