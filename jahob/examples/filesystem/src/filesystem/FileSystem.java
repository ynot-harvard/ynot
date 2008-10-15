package filesystem;

import filesystem.disk.*;
import filesystem.buffercache.*;
import filesystem.inode.*;
import filesystem.subsystem.*;
import filesystem.systemcall.*;

public class FileSystem {
    private static final int BUFFERCACHE_SIZE = 10;
    private static final int INODECACHE_SIZE = 10;               
    private static final int GLOBAL_FILETABLE_SIZE = 100;
    private static final int USER_FILETABLE_SIZE = 100;
    
    public static final int BLOCK_SIZE = 4096;    
        
    public static BlockedDisk disk;
    public static BufferCache bufferCache;
    public static InodeCache inodeCache;
    public static SubSystem subSystem;
    public static SuperBlock superBlock;
    public static SystemCall systemCall;
    public static FileTable globalFileTable;
    public static UserFileTable userFileTable;    
    
    public static void init (BlockedDisk d) {        
        disk = d;
        bufferCache = new BufferCache(BUFFERCACHE_SIZE);
        inodeCache = new InodeCache(INODECACHE_SIZE);
        subSystem = new SubSystem();
        globalFileTable = new FileTable(GLOBAL_FILETABLE_SIZE);
        userFileTable = new UserFileTable(USER_FILETABLE_SIZE);
        superBlock = new SuperBlock();
    }
    
    public static void load(Disk d) {             
        //loading the super block        
        byte[] superdata = new byte[BLOCK_SIZE * 3];
        disk.read(1, 0, superdata, 0, BLOCK_SIZE * 3);
        superBlock.unserialize(superdata, 0);
    }
    
}