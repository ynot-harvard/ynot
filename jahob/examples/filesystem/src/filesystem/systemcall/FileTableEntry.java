package filesystem.systemcall;

import filesystem.inode.*;

public class FileTableEntry {
    public Inode inode;
    public int offset;
    public int refCount;
    
    public final int index;    
    
    public FileTableEntry(int index) {
        this.index = index;        
    }
    
    public void clear() {
        inode = null;
        offset = -1;
        refCount = 0;
    }
}
