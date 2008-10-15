package filesystem.systemcall;

public class FileDescriptor {
    public FileTableEntry fileTableEntry;  
    public final int index;
    
    public FileDescriptor(int index) {
        this.index = index;
    }
    
    public void clear () {
        fileTableEntry = null;
    }
    
}
