package filesystem.systemcall;

public class UserFileTable {
    public final FileDescriptor[] descriptors;
    public int index;
        
    public UserFileTable(int size) {
        descriptors = new FileDescriptor[size];
        
        for (int i = 0; i < size; i++) {
            FileDescriptor d = new FileDescriptor(i);
            d.clear();
            descriptors[i] = d;
        }
        
        index = -1;
    }
    
    public FileDescriptor alloc() {
        int old = index;
        
        index = (index + 1) % descriptors.length;
        while (descriptors[index].fileTableEntry != null && old != index) 
            index = (index + 1) % descriptors.length;
                
        return descriptors[index];
    }
    
    public void free (FileDescriptor fd) {
        descriptors[fd.index].clear();
    }
}
