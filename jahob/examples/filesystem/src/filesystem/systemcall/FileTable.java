package filesystem.systemcall;

public class FileTable {
    public final FileTableEntry[] fileTable;
    private int index;
        
    public FileTable(int size) {
        fileTable = new FileTableEntry[size];
        
        for (int i = 0; i < size; i++) {
            FileTableEntry fileTableEntry = new FileTableEntry(i);
            fileTableEntry.clear();
            fileTable[i] = fileTableEntry;
        }
        
        index = -1;
    }
    
    public FileTableEntry alloc() {
        int old = index;
        
        index = (index + 1) % fileTable.length;
        while (fileTable[index].inode != null && old != index) 
            index = (index + 1) % fileTable.length;
                
        return fileTable[index];
    }
    
    public void free (FileTableEntry fte) {
        fileTable[fte.index].clear();
    }
}
