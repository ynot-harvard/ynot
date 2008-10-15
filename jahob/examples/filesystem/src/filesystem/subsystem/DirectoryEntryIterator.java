package filesystem.subsystem;

import filesystem.util.*;

public class DirectoryEntryIterator /* implements Iterator but need generics */ {    
    public static final int FILENAME_SIZE = 16;
    public static final int DIRENTRY_SIZE = FILENAME_SIZE + 4;     
    
    private byte[] block;
    private int eindex;
    private int maxindex;
    private int count;
    
    public DirectoryEntryIterator (byte[] block, int count) {
        this.block = block;
        this.eindex = 0;
        this.maxindex = count / DIRENTRY_SIZE;        
    }
    
    public DirectoryEntry next() {
        int bindex = eindex * DIRENTRY_SIZE;                      
                
        //assume inode id is int
        int inodeid = ByteArrayOperation.convertToInt(block, bindex);
        String filename = new String (block, bindex + 4, FILENAME_SIZE);
        eindex++;
        return new DirectoryEntry(inodeid, filename);
    }
    
    public boolean hasNext() {
        return eindex <= maxindex;
    }
    
}


