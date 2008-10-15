package filesystem.subsystem;

import filesystem.util.*;

public class DirectoryBlock /* implements Iterator but need generics */ {    
    public static final int FILENAME_SIZE = 16;
    public static final int DIRENTRY_SIZE = FILENAME_SIZE + 4;     
    
    private byte[] block;        
    public /*readonly*/ int entryCount;
    
    public DirectoryBlock (byte[] block, int count) {
        this.block = block;        
        this.entryCount = count / DIRENTRY_SIZE;        
    }
    
    //requires eindex <= maxindex
    public DirectoryEntry get(int eindex) {
        int bindex = eindex * DIRENTRY_SIZE;                      
                
        //assume inode id is int
        int inodeid = ByteArrayOperation.convertToInt(block, bindex);
        String filename = ByteArrayOperation.convertToString (block, bindex + 4, FILENAME_SIZE);
        return new DirectoryEntry(inodeid, filename);
    }
        
    public void put (DirectoryEntry de, int eindex) {
        int bindex = eindex * DIRENTRY_SIZE;                      
                
        ByteArrayOperation.mzero(block, bindex, DIRENTRY_SIZE);
        //assume inode id is int
        ByteArrayOperation.convertToBytes(de.inodeid, block, bindex);        
        ByteArrayOperation.convertToBytes(de.filename, block, bindex + 4, FILENAME_SIZE);
    }
}


