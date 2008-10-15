package filesystem.inode;

/**
 * fileType == DIRECTORY || fileType == REGULAR
 * time*LastModified' >= timeInodeLastModified
 * numLinks >= 0
 * fileSize >= 0
 * isDirtyFromInodeChange --> isDirtyFromFileChange
 * refCount >= 0
 *
 */

import filesystem.util.*;

public class Inode {
    public static final int FREE = 0;
    public static final int DIRECTORY = 1;
    public static final int REGULAR = 2;
    
    public int id;
    public int fileType;
    public int timeInodeLastModified;
    public int timeFileLastModified;
    public int linkCount;
    public boolean isLocked;
    public boolean isProcessWaitingForInode;
    public boolean isDirtyFromFileChange;
    public boolean isDirtyFromInodeChange;
    public int refCount;
    
    public boolean hasBeenModified;
    public final InodeNode freelistNode;
    public final InodeNode hashqueuesNode;
    
    public final BlockTable blockTable;
    
    public Inode() {                
        blockTable = new BlockTable();
        freelistNode = new InodeNode(this);
        hashqueuesNode = new InodeNode(this);
        
        clear();
        blockTable.clear();
    }
    
    private int convertToInt(boolean b) {
        return b ? 1 : 0;
    }
    
    private boolean convertToBoolean(int i) {
        if (i != 0 && i != 1)
            throw new RuntimeException();
        
        return i == 0 ? false : true;
    }
    
    public void serialize(byte[] buffer, int start) {
        //format inode into bytes and write into buffer
        ByteArrayOperation.convertToBytes(fileType, buffer, start); start += 4;
        ByteArrayOperation.convertToBytes(timeInodeLastModified, buffer, start); start += 4;
        ByteArrayOperation.convertToBytes(timeFileLastModified, buffer, start); start += 4;
        ByteArrayOperation.convertToBytes(linkCount, buffer, start); start += 4;
        ByteArrayOperation.convertToBytes(convertToInt(isLocked), buffer, start); start += 4;
        ByteArrayOperation.convertToBytes(convertToInt(isProcessWaitingForInode), buffer, start); start += 4;
        ByteArrayOperation.convertToBytes(convertToInt(isDirtyFromFileChange), buffer, start); start += 4;
        ByteArrayOperation.convertToBytes(convertToInt(isDirtyFromInodeChange), buffer, start); start += 4;
        ByteArrayOperation.convertToBytes(refCount, buffer, start); start += 4;
        System.out.println("buffer.length=" + buffer.length + ";start=" + start);
        blockTable.serialize(buffer, start);
    }
    
    public void unserialize(byte[] buffer, int start) {
        fileType = ByteArrayOperation.convertToInt(buffer, start);
        timeInodeLastModified = ByteArrayOperation.convertToInt(buffer, start); start += 4;
        timeFileLastModified = ByteArrayOperation.convertToInt(buffer, start); start += 4;
        linkCount = ByteArrayOperation.convertToInt(buffer, start); start += 4;
        isLocked = convertToBoolean(ByteArrayOperation.convertToInt(buffer, start)); start += 4;
        isProcessWaitingForInode = convertToBoolean(ByteArrayOperation.convertToInt(buffer, start)); start += 4;
        isDirtyFromFileChange = convertToBoolean(ByteArrayOperation.convertToInt(buffer, start)); start += 4;
        isDirtyFromInodeChange = convertToBoolean(ByteArrayOperation.convertToInt(buffer, start)); start += 4;
        refCount = ByteArrayOperation.convertToInt(buffer, start); start += 4;
        blockTable.unserialize(buffer, start);
    }
    
    public void clear() {
        id = -1;
        fileType = 0;
        timeInodeLastModified = -1;
        timeFileLastModified = -1;
        linkCount = 0;        
        isLocked = false;
        isProcessWaitingForInode = false;
        isDirtyFromFileChange = false;
        isDirtyFromInodeChange = false;
        refCount = 0;
    }
    
    public String toString() {
        p("INODE:");
        p("\tfileType=" + fileType);
        
        p("\tid" + id);
        p("\tfileType=" + fileType);
        p("\ttimeInodeLastModified" + timeInodeLastModified);
        p("\ttimeFileLastModified=" + timeFileLastModified);
        p("\tlinkCount=" + linkCount);
        p("\tfileSize=" + blockTable.blockCount);
        p("\tisLocked=" + isLocked);
        p("\tisProcessWaitingForInode=" + isProcessWaitingForInode);
        p("\tisDirtyFromFileChange=" + isDirtyFromFileChange);
        p("\tisDirtyFromInodeChange=" + isDirtyFromInodeChange);
        p("\trefCount=" + refCount);
        
        return null;
    }
    
    private void p(String s) {
        System.out.println(s);
    }
    
}
