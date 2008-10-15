package filesystem.subsystem;

public class DirectoryEntry {
    public int inodeid;
    public String filename; //filename
    
    
    public DirectoryEntry(int inodeid, String filename) {        
        this.inodeid = inodeid;
        this.filename = filename;
    }
    
}
