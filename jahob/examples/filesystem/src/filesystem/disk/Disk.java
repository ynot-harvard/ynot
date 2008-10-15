package filesystem.disk;

public class Disk {
    /*: specfield contents : "(Nat * byte) set" */
    
    public final /*readonly*/ byte[] data;
	
    public Disk(int size) 
    /*:
     	requires "size > 0"
     	modifies contents
     	ensures "contents = { (x, 0) | x : Nat & x < size }"
    */
    {
    	this.data = new byte[size];
    }
    
    
    //read data from start to start + length into data    
    public void read (int diskstart, byte[] buffer, int bufstart, int len) {
    	for (int i = 0; i < len; i++) {
    		buffer[bufstart + i] = data[diskstart + i];
    	}
    }
            
    //write buffer to data from start to length
    public void write (int diskstart, byte[] buffer, int bufstart, int len) {
       	for (int i = 0; i < len; i++) {
    		data[diskstart + i] = buffer[bufstart + i];
    	}
    }
}
