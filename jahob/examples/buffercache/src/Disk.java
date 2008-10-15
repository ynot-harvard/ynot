public /*: claimedby BufferCache */ class Disk {                    
    public static final int BLOCK_SIZE = 4096;
    public static final int DISK_SIZE = 16777216;
    public static final int BLOCK_COUNT = 4096;
    
    public static /*readonly*/ byte[] data;
    
    public static void init () {
         data = new byte[DISK_SIZE];
    }
   
    //read disk from start to start + length into data    
    public static void read (int blkid, int blkstart, byte[] buffer, int bufstart, int len) {        
        int diskstart = BLOCK_SIZE * blkid;
        
        int i = 0;
        while (i < len) {
            buffer[bufstart + i] = data[diskstart + i];
            i = i + 1;
    	}//*/
    }
            
    //write buffer to disk from start to length
    public static void write (int blkid, int bufstart, byte[] buffer, int blkstart, int len) {
        int diskstart = BLOCK_SIZE * blkid;
        
        int i = 0;
        while (i < len) {
    		data[diskstart + i] = buffer[bufstart + i];
                i = i + 1;
    	}
    }
}
