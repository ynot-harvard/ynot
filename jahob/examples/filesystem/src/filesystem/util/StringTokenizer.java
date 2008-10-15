package filesystem.util;

public class StringTokenizer implements Iterator {
    private char[] str;
    private char[] delim;
    private int index;
    
    /** Creates a new instance of StringTokenizer */
    public StringTokenizer(String str, String delim) {
        this.str = str.toCharArray();
        this.delim = delim.toCharArray();
        this.index = 0;
    }
    
    public boolean hasNext() {
        return index < str.length;
    }   
    
    public String next() {            
        for (int i = index; i < str.length; i++) {
            if (delimFound(i)) {                
                String ret = new String(str, index, i - index);                
                index = i + delim.length;
                return ret;
            }
        }
                
        String ret = new String(str, index, str.length - index);
        index = str.length;
        return ret;
    }
    
    private boolean delimFound (int start) {
        if (start + delim.length >= str.length)
            return false;
        
        for (int i = 0; i < delim.length; i++, start++) {
            if (str[start] != delim[i])
                return false;
        }
        
        return true;
    }
}
