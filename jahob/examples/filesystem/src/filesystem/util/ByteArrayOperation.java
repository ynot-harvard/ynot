/*
 * ByteConversion.java
 *
 * Created on April 14, 2005, 12:49 PM
 */

package filesystem.util;

/**
 *
 * @author sbugrara
 */
public class ByteArrayOperation {
    
    /** Creates a new instance of ByteConversion */
    public ByteArrayOperation() {
    }
           
    public static void convertToBytes(int[] val, byte[] array, int start) {
        for (int i = 0; i < val.length; i++) {
            convertToBytes(val[i], array, start + i * 4);
        }
    }
    
    public static void convertToBytes(int val, byte[] array, int start) {
        array[start] = (byte) ((val << 24 >>> 24) & 255);
        array[start + 1] = (byte) ((val << 16 >>> 24) & 255);
        array[start + 2] = (byte) ((val << 8 >>> 24) & 255);
        array[start + 3] = (byte) ((val >>> 24) & 255);        
    }
    
    public static void convertToBytes(boolean val, byte[] array, int start) {
        convertToBytes(val ? 1 : 0, array, start);
    }
    
    public static int convertToInt(byte[] array, int start) {
        int j0 = array[start + 0] < 0 ? array[start + 0] + 256 : array[start + 0];
        int j1 = array[start + 1] < 0 ? array[start + 1] + 256 : array[start + 1];
        int j2 = array[start + 2] < 0 ? array[start + 2] + 256 : array[start + 2];
        int j3 = array[start + 3] < 0 ? array[start + 3] + 256 : array[start + 3];
        
        return j3 << 24 | j2 << 16 | j1 << 8 | j0;        
    }
    
    public static void convertToIntArray(byte[] array, int start, int[] val) {
        for (int i = 0; i < val.length; i++) {
            val[i] = convertToInt(array, start + i * 4);
        }
    }
    
    public static boolean convertToBoolean(byte[] array, int start) {
        return convertToInt(array, start) == 1 ? true : false;
        
    }
    
    public static void mzero (byte[] a) {
        mzero(a, 0, a.length);
    }
    
    
    public static void mzero (byte[] a, int start, int count) {
        for (int i = 0; i < count; i++) {
            a[i + start] = 0;
        }
    }
    
        
    public static boolean iszero (byte[] a) {
        for (int i = 0; i < a.length; i++) 
            if (a[i] != 0)
                return false;
        
        return true;
    }
    
    
    public static void mcopy (byte[] src, int srcstart, byte[] dst, int dststart, int count) {
        for (int i = 0; i + srcstart < src.length && i + dststart < dst.length && i < count; i++) {
            dst[dststart + i] = src[srcstart + i];
        }
    }

    //convert x bytes to String starting at start in data where x = min(indexof(0), size)
    public static String convertToString (byte[] data, int start, int size) {
        int i;
        
        for (i = 0; i < size; i++) 
            if (data[i + start] == 0)
                break;
        
        return new String (data, start, i);
    }
    
    public static void convertToBytes (String val, byte[] data, int start, int size) {
        byte[] bs = val.getBytes();
        
        mcopy(bs, 0, data, start, size);
    }
}
