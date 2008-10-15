import filesystem.systemcall.*;
import filesystem.*;
import filesystem.disk.*;

public class Test {
        
    public static void main(String[] args) {
        BlockedDisk disk = new BlockedDisk(4096 * 4096);
        MakeFileSystem.make(disk);
        //FileSystem.init(disk);
        FileSystem.load(disk);
        
        SystemCall sc = FileSystem.systemCall;
        
        String s1 = "hello, my name is joe";
        String s2 = "hello, my name is sam";
        
        byte[] data = new byte[s1.length()];
        
        sc.create("/file1.txt");
        sc.mkdir("/dir1");
        sc.create("/dir1/file2.txt");
        
        FileDescriptor ufte1 = sc.open("/dir1/file2.txt");
        sc.write(ufte1, s1.getBytes(), s1.length());
        sc.close(ufte1);
        
        FileDescriptor ufte2 = sc.open("/file1.txt");
        sc.write(ufte2, s1.getBytes(), s2.length());
        sc.close(ufte2);
        
        ufte1 = sc.open("/dir1/file2.txt");
        sc.read(ufte1, data, s1.length());
        sc.close(ufte1);
        System.out.println("file2.txt: ");
        pstr(data);
        
        ufte2 = sc.open("/file1.txt");
        sc.read(ufte2, data, s2.length());
        sc.close(ufte2);        
        System.out.println("file2.txt: ");
        pstr(data);
        
        System.out.println("DONE");
    }
    
    private static void pstr (byte[] data) {
        String str = new String (data, 0, data.length);
        //for (int i = 0; i < data.length; i++)
           // System.out.print(data[i]);
        ///System.out.println();
        System.out.println(str);
    }
}
