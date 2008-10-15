package filesystem.systemcall;

public class SystemCall {
    
    public static FileDescriptor create(String pathname) {
        return Create.create(pathname);
    }
    
    public static void close(FileDescriptor fd) {
        Close.close(fd);
    }
    
    public static int write(FileDescriptor fd, byte[] data, int count) {
        return Write.write(fd, data, count);
    }
    
    public static int read(FileDescriptor fd, byte[] data, int count) {
        return Read.read(fd, data, count);
    }
    
    public static FileDescriptor open(String pathname) {
        return Open.open(pathname);
    }
    
    public static void mkdir (String dirname) {
        Mkdir.mkdir(dirname);
    }
}
