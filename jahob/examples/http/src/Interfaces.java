import java.net.InetSocketAddress;
import java.nio.ByteBuffer;
import java.nio.CharBuffer;
import java.nio.channels.SelectableChannel;
import java.nio.channels.SelectionKey;
import java.util.Set;

interface SocketChannelWrapper {
    public abstract void configureBlocking(boolean blocking);

    public abstract SelectionKeyWrapper register(SelectorWrapper selector, int ops);

    public abstract int read(ByteBuffer dst);

    public abstract int write(ByteBuffer dst);

    public abstract SocketWrapper socket();

    public abstract boolean equals(Object obj);    
}

interface SocketWrapper {
    public abstract void close();
}

interface ServerSocketWrapper {
    public abstract void bind(InetSocketAddress isa);

    public abstract void close();
}

interface CharsetEncoderWrapper {
    public abstract ByteBuffer encode(CharBuffer in);
}

interface CharsetDecoderWrapper {
    public abstract CharBuffer decode(ByteBuffer in);
}

interface SelectionKeyWrapper {
    public static int OP_ACCEPT = SelectionKey.OP_ACCEPT;

    public static int OP_READ = SelectionKey.OP_READ;

    public static int OP_WRITE = SelectionKey.OP_WRITE;

    public abstract SelectableChannel channel();

    public abstract boolean isAcceptable();

    public abstract boolean isReadable();

    public abstract boolean isWritable();
}

interface SelectorWrapper {
    public abstract int select();

    public abstract IterSet selectedKeys();
}

interface ServerSocketChannelWrapper {
    public abstract void configureBlocking(boolean blocking);

    public abstract ServerSocketWrapper socket();

    public abstract SelectionKeyWrapper register(SelectorWrapper selector, int ops);

    public abstract SocketChannelWrapper accept(); 
}