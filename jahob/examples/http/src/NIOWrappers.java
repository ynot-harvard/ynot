/*
 * Created on Feb 17, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */

/**
 * @author nguyenh2
 * 
 * TODO To change the template for this generated type comment go to Window -
 * Preferences - Java - Code Style - Code Templates
 */

import java.io.*;
import java.nio.*;
import java.nio.channels.*;
import java.nio.charset.*;
import java.net.*;
import java.util.*;

class SocketChannelWrapperImpl implements SocketChannelWrapper {
    SocketChannel channel;

    SocketChannelWrapperImpl(SocketChannel channel) {
        this.channel = channel;
    }

    public void configureBlocking(boolean blocking) {
        try {
            channel.configureBlocking(blocking);
        }
        catch (IOException e) {
            System.out.println(e.getMessage());
            e.printStackTrace();
        }
    }

    public SelectionKeyWrapper register(SelectorWrapper selector, int ops) {
        try {
            return new SelectionKeyWrapperImpl(channel.register(((SelectorWrapperImpl)selector).selector, ops));
        }
        catch (IOException e) {
            System.out.println(e.getMessage());
            e.printStackTrace();
            return null;
        }
    }

    public int read(ByteBuffer dst) {
        try {
            return channel.read(dst);
        }
        catch (Exception e) {
            System.out.println(e.getMessage());
            e.printStackTrace();
            return -1;
        }
    }

    public int write(ByteBuffer dst) {
        try {
            return channel.write(dst);
        }
        catch (Exception e) {
            System.out.println(e.getMessage());
            e.printStackTrace();
            return -1;
        }
    }
    
    public SocketWrapper socket() {
        return new SocketWrapperImpl(channel.socket());
    }
    
    public boolean equals(Object obj) {
        SocketChannelWrapper sc = (SocketChannelWrapper)obj;
        return this.channel == ((SocketChannelWrapperImpl)sc).channel;
    }
}

class ServerSocketChannelWrapperImpl implements ServerSocketChannelWrapper {
    ServerSocketChannel channel;

    ServerSocketChannelWrapperImpl(ServerSocketChannel channel) {
        this.channel = channel;
    }

    public static ServerSocketChannelWrapper open () {
        try {
            return new ServerSocketChannelWrapperImpl(ServerSocketChannel.open());
        }
        catch (IOException e) {
            System.out.println(e.getMessage());
            e.printStackTrace();
            return null;
        }
    }

    public void configureBlocking(boolean blocking) {
        try {
            channel.configureBlocking(blocking);
        }
        catch (IOException e) {
            System.out.println(e.getMessage());
            e.printStackTrace();
        }
    }

    public ServerSocketWrapper socket() {
        return new ServerSocketWrapperImpl(channel.socket());
    }

    public SelectionKeyWrapper register(SelectorWrapper selector, int ops) {
        try {
            return new SelectionKeyWrapperImpl(channel.register(((SelectorWrapperImpl)selector).selector,
                    ops));
        }
        catch (IOException e) {
            System.out.println(e.getMessage());
            e.printStackTrace();
            return null;
        }
    }

    public SocketChannelWrapper accept() {
        try {
            return new SocketChannelWrapperImpl(channel.accept());
        }
        catch (IOException e) {
            System.out.println(e.getMessage());
            e.printStackTrace();
            return null;
        }
    }
}

class SelectorWrapperImpl implements SelectorWrapper {
    Selector selector;

    SelectorWrapperImpl(Selector selector) {
        this.selector = selector;
    }

    public static SelectorWrapper open() {
        try {
            return new SelectorWrapperImpl(Selector.open());
        }
        catch (IOException e) {
            System.out.println(e.getMessage());
            e.printStackTrace();
            return null;
        }
    }

    public int select() {
        try {
            return selector.select();
        }
        catch (IOException e) {
            System.out.println(e.getMessage());
            e.printStackTrace();
            return 0;
        }
    }

    public IterSet selectedKeys() {
        try {
            Set keys = selector.selectedKeys();
            Iterator it = keys.iterator();
            IterSet wrappedkeys = new List();
            while (it.hasNext()) {
                SelectionKey key = (SelectionKey) it.next();
                it.remove();
                wrappedkeys.add(new SelectionKeyWrapperImpl(key));
            }
            return wrappedkeys;
        }
        catch (Exception e) {
            System.out.println(e.getMessage());
            e.printStackTrace();
            return null;
        }
    }
}

class SelectionKeyWrapperImpl implements SelectionKeyWrapper {
    private SelectionKey selectionKey;

    SelectionKeyWrapperImpl (SelectionKey selectionKey) {
        this.selectionKey = selectionKey;
    }

    public SelectableChannel channel() {
        return selectionKey.channel();
    }

    public boolean isAcceptable() {
        try {
            return selectionKey.isAcceptable();
        }
        catch (Exception e) {
            System.out.println(e.getMessage());
            e.printStackTrace();
            return false;
        }
    }

    public boolean isReadable() {
        try {
            return selectionKey.isReadable();
        }
        catch (Exception e) {
            System.out.println(e.getMessage());
            e.printStackTrace();
            return false;
        }
    }

    public boolean isWritable() {
        try {
            return selectionKey.isWritable();
        }
        catch (Exception e) {
            System.out.println(e.getMessage());
            e.printStackTrace();
            return false;
        }
    }

}

class CharsetDecoderWrapperImpl implements CharsetDecoderWrapper {
    CharsetDecoder decoder;

    CharsetDecoderWrapperImpl(CharsetDecoder decoder) {
        this.decoder = decoder;
    }

    public final CharBuffer decode(ByteBuffer in) {
        try {
            return decoder.decode(in);
        }
        catch (Exception e) {
            System.out.println(e.getMessage());
            e.printStackTrace();
            return null;
        }
    }
}

class CharsetEncoderWrapperImpl implements CharsetEncoderWrapper {
    CharsetEncoder encoder;

    CharsetEncoderWrapperImpl(CharsetEncoder encoder) {
        this.encoder = encoder;
    }

    public final ByteBuffer encode(CharBuffer in) {
        try {
            return encoder.encode(in);
        }
        catch (Exception e) {
            System.out.println(e.getMessage());
            e.printStackTrace();
            return null;
        }
    }
}

class ServerSocketWrapperImpl implements ServerSocketWrapper {
    ServerSocket socket;

    ServerSocketWrapperImpl(ServerSocket socket) {
        this.socket = socket;
    }

    public void bind(InetSocketAddress isa) {
        try {
            socket.bind(isa);
        }
        catch (Exception e) {
            System.out.println(e.getMessage());
            e.printStackTrace();
        }
    }
    
    public void close() {
        try {
            socket.close();
        }
        catch (Exception e) {
            System.out.println(e.getMessage());
            e.printStackTrace();
        }
    }
}

class SocketWrapperImpl implements SocketWrapper {
    Socket socket;

    SocketWrapperImpl(Socket socket) {
        this.socket = socket;
    }
    
    public void close() {
        try {
            socket.close();
        }
        catch (Exception e) {
            System.out.println(e.getMessage());
            e.printStackTrace();
        }
    }
}