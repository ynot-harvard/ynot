/*
 * Created on Feb 16, 2005
 *
 */

/**
 * @author nguyenh2
 *  
 */

import java.nio.charset.*;
import java.nio.*;
import java.util.Date;
import java.util.Set;

class URI {
    String filename;

    URI(String filename) {
        this.filename = filename;
    }
}

class Request {
    Connection conn;

    URI uri;

    Request(Connection conn, URI uri) {
        this.conn = conn;
        this.uri = uri;
    }
}

class Response {
    Connection conn;

    ByteBuffer contents;

    Response(Connection conn, ByteBuffer contents) {
        this.conn = conn;
        this.contents = contents;
    }
    
    static Response reject(SocketChannelWrapper channel) {
        CharBuffer buffer = CharBuffer.allocate(1024);
        String body = "<html><head><title>Hello, World</title></head><body>Request queue full</body></html>";
        buffer.put("HTTP/1.0 200 OK\nContent-Type: text/html\nContent-Length: " + body.length() + "\n\n");
        buffer.put(body);

        //Charset charset = Charset.forName("ISO-8859-1");
        //CharsetEncoderWrapper encoder = new CharsetEncoderWrapper(charset.newEncoder());
        //result = encoder.encode(buffer);
        
        ByteBuffer result = ByteBuffer.allocate(buffer.length());
        for (int i = 0; i < buffer.length(); i++) {
            result.put(i, (byte)buffer.get(i));
        }
        
        return new Response(new Connection(channel, Connection.CLIENT), result);
    }
}

class Connection {
    public static final int CLIENT = 1;

    public static final int WORKER = 2;

    SocketChannelWrapper channel; //

    int type; // is it connection to client or connection to a worker or something else

    Connection(SocketChannelWrapper channel, int type) {
        this.channel = channel;
        this.type = type;
    }
}

class Worker {
    static final int AVAIL = 1; // can serve next request
    static final int BUSY = 2; // serving some request, can't serve anything else
    static final int RESULT = 3; // result contains result, can't serve until result is read off
    private int status;
    private ByteBuffer result;
    private Connection conn;
    
    Worker() {
        this.status = AVAIL;
        result = null;
    }
    
    public boolean isAvail() {
        return status == AVAIL;
    }
    
    public boolean isBusy() {
        return status == BUSY;
    }
    
    public boolean hasResult() {
        if (status == RESULT) {
            return true;
        }
        else {
	        int rn = (int) (Math.random() * 3);
	        if (rn <= 1 || status == AVAIL) {
	            return false;
	        }
	        else {
	            status = RESULT;
	            return true;
	        }
        }
    }
    
    /*
     * requires status == RESULT
     */
    public Response getResult() {
        if (status == RESULT) {
            status = AVAIL;
            return new Response(this.conn, this.result);
        }
        else {
            return null;
        }
    }
    
    /*
     * requires status == AVAIL
     * if status is not AVAIL, req is discarded -- we don't want this to happen
     */
    public void serve(Request req) {
        if (status == AVAIL) {
            status = BUSY;
            URI uri = req.uri;
            
            this.conn = req.conn;
            
            //construct artificial response
            CharBuffer buffer = CharBuffer.allocate(1024);
            String body = "<html><head><title>Hello, World</title></head><body><h1>Hello, World. this is my test HTTP server. Generated at " + new Date() + "</h1></body></html>";
            buffer.put("HTTP/1.0 200 OK\nContent-Type: text/html\nContent-Length: " + body.length() + "\n\n");
            buffer.put(body);

            //Charset charset = Charset.forName("ISO-8859-1");
            //CharsetEncoderWrapper encoder = new CharsetEncoderWrapper(charset.newEncoder());
            //result = encoder.encode(buffer);
            
            result = ByteBuffer.allocate(buffer.length());
            for (int i = 0; i < buffer.length(); i++) {
                result.put(i, (byte)buffer.get(i));
            }
            
            // status = RESULT;
        }
    }
}


/*
 * @author nguyenh2 
 * 
 * HTTPServer receives requests from clients into a buffer. It
 * then forwards the requests (taken from buffer) to an available worker (taken
 * from a pool of workers). Responses from workers are buffered and then
 * forwarded to clients made the corresponding requests.
 * 
 * Clients talk to HTTPServer via non-blocking IO. Question: How do workers talk
 * to HTTPServer? For now: just methods that make a random decision whether they
 * serve the request immediately or wait.
 */

class HTTPServer {
    private ServerSocketChannelWrapper server;
    private SelectorWrapper selector;
    private int port = 8080;

    /*
     * This buffer behaves like a queue. It contains requests received from
     * clients. These requests are waiting to be sent to some worker to be
     * served. This buffer behaves like a queue.
     */
    private List reqBuf;
    private int MAXREQBUF = 100;

    /*
     * Responses received from workers. To be sent to corresponding clients
     */
    private List resBuf;
    private int MAXRESBUF = 200; //responses are in general bigger than requests, so the queue might be longer ...
    
    /*
     * Workers pool
     */
    private Worker[] workers;
    private int nworkers;
    private int MAXWORKER = 100;

    static HTTPServer init(int port, int nworkers) {
        HTTPServer http = new HTTPServer(); 
        http.port = port;
        http.nworkers = nworkers;
        http.reqBuf = new List();
        http.resBuf = new List();
        
        return http;
    }

    void run() {
        
        workers = new Worker[nworkers];
        for (int i = 0; i < nworkers; i++) {
            workers[i] = new Worker();
        }
        
        server = ServerSocketChannelWrapperImpl.open();
        server.configureBlocking(false);
        server.socket().bind(new java.net.InetSocketAddress(this.port));
        selector = SelectorWrapperImpl.open();
        SelectionKeyWrapper acceptkey = server.register(selector, SelectionKeyWrapper.OP_ACCEPT);
        //sk.attach(new Acceptor());
        int selected = 0;
        while ((selected = selector.select()) > 0) {
            // talk to clients
            IterSet readykeys = selector.selectedKeys();
            readykeys.initIter();
            while (readykeys.hasNext()) {
                SelectionKeyWrapper sk = (SelectionKeyWrapper) readykeys.next();

                if (sk.isAcceptable()) {
                    SocketChannelWrapper channel = server.accept();
                    channel.configureBlocking(false);
                    channel.register(selector, SelectionKeyWrapper.OP_READ); // waiting for data from client
                }

                if (sk.isReadable()) {
                    SocketChannelWrapper channel = new SocketChannelWrapperImpl((java.nio.channels.SocketChannel) sk.channel());
                    readClient(channel);
                    channel.register(selector, SelectionKeyWrapper.OP_WRITE);
                }

                if (sk.isWritable()) {
                    SocketChannelWrapper channel = new SocketChannelWrapperImpl((java.nio.channels.SocketChannel) sk.channel());
                    writeClient(channel);
                    //channel.register(selector, 0);
                }
            }

            // talk to servers
            
            for (int i = 0; i < nworkers; i++) {
                Worker worker = workers[i];
                // see if there are any available workers to send requests to
                if (worker.isAvail()) {
                    if (!reqBuf.isEmpty()) {
                        Request req = (Request)reqBuf.removeLast();
                        worker.serve(req);
                    }
                }
                
                // see if there are any jobs done to move them to resBuf
                if (worker.hasResult() && resBuf.size() < MAXRESBUF) {
                    Response res= worker.getResult();
                    resBuf.add(res);
                }
            }
        }
    }

    boolean readClient(SocketChannelWrapper channel) {
        //we expect each HTTP request to come in one package
        ByteBuffer buffer = ByteBuffer.allocate(2048);
        channel.read(buffer);

        //convert to characters
        buffer.flip();
        Charset charset = Charset.forName("ISO-8859-1");
        CharsetDecoderWrapper decoder = new CharsetDecoderWrapperImpl(charset.newDecoder());
        CharBuffer charBuffer = decoder.decode(buffer);

        if (reqBuf.size() < MAXREQBUF) { 
            // put the request to queue
            Request req = new Request(new Connection(channel, Connection.CLIENT), new URI(charBuffer.toString()));
            reqBuf.add(req);
        }
        else {
            if (resBuf.size() < MAXRESBUF) {
                resBuf.add(Response.reject(channel));
            }
            else {
                channel.socket().close();
            }
        }

        return true;
    }

    boolean writeClient(SocketChannelWrapper channel) {
        Response res = null;
        boolean flag = true;
        resBuf.initIter();
        while (flag && resBuf.hasNext()) {
            Response tmp = (Response) resBuf.next();
            if (tmp.conn.channel.equals(channel)) {
                res = tmp;
                flag = false;
            }
        }

        if (res != null) {
            // there is a response for this channel, send it
            channel.write(res.contents);
            resBuf.remove(res); //request sent, remove it
        }
        return true;
    }
}

public class HTTPD {
    public static void main(String[] args) {
        int port = 8080;
        int nworkers = 3;
        
        if (args.length > 0) {
            port = Integer.parseInt(args[0]);
            if (args.length > 1) {
                nworkers = Integer.parseInt(args[1]);
            }
        }
        HTTPServer server = HTTPServer.init(port, nworkers);
        server.run();
    }
}