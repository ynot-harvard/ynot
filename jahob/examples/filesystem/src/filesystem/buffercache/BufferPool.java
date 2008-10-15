package filesystem.buffercache;

import filesystem.*;

class BufferPool {
    //: specfield contents : "object set"
    //: vardefs "contents == {b. (b:Buffer) & (EX i. b=buffers.[i])}"
            
    Buffer[] buffers;
    
     //NOTE: ask vk how do we reference the relation implied by the blkid field in Buffer
     
     //need to say contents are distinct instantiations of Buffer
    //card contents = poolSize & (contents `` glbbuffers) = {0}

    BufferPool(int poolSize)
    /*:
      requires "0 <= poolSize"
      modifies contents
      ensures "card contents = poolSize & (ALL b. b:contents & b..blkid = 0)"
    */
    {
        buffers = new Buffer[poolSize];
	int i = 0;
	while (i < buffers.length) {
            Buffer buf = new Buffer(1024);
            buffers[i] = buf;
	    i = i + 1;
        }
    }
}