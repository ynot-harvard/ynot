package filesystem.inode;

import filesystem.*;
import filesystem.buffercache.*;

public class InodeCache {

	public final InodePool pool;
	public final InodeList freelist;
	public final InodeHashQueues hashqueues;
	
	public InodeCache (int inodeCount) {
		pool = new InodePool(inodeCount);
		freelist = new InodeList();
		hashqueues = new InodeHashQueues(inodeCount / 10);		
                      
                for (int i = 0; i < pool.inodes.length; i++) {                              
                    freelist.add(pool.inodes[i].freelistNode);
                }   
	}
	
	public Inode iget (int inodeid) {
		while (true) {
			Inode inode = hashqueues.get(inodeid);
			
			if (inode != null) {
				if (inode.isLocked) {
					//call sleep until inode is unlocked
                                        inode.isLocked = false;
					return inode;
				}
                                else {
                                    freelist.remove(inode.freelistNode);
				}
				
				inode.refCount++;
				return inode;
			}
			
			if (freelist.isEmpty())
				return null;
			
			inode = freelist.pop().inode;
			hashqueues.remove(inode.id);
			inode.clear();
			iread (inodeid, inode);
			inode.id = inodeid;
			inode.refCount++;
			hashqueues.add(inode.hashqueuesNode);
			return inode;
		}
		
	}
	
	//loads the disk inode with inodeid into the in-core inode structure
	//invokes the FileSystem.bufferCache: requires INODES_PER_BLOCK and INODELIST_START
	public void iread (int inodeid, Inode inode) {
            int inodesperblock = FileSystem.BLOCK_SIZE / FileSystem.superBlock.inodeSize;
            int blkid = inodeid / inodesperblock + FileSystem.superBlock.inodeListStart;
            Buffer buffer = FileSystem.bufferCache.bread(blkid);
            int offset = (inodeid % inodesperblock) * FileSystem.superBlock.inodeSize;
                    
            inode.clear();
            inode.id = inodeid;
            inode.unserialize (buffer.data, offset);       
            FileSystem.bufferCache.brelse(buffer);
        }
	
	public void iwrite (Inode inode) {
            int inodeid = inode.id;
            int inodesperblock = FileSystem.BLOCK_SIZE / FileSystem.superBlock.inodeSize;
            int blkid = inodeid / inodesperblock + FileSystem.superBlock.inodeListStart;
            Buffer buffer = FileSystem.bufferCache.bread(blkid);
            int offset = (inodeid % inodesperblock) * FileSystem.superBlock.inodeSize;
                    
            inode.serialize (buffer.data, offset);
            FileSystem.bufferCache.bwrite(buffer);
            FileSystem.bufferCache.brelse(buffer);
	}
	
	public void iput (Inode inode) {
		//if-construct needs to be atomic
		if (inode.isLocked) {
			inode.isLocked = true;
		}
		
		inode.refCount--;
		if (inode.refCount == 0) {
			if (inode.linkCount == 0) {
                                BlockIterator bi = inode.blockTable.iterator();
                                while (bi.hasNext()) {
                                    int blkid = bi.next();
                                    FileSystem.subSystem.free(blkid);                                       
                                }
                                                        
				inode.fileType = 0; 
                                FileSystem.subSystem.ifree(inode.id);
			}
			
			
			if (inode.hasBeenModified)
				iwrite (inode);
			 			
			freelist.add(inode.freelistNode);
		}
                
                inode.isLocked = false;
	}        
}
