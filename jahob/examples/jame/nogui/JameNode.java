/*
 * Created on Mar 8, 2005
 * CHECKED 2
 */

/**
 * Double linked list node implementation for Jame.
 * 
 * @author aragos
 */
public class JameNode
{	
    public /*:readonly*/ JameNode prev;
    public /*:readonly*/ JameNode next;
    public /*:readonly*/ Object content;
    
    public void init( Object newContent )
    /*:
     modifies content
     ensures "content = newContent"
     */
    {
        this.content = newContent;
    }
    
    public void initEx(Object newContent, JameNode newNext, JameNode newPrev )
    /*:
     modifies content, prev, next
     ensures "
     	content = newContent &
     	prev = newPrev &
     	next = newNext "
     */
    {
        this.content = newContent;
        this.next = newNext;
        this.prev = newPrev;
    }
    
    public void setNext( JameNode newNext )
    /*:
     modifies next
     ensures "next = newNext"
     */
    {
        this.next = newNext;
    }
    
    public void setPrev( JameNode newPrev )
    /*:
     modifies prev
     ensures "prev = newPrev"
     */
    {
        this.prev = newPrev;
    }       
}
