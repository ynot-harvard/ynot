/*
 * Created on Mar 10, 2005
 */

/**
 * @author aragos
 */
public class JameCommandContainer
{
    public /*:readonly*/ JamePlayer player;
    
    public void init( JamePlayer newPlayer )
    /*:
     modifies player
     ensures "player = newPlayer"
     */
    {
        this.player = newPlayer;
        //Jame.pendingCommands.add(this);
    }
    
    public boolean execute(){return true;}
}
