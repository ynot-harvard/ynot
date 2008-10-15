/*
 * Created on Mar 10, 2005
 */

/**
 * @author aragos
 */
public class JameCreateUnitCommand extends JameCommandContainer
{
    private String unitType;
    private int xPos;
    private int yPos;
    
    JameCreateUnitCommand( JamePlayer newPlayer, String newType, int x, int y )
    {        
        init( newPlayer );
        this.unitType = newType;
        this.xPos = x;
        this.yPos = y;
    }
    
    public boolean execute()
    {
        JameTerrain field = JameMap.getField( xPos, yPos );
        JameUnitType type = JameUnitType.getType(unitType);
        if( field != null && type != null &&
                JameMap.getFieldBuilding( field ) == null && JameMap.getFieldUnit( field ) == null )
        {
            JameUnit unit = new JameUnit( type, field, this.player );
            JameMap.placeUnit( unit, field );
            this.player.addUnit( unit );
            return true;
        }
        return false;
    }
}
