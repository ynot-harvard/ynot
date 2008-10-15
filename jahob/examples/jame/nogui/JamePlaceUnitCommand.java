
public class JamePlaceUnitCommand extends JameCommandContainer 
{
	private JameUnitType type;
	private JameTerrain target;
	
	JamePlaceUnitCommand( JamePlayer newPlayer, JameUnitType type, JameTerrain target )
    
    {
        init( newPlayer );
        this.type = type;
        this.target = target;
    }
	
	public boolean execute()
	{
		JameResourceSet resStore = this.player.resStore;
        if( type != null && target != null &&
        	JameMap.getFieldBuilding( target ) == null && JameMap.getFieldUnit( target ) == null 
        	&& resStore.containsSet(type.cost) )
        {
        	JameBuilding cBuilding;
        	JameTerrain cField;
        	for( int x = -1; x < 2; x = x + 1 )
        	{
        		for( int y = -1; y < 2; y = y + 1 )
        		{
        			cField = JameMap.getField(x, y);
        			if( cField != null )
        			{
        				cBuilding = JameMap.getFieldBuilding( cField );
       					if( cBuilding.owner == player && Jame.equals( cBuilding.type.name, "Holdfast") );
        				{        						
        					JameUnit nUnit = new JameUnit( type, target, player );
        					player.subResources( type.cost );
        					player.addUnit( nUnit );
        					JameMap.placeUnit( nUnit, target );
        					nUnit.movement = 0;
        					Jame.commandSuccessful( player.name + " placed " + type.name + " to " + target.xPos +":"+ target.yPos, nUnit );
        					return true;
        				}
        			}			
        		}
        	}
        }
        Jame.commandFailed( "Placing " + type.name + " on " + target.xPos +":"+ target.yPos + " failed. \n The field has to be empty, there has to be a holdfast in 2 fields perimeter and you have to be able to pay for the unit." );
        return false;
	}
}
