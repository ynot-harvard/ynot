/*
 * Created on Mar 10, 2005
 */

/**
 * @author aragos
 */
public class JameMoveUnitCommand extends JameCommandContainer
{
    public JameUnit unit;
    //public JameTerrain start;
    public JameTerrain target;
    
    JameMoveUnitCommand( JamePlayer newPlayer, JameUnit unit, JameTerrain start, JameTerrain target )
    
    {
        init( newPlayer );
        this.unit = unit;
        this.target = target;
        //this.start = start;
    }
    
    public boolean execute()
    /*:
     requires "target ~= null & this..JameMoveUnitCommand.unit ~= null & this..JameCommandContainer.player ~= null & this..JameCommandContainer.player..JamePlayer.units ~= null & JameMap.initialised 
     			& target..JameMapContainer.type ~= null & this..JameMoveUnitCommand.unit..JameMapContainer.field ~= null"
     			
     modifies "JameUnit.movement", "JameMap.units..JameCollection.collection", "JameMap.units..JameCollection.free", "JameMap.units..JameCollection.size", "JameMap.buildings..JameCollection.free",
     			"this..JameMoveUnitCommand.unit..JameMapContainer.owner..JamePlayer.units..JameCollection.collection", "this..JameMoveUnitCommand.unit..JameMapContainer.owner..JamePlayer.units..JameCollection.free",
     			"this..JameMoveUnitCommand.unit..JameMapContainer.owner..JamePlayer.units..JameCollection.size", "JameCollection.collection", "JameCollection.free", "JameCollection.size"
     ensures "     	
     	comment ''fight''
     	( 
     		( ( (old this..JameMoveUnitCommand.unit..JameMapContainer.field) ~= target ) &
     		( EX a . a : JameMap.units..JameCollection.collection & a..JameMapContainer.field = target & 
     			a..JameMapContainer.owner ~= this..JameMoveUnitCommand.unit..JameMapContainer.owner ) ) 
     		--> 
     		JameMap.units..JameCollection.collection <= (old JameMap.units..JameCollection.collection) &
     		( ALL b . b : ((old JameMap.units..JameCollection.collection) - JameMap.units..JameCollection.collection) 
     			--> (b..JameMapContainer.field = target | b = this..JameMoveUnitCommand.unit) )     		
     	)
     	"
     */
    /*
     comment ''move if field is free and unit has movement''
     	(   
     		( this..JameMoveUnitCommand.unit..JameMapContainer.field = target ) &
     		( (old this..JameMoveUnitCommand.unit..JameUnit.movement) >= target..JameTerrain.movementPoints ) &
     		comment ''add distance constraint''
     		( ALL u . u : (old JameMap.units..JameCollection.collection) --> u..JameMapContainer.field ~= target ) &
     		( (old this..JameMoveUnitCommand.unit..JameMapContainer.field) ~= target ) 
     	)
     */
    {  
    	//: assume "target..JameMapContainer.type : JameTerrainType & target..JameMapContainer.type : alloc.JameTerrainType & this..JameMoveUnitCommand.unit : JameMap.units..JameCollection.collection"
        if( target != null && unit != null && target != unit.field && this.player.units.contains(unit)  &&
        	JameMap.getFieldBuilding( target ) == null && ((JameTerrainType)target.type).movementPoints <= unit.movement && 
        	Math.abs(target.xPos - unit.field.xPos) < 2 && Math.abs(unit.field.yPos - target.yPos) < 2)
        {
        	JameUnit fieldUnit = JameMap.getFieldUnit(target);
        	// everything ok, move unit
        	if( fieldUnit == null )
        	{
        		JameMap.moveUnit( unit, target );
        		unit.movement = unit.movement - ((JameTerrainType)target.type).movementPoints;
        	}
        	// units on field, if ...
        	else
        	{
       			// ... own then don't move
       			if( fieldUnit.owner == this.player )
       			{
        			Jame.commandFailed( "Moving " + unit.type.name + " to " + target.xPos +":"+ target.yPos + " failed. \n The field is blocked by your own unit." );
        			return false;
        		}
        		// ... enemy then fight
            	String casualities = Jame.fight( this.unit, fieldUnit );
            	Jame.commandSuccessful( "A fight took place on " + target.xPos + ":" + target.yPos + ". The following units died: " + casualities, null );
                return true;
        	}
        	Jame.commandSuccessful( this.player.name + " moved " + unit.type.name + " to " + target.xPos +":"+ target.yPos, null );
            return true;
        }
        if( target != null && unit != null )
        	Jame.commandFailed( "Moving " + unit.type.name + " to " + target.xPos +":"+ target.yPos + " failed. \n The field has to be empty of buildings and the unit has to have enough movement points to advance." );
        return false;
    }
    
}
