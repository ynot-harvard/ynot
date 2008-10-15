/*
 * Created on Mar 10, 2005
 */

/**
 * @author aragos
 */
public class JameBuildCommand extends JameCommandContainer
{
    private JameBuildingType type;
    private JameTerrain target;
    
    JameBuildCommand( JamePlayer newPlayer, JameBuildingType type, JameTerrain target )
    {
        init( newPlayer );        
        this.type = type;
        this.target = target;
    }

    public void test()
    /*:
      requires "JI.allocPlayer"
      modifies "JamePlayer.player"
      ensures "JI.allocPlayer"
     */
    {
    }

    public boolean execute()
    /*:
     requires "JI.buildingsOwned &
               JI.buildingInverse &
               JI.allocPlayer &
               JameMap.initialised & 
               this..JameCommandContainer.player..JamePlayer.resStore ~= null & 
               this..JameCommandContainer.player ~= null & 
               this..JameCommandContainer.player..JamePlayer.buildings ~= null & 
               this..JameCommandContainer.player..JamePlayer.resStore..JameResourceSet.resources ~= null"
     modifies 	"JameMap.buildings..JameCollection.free", 
                "JameMap.units..JameCollection.free", 
                "JameMap.buildings..JameCollection.collection", 
                "JameMap.buildings..JameCollection.size",
                "this..JameCommandContainer.player..JamePlayer.buildings..JameCollection.collection", 
                "this..JameCommandContainer.player..JamePlayer.buildings..JameCollection.size",
                "this..JameCommandContainer.player..JamePlayer.buildings..JameCollection.free",
                "JameMapContainer.owner", "JameMapContainer.field", "JameMapContainer.type"
     ensures  	"JI.buildingsOwned &
                 JI.buildingInverse &
                 JI.allocPlayer";
     */
    {
    	//: assume "this..JameBuildCommand.target ~= null & this..JameBuildCommand.type ~= null & this..JameBuildCommand.type..JameBuildingType.cost ~= null" 
        if( target != null && type != null &&
                JameMap.getFieldBuilding( target ) == null && JameMap.getFieldUnit( target ) == null &&
                this.player.resStore.containsSet(type.cost) )
        {
        	//: assume "this..JameCommandContainer.player : alloc.JamePlayer"
            JameBuilding building = new JameBuilding( type, target, null );
            JameMap.placeBuilding( building, target );
            this.player.addBuilding( building );
            this.player.subResources(type.cost);
            Jame.commandSuccessful( this.player.name + " builds " + type.name + " on " + target.xPos +":"+ target.yPos, building );
            // assert "JameMap.buildings..JameCollection.collection = old (JameMap.buildings..JameCollection.collection)";
            // assume "False";
            return true;
        }
        Jame.commandFailed( "Building " + type.name + " on " + target.xPos +":"+ target.yPos + " failed. \n The field has to be empty and you have to be able to pay for the building." );
        return false;
    }
}
