/* 
   The JI class (JameInvariants) contains global invariants for Jame.
   They are written as public boolean variables, so they do not impose
   constraints by themself, only define shorthands.
 */
public class JI {
 /*:
   public static specvar fieldsOwned :: bool;
   public vardefs "fieldsOwned == pointsto 
     (JameMap.fields..JameCollection.collection)
     JameMapContainer.owner
     (JamePlayer.player..JameCollection.collection)";

   public static specvar unitsOwned :: bool;
   public vardefs "unitsOwned == pointsto 
     (JameMap.units..JameCollection.collection)
     JameMapContainer.owner
     (JamePlayer.player..JameCollection.collection)";

   public static specvar buildingsOwned :: bool;
   public vardefs "buildingsOwned == pointsto 
     (JameMap.buildings..JameCollection.collection)
     JameMapContainer.owner
     (JamePlayer.player..JameCollection.collection)";

   public static specvar allocPlayer :: bool;
   public vardefs "allocPlayer == 
     (Object.alloc Int JamePlayer <= JamePlayer.player..JameCollection.collection)";

   public static specvar buildingInverse :: bool;
   public vardefs "buildingInverse ==
     (ALL b . b : JameMap.buildings..JameCollection.collection --> 
             b : b..JameMapContainer.owner..JamePlayer.buildings..JameCollection.collection)";
  */
}
