
public class JameDemo 
{
	
	private JameUnit unit1, unit2;
	private int i;
	private boolean arrived1, arrived2;
	
	
	private static int pause = 1000; 
	
	public JameDemo()
	{
		unit1 = null;
		unit2 = null;
		arrived1 = false;
		arrived2 = false;
		i = 0;
	}

	public void execute()
	{		
		if( i == 0 ) //player 1
		{
			(new JameBuildCommand( Jame.currentPlayer, JameBuildingType.getType("Holdfast"), JameMap.getField(1,1) )).execute();
			i++;
			sleep();
			return;
		}
		if( i == 1 )
		{
			Jame.nextPlayer();
			i++;
			sleep();
			return;
		}
		if( i == 2 ) //player 2
		{
			(new JameBuildCommand( Jame.currentPlayer, JameBuildingType.getType("Holdfast"), JameMap.getField(Jame.mapMaxWidth, Jame.mapMaxHeight) )).execute();
			i++;
			sleep();
			return;
		}
		if( i == 3 )
		{
			Jame.nextPlayer();
			i++;
			sleep();
			return;
		}
		if( i == 4 ) //player 1
		{
			(new JamePlaceUnitCommand( Jame.currentPlayer, JameUnitType.getType("Knight"), JameMap.getField(1,2) )).execute();			
			unit1 = JameMap.getFieldUnit(JameMap.getField(1,2));
			i++;
			sleep();
			return;
		}
		if( i == 5 )
		{
			Jame.nextPlayer();
			i++;
			sleep();
			return;
		}
		if( i == 6 ) //player 2
		{
			(new JamePlaceUnitCommand( Jame.currentPlayer, JameUnitType.getType("Knight"), JameMap.getField(Jame.mapMaxWidth, Jame.mapMaxHeight - 1) )).execute();			
			
			unit2 = JameMap.getFieldUnit(JameMap.getField(Jame.mapMaxWidth, Jame.mapMaxHeight - 1));
			i++;
			sleep();
			return;
		}
		if( i == 7 && arrived1 && arrived2 )
		{
			i = 3;
			arrived1 = false;
			arrived2 = false;
			unit1 = null;
			unit2 = null;
			sleep();
			return;
		}
		if( i == 7 && Jame.currentPlayerPosition == 0 ) //player 1
		{
			int xGoal = 8;
			int yGoal = 8;
			if( unit1.field.xPos < xGoal && unit1.movement >= ((JameTerrainType)JameMap.getField(unit1.field.xPos + 1, unit1.field.yPos).type).movementPoints &&
				((JameTerrainType)JameMap.getField(unit1.field.xPos + 1, unit1.field.yPos).type).movementPoints <= ((JameTerrainType)JameMap.getField(unit1.field.xPos, unit1.field.yPos + 1).type).movementPoints )
			{
				int a = unit1.field.xPos;
				int b = unit1.field.yPos;
				(new JameMoveUnitCommand( Jame.currentPlayer, unit1, unit1.field, JameMap.getField(unit1.field.xPos + 1, unit1.field.yPos) )).execute();
				if( unit1.field.xPos == a && unit1.field.yPos == b )
					arrived1 = true;
				sleep();
				return;
			}
			else if( unit1.field.yPos < yGoal && unit1.movement >= ((JameTerrainType)JameMap.getField(unit1.field.xPos, unit1.field.yPos + 1).type).movementPoints )
			{
				int a = unit1.field.xPos;
				int b = unit1.field.yPos;
				(new JameMoveUnitCommand( Jame.currentPlayer, unit1, unit1.field, JameMap.getField(unit1.field.xPos, unit1.field.yPos + 1) )).execute();
				if( unit1.field.xPos == a && unit1.field.yPos == b )
					arrived1 = true;
				sleep();
				return;
			}
			else if( unit1.field.xPos == xGoal && unit1.field.yPos == yGoal )
			{
				arrived1 = true;
			}
			Jame.nextPlayer();
			sleep();
			return;
		}
		if( i == 7 && Jame.currentPlayerPosition == 1 ) //player 2
		{
			int xGoal = 8;
			int yGoal = 8;
			if( unit2.field.yPos > yGoal && unit2.movement >= ((JameTerrainType)JameMap.getField(unit2.field.xPos, unit2.field.yPos - 1).type).movementPoints &&
				((JameTerrainType)JameMap.getField(unit2.field.xPos, unit2.field.yPos - 1).type).movementPoints <= ((JameTerrainType)JameMap.getField(unit2.field.xPos-1, unit2.field.yPos).type).movementPoints)
			{
				int a = unit2.field.xPos;
				int b = unit2.field.yPos;
				(new JameMoveUnitCommand( Jame.currentPlayer, unit2, unit2.field, JameMap.getField(unit2.field.xPos, unit2.field.yPos - 1) )).execute();
				if( unit2.field.xPos == a && unit2.field.yPos == b )
					arrived2 = true;
				sleep();
				return;
			}
			else if( unit2.field.xPos > xGoal && unit2.movement >= ((JameTerrainType)JameMap.getField(unit2.field.xPos - 1, unit2.field.yPos).type).movementPoints )
			{
				int a = unit2.field.xPos;
				int b = unit2.field.yPos;
				(new JameMoveUnitCommand( Jame.currentPlayer, unit2, unit2.field, JameMap.getField(unit2.field.xPos - 1, unit2.field.yPos) )).execute();
				if( unit2.field.xPos == a && unit2.field.yPos == b )
					arrived2 = true;
				sleep();
				return;
			}
			else if( unit2.field.xPos == xGoal && unit2.field.yPos == yGoal )
			{
				arrived2 = true;
			}
			Jame.nextPlayer();
			sleep();
			return;
		}		
		/*else
		{
			i = 0;			
			Jame.gui.setDemoMode(false);
			Jame.demoMode = false;
		}	*/	
	}
	
	public void sleep()
	{
		javax.swing.SwingUtilities.invokeLater(new Runnable() 
		{
			public void run() 
		    {
				try{
				Thread.sleep(pause);
				Jame.demo.execute();
				//System.out.println("hihi" + System.currentTimeMillis() );
				}
				catch( Exception e)
				{
					e.printStackTrace();
				}
		    }
		 });
	}
}