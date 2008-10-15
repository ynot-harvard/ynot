/*
 * Created on Mar 8, 2005
 * CHECKED 2
 */

/**
 * Research in Jame.
 * 
 * @author aragos
 */
public class JameResearch
{
    public /*:readonly*/ String name;			// researchs name
    public /*:readonly*/ JameResourceSet cost;	// researchs cost
    public /*:readonly*/ JameCollection cond;	/*: public specvar conditionSet :: objset */	// researchs conditions
    
    public JameResearch( String newName, JameResourceSet newCost, JameCollection conditions )
    /*:
     modifies name, cost, conditionSet
     ensures "
     	name = newName &
     	cost = newCost &
     	conditionSet = conditions"
     */
    {
        this.name = newName;
        this.cost = newCost;
        this.cond = conditions;
    }    
}
