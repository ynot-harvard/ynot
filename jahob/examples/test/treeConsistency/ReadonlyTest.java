public class ReadonlyTest
{
    public void test()
    {
    	Readonly blub = new Readonly();
    	blub.roField = 10;
    	while( true )
    		Readonly.roVariable = 2;        
    }
}
