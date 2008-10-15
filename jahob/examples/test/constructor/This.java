public class This
{
	TestObject thisSet;
	//: inv "ALL x . x : thisSet..TestObject.testSet --> x : This & x ~= null"
	
	public void init()
	/*:
	 modifies "TestObject.testSet"
	 ensures "this : thisSet..TestObject.testSet"	 
	 */
	{
            // assume "this : This";
		test( this );
	}
	
	public void test( This element )
	/*:
	 requires "element ~= null"
	 modifies "TestObject.testSet"
	 ensures "thisSet..TestObject.testSet = old (thisSet..TestObject.testSet) Un {element}"
	 */
	{	
	}
}
