class Test1 {
    private static void foo() 
    /*:
        requires "True"
        modifies arrayState
        ensures "True"
    */
    {	
	Object[] bar1 = new Object[30];

        bar1[7] = null;
        //: noteThat "bar1.[7] = null";
	//
    }
}
