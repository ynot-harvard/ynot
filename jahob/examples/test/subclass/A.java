class A extends B {
    public static void test() 
    //: requires "True" modifies "B.bf" ensures "True";
    {
	A a = new A();
	a.bf = null;
	a.init();
    }
}