class test {
    //: public specvar f1 :: int
    //: private vardefs "f1 == ff1"
    
    private int ff1;
    private int ff2;

    public void empty()
	/*:
	  requires "True"
	  ensures "True"
	 */
    {
    }
    
    public void inc(test p)
	/*:
	  requires "True"
	  modifies f1
	  ensures "this..test.f1 = 1"
	*/
	// ensures "this..test.ff1 = old(p..test.ff1)"
	
    {
	this.ff1 = 1;
	//this.ff2 = this.ff2 + p.ff2;
    }
}
