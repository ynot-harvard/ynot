class Test {
    int x; //: inv "0 <= x"

    int y; //: inv "0 <= y"

    public void foo(int x1) {
	if (0 <= x1) {
	    x = x1;
	} else {
	    x = 0;
	}
    }

    public void inc() {
	x = x + 1;
    }
}
