public class Big extends Object {
    private Small s;

    //: inv "s..Object.owner = token.Big";

    public void test()
    {
        //: assume "s : alloc.Small";
        //: assume "s ~= null";
        s.sx = 7;
        // The next two do nothing, just test the release and acquire mechanism:
        //: release(s)
        //: incorporate(s)
    }
}
