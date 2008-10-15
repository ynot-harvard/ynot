class Test {
    public static void main(String[] args) 
    /*:
      modifies "SetIterBoundedArray.size", "SetIterBoundedArray.content", "SetIterBoundedArray.init", "SetIterBoundedArray.maxSize"
      ensures "True";
     */
    {
        SetIterBoundedArray sa = new SetIterBoundedArray(10);
        //: assert "sa..SetIterBoundedArray.size = 0";

        Object charles = new Object();
        sa.insert(charles);

       //: assert "sa..SetIterBoundedArray.size = 1";
    }

    public static void main2(String[] args) 
    /*:
      modifies "SetIterBoundedArray.size", "SetIterBoundedArray.content", "SetIterBoundedArray.init", "SetIterBoundedArray.maxSize"
      ensures "True";
     */
    {
        SetIterBoundedArray sa = new SetIterBoundedArray(10);
        //: assert "sa..SetIterBoundedArray.size = 0";

        Object charles = new Object();
        Object viktor = new Object();
        Object karen = new Object();
        
        sa.insert(karen);
        sa.insert(charles);
        sa.insert(viktor);
       //: assert "sa..SetIterBoundedArray.size = 3";
    }
}
