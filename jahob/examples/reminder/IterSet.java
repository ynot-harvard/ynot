public interface IterSet {
    //: specfield setContent : "Object set" = "{}";
    //: specfield toIter : "Object set";

    public void add(Object o1)
    /*:
        requires "o1 != null & o1 ~: setContent"
        modifies setContent
        ensures "setContent = old(setContent) Un {o1}";
    */ ;

    public void remove(Object o1)
    /*:
        requires "o1 != null & o1 : setContent"
        modifies setContent, toIter
        ensures "setContent = old(setContent) - {o1} &
                 toIter = toIter - {o1}";
    */ ;

    public void initIter()
    /*:
        requires "true"
        modifies toIter
        ensures "toIter = setContent";
    */ ;

    public Object next()
    /*:
        requires "card toIter > 0"
        modifies toIter
        ensures "returned != null & 
                 returned : old(toIter) &
                 toIter = old(toIter) - {returned}";
    */ ;
}
