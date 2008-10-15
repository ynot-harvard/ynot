public interface IterSet {
    //: specfield setContent : "Object set" = "{}";
    //: specfield toIter : "Object set" = "{}";

    public void add(Object o)
    /*:
        requires "o != null & o ~: setContent"
        modifies setContent
        ensures "setContent = old(setContent) Un {o}";
    */ ;

    public void remove(Object o)
    /*:
        requires "o != null & o : setContent"
        modifies setContent, toIter
        ensures "setContent = old(setContent) - {o} &
                 toIter = toIter - {o}";
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
