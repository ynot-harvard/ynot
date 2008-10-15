public interface GlobalSet {
    //: specstatic setContent : "Object set" = "{}"

    public void init()
    /*:
        requires "True" 
	modifies setContent
	ensures "setContent = {}"
    */ ;

    public void add(Object o1)
    /*:
        requires "o1 != null & o1 ~: setContent"
        modifies setContent
        ensures "setContent = old(setContent) Un {o1}"
    */ ;

    public void remove(Object o1)
    /*:
        requires "o1 != null & o1 : setContent"
        modifies setContent
        ensures "setContent = old(setContent) - {o1}"
    */ ;
}
