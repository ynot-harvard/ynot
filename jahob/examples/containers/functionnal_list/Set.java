public class Set
{
   private FuncList lst;

   /*: 
     public specvar content :: objset;
     vardefs "content == lst..FuncList.content";

     public ensured invariant ("ContentAlloc") "content \<subseteq> Object.alloc";
   */

    public Set()
    /*: 
      modifies content 
      ensures "content = {}"
    */
    {
        lst = FuncList.nil();
    }

    public static Set setOfFuncList(FuncList l)
    /*:
      ensures "result..content = l..FuncList.content & result ~= null";
    */
    {
        Set s = new Set();
        s.lst = l;
        return s;
    }

    public void add(Object o1)
    /*: requires "o1 ~= null"
        modifies content
        ensures "content = old content Un {o1}"
    */
    {
        lst = FuncList.cons(o1, lst);
    }

    public boolean isEmpty()
    /*: ensures "result = (content = {})";
    */
    {
        return FuncList.is_nil(lst);
    }

    public Object getOne()
    /*: requires "content ~= {}"
        ensures "result : content";
    */
    {
        return FuncList.head(lst);
    }

    public boolean member(Object o1)
    //: ensures "result = (o1 : content)";
    {
        return FuncList.is_in(o1, lst);
    }

    public void remove(Object o1)
    /*: modifies content
        ensures "content = old content \<setminus> {o1}";
    */
    {
        lst = FuncList.remove(o1, lst);
    }

    public static void main(String[] args)
    {
        Set l = new Set();

	Object o1 = new Object();
        Object o2 = new Object();
        Object o3 = new Object();
        Object o4 = new Object();
	
       
        l.add(o1);
        l.add(o2);
        l.add(o3);
        l.add(o4);
        l.remove(o2);
        l.remove(o4);
        l.remove(o1);

        if (l.isEmpty()) {
            //System.out.println("Oops, the list is empty but should have one element.");
        } else {
            //System.out.println("ok1.");
        }
        l.remove(o3);
        if (!l.isEmpty()) {
            //System.out.println("Oops, the list is not empty but should be.");
        } else {
            //System.out.println("ok2.");
        }
    }


}
