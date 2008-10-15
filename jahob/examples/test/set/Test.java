public final class Test
{
    public static void test()
    /*:
        requires "True"
	modifies "GlobalSet.setContent"
	ensures "card GlobalSet.setContent > 0"
     */
    {	
	GlobalSet s = new GlobalList();
	s.init();
	Object o7 = new Object();
	s.add(o7);
    }

    public static void fakeInit() 
    /*: 
        requires "True"
        modifies "content"
        ensures "content = {}";
    */
    {
    }

    public static void fakeAdd(Object oo)
    /*: 
        requires "True"
        modifies "content" 
        ensures "content = (old content) Un {oo}";
    */
    {
    }

    public static void main()
    /*:
      requires "finite content & (card content = n) & 
                (content Int alloc_Object = {})"
      modifies "content" 
      ensures "card content = (n + 1::nat)";
    */

    {
	Object o1 = new Object();
	fakeAdd(o1);
	/* Here is an Isabelle proof, note that it requires a lemma,
	   and even with it, it takes a while.

lemma foo: "[|(x_3 : alloc_Object);
((content Int alloc_Object) = {})|] ==> 
x_3 ~: content"
apply auto
done

lemma 0: "([|(x_3 : alloc_Object);
(~(x_3 = nullObj));
(x_1 = (content Un {x_3}));
finite content;
((card content) = n);
((content Int alloc_Object) = {})|] ==>
    ((card x_1) = ((n + 1) :: nat)))"
apply (auto simp add: foo)
done
	*/
    }

    public static void main1()
    /*:
      requires "card content = n" 
      modifies "content" 
      ensures "card content = (n + 2::nat)";
    */
    {
	Object o1 = new Object();
	Object o2 = new Object();
	fakeAdd(o1);
	fakeAdd(o2);
    }

    public static void main0()
    /*:
      requires "g content" 
      modifies "content"
      ensures "f content (old content)";
    */
    {
	Object o1 = new Object();
	Object o2 = new Object();
	fakeAdd(o1);
	fakeAdd(o2);
    }
}
