// Not finished
public final class AssocList 
    /* unsorted global association list with potentially duplicate keys */
{
    private static Node first;

    /*: 
      private static specvar inlist :: objset;
      vardefs
        "inlist == {n. n ~= null & rtrancl_pt (% x y. x..Node.next=y) AssocList.first n}";

      invariant "tree [Node.next, Node.key]";

      public static specvar content :: "(obj * obj) set";
      vardefs 
        "content == {(k,v). EX n. k = n..Node.key & v = n..Node.value & n : inlist}";

      private static specvar reach :: "obj => obj => bool";
      vardefs
        "reach == (% a b. rtrancl_pt (% x y. x..Node.next=y) a b)";

      invariant "ALL v. v : inlist --> (v..Node.key ~= null) & (v..Node.value ~= null)";

      private static specvar isolated :: "obj => bool";
      vardefs
        "isolated == (% n. (ALL v. v ~= null --> v..Node.next ~= n & v..Node.key ~= n))";

      invariant "ALL n. n ~= null & ~ rtrancl_pt (% x y. x..Node.next=y | x..Node.key=y) first n
                 --> isolated n";

    */

    public static void init()
    /*: modifies content
        ensures "ALL x. x ~: content"
    */
    {
        first = null;
        //: noteThat "ALL x. x ~: inlist";
    }

    public static boolean isEmpty()
    /*: ensures "result = (ALL x. x ~: content)";
    */
    {
        // Sadly, this does not work when we add an additional invariant on isolation,
        // because that invariant confuses Isabelle.

        boolean res = (first==null);
        //: noteThat "res = (ALL x. x ~: inlist)";
        return res;
    }

    public static boolean defined(Object key)
    /*: ensures "result = (EX v. (key,v) : content)" */
    {
        Node n = first;
        while /*: inv "reach first n &
                       (ALL v. v ~= null & reach first v & ~ reach n v --> v..Node.key ~= key)" */
            (n != null) {
            if (n.key==key) {
                return true;
            }
            n = n.next;
        }
        //: noteThat "comment ''notFound'' (ALL v. v : inlist --> v..Node.key ~= key)";
        return false;
    }

    public static Object lookup(Object key)
    /*: ensures "(key,result) : content | 
                 (ALL v. (key,v) ~: content)" */
    {
        Node n = first;
        while /*: inv "reach first n &
                       (ALL v. v ~= null & reach first v & ~ reach n v --> v..Node.key ~= key)" */
            (n != null) {
            if (n.key==key) {
                return n.value;
            }
            n = n.next;
        }
        //: noteThat "comment ''notFound'' (ALL v. v : inlist --> v..Node.key ~= key)";
        return null;
    }

    public static void remove(Object key)
    /*: requires "key ~= null & (EX v. (key,v) : content)"
        modifies content
        ensures "content = old content - {(x,y). x = key}"
    */
    { // Need to see if isolation invariant preserved.
        Node f = first;
        //: noteThat "EX x. x : inlist";
        //: noteThat "f ~= null";
        //: noteThat "comment ''present'' (EX v. v ~= null & reach f v & v..Node.key = key)";
        if (f.key==key) {
            //: noteThat "comment ''othersDifferent'' (ALL v. v : inlist & v ~= f --> v..Node.key ~= key)";
            first = f.next;            
            f.next = null;
            f.key = null;
            f.value = null;
            //: noteThat "inlist = old inlist - {f}";
            //: noteThat "ALL v. v : inlist --> v..Node.key ~= key";

            /* This lemma suffices to prove postcondition.
               Unfortunately, the generated VC has additional assumptions that confuse Isabelle and even
               slicing does not help.

               lemma AssocList_remove_InitialPartOfProcedure11: "([|
               (AssocList_content = {p. (EX k v. ((p = (k, v)) & (EX n. ((k = (fieldRead Node_key n)) & (n : AssocList_inlist) & (v = (fieldRead Node_value n))))))});
               (AssocList_first ~= null);
               ((fieldRead Node_key AssocList_first) = key);
               comment ''othersDifferent'' (ALL v. (((v : AssocList_inlist) & (v ~= AssocList_first)) --> ((fieldRead Node_key v) ~= key)));
               (AssocList_content_25 = {p. (EX k v. ((p = (k, v)) & (EX n. ((k = (fieldRead (fieldWrite Node_key AssocList_first null) n)) & (n : AssocList_inlist_31) & (v = (fieldRead (fieldWrite Node_value AssocList_first null) n))))))});
               (AssocList_inlist_31 = (AssocList_inlist - {AssocList_first}));
               (ALL v. ((v : AssocList_inlist_31) --> ((fieldRead (fieldWrite Node_key AssocList_first null) v) ~= key)))
               |] ==>
               (AssocList_content_25 = (AssocList_content - {p. (EX x y. ((p = (x, y)) & (x = key)))})))"

             */
        } else {
            Node prev = f;
            Node n = f.next;
            while /*: inv "reach first prev & prev..Node.next = n &
                    (EX v. v ~= null & reach n v & v..Node.key = key) &
                    (ALL v. v ~= null & reach first v & ~ reach n v --> v..Node.key ~= key)" */
                (n.key != key) {
                prev = n;
                n = n.next;
                //: noteThat "n ~= null";
            }
            prev.next = n.next;
            n.key = null;
            n.next = null;
            n.value = null;
            //: noteThat "inlist = old inlist - {n}";
            //: noteThat "ALL v. v : inlist --> v..Node.key ~= key";            
            /* Verification condition for this branch is also true, but extra assumptions 
               prevent Isabelle from proving it.
            */
        }
        // Bug: had a bug where was not checking for the first element.
        // Bug: another bug where I thought I was removing occurrences of null, but I did not.
        // Bug: Had to change the invariant to require non-null keys and values to avoid tranversing the entire structure.
        // Bug: In while loop I initially forgot to update prev, so got obviously wrong VC.
    }

    public static void add(Object key, Object value)
    /*: requires "key ~= null & value ~= null"
        modifies content
        ensures "content = old content Un {(key,value)}"
    */
    {
        //: noteThat "comment ''notDefined'' (ALL v. v : inlist --> v..Node.key ~= key)";
        Node n = new Node();
        n.key = key;
        n.value = value;
        n.next = first;
        first = n;
        //: noteThat "comment ''inserted'' (inlist = old inlist Un {n})";
    }

    public static void update(Object key, Object value) // TODO
    /*: requires "key ~= null & value ~= null"
        modifies content
        ensures "content = (old content - {(x,y). x=key}) Un {(key,value)}"
    */
    {
        Node n = first;
        while /*: inv "reach first n &
                       (ALL v. v ~= null & reach first v & ~ reach n v --> v..Node.key ~= key)" */
            ((n != null) && (n.key != key)) {
            n = n.next;
        }
        if (n==null) {
            //: noteThat "comment ''notDefined'' (ALL v. v : inlist --> v..Node.key ~= key)";
            n = new Node();
            n.key = key;
            n.value = value;
            n.next = first;
            first = n;
            //: noteThat "comment ''inserted'' (inlist = old inlist Un {n})";
        } else {
            //: assume "False";
            n.value = null;
        }
        /* Realized a missing precondition that key is not part of an unreachable structure with sharing... Introduced isolated invariant.
           But then init violates it, so that is restrictive.  So implement a garbage collection transformation
           in verification condition generator?

           It also seems that this invariant is not preserved by MONA even with no modifications?!
        */
    }

}
