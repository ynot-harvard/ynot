class Library {
    public static FuncList persons;
    public static FuncList books;
    public static AssocList borrows;

    /*:
      public static specvar valid :: bool;
      vardefs "valid == BooksAllocated & BooksAreBooks & PersonsAllocated & PersonsArePersons & globalPointsTo & uniqueOwner";

      private static specvar BooksAllocated :: bool;
      vardefs "BooksAllocated == books..FuncList.content \<subseteq> Object.alloc";

      private static specvar BooksAreBooks :: bool;
      vardefs "BooksAreBooks == books..FuncList.content \<subseteq> Book";

      private static specvar PersonsAllocated :: bool;
      vardefs "PersonsAllocated == persons..FuncList.content \<subseteq> Object.alloc";

      private static specvar PersonsArePersons :: bool;
      vardefs "PersonsArePersons == persons..FuncList.content \<subseteq> Person";

      private static specvar globalPointsTo :: bool;
      vardefs "globalPointsTo == 
         (ALL p b. (p,b) : (borrows..AssocList.content) -->
	 ((p : persons..FuncList.content) 
	 & (b : books..FuncList.content)))";

      private static specvar uniqueOwner :: bool;
      vardefs "uniqueOwner == 
          (ALL p1 p2 b.
            ((p1,b) : borrows..AssocList.content &
             (p2,b) : borrows..AssocList.content) --> p1 = p2)";

    */

    // ------------------------------------------------------------
    //              Auxiliary private procedures
    // ------------------------------------------------------------

    public static void msg(String s)
    /*:
      requires "True"
      ensures "True";
     */
    {
        // System.out.println(s);
    }

    private static Person currentReader(Book b)
    /*: requires "globalPointsTo & PersonsArePersons & b ~= null & b : books..FuncList.content"
        ensures "(result = null --> (ALL p. (p,b) ~: borrows..AssocList.content)) &
               (result ~= null --> (result,b) : borrows..AssocList.content)";
     */
    {
        FuncList s = AssocList.inverseImage (b, borrows);
	Person r;
	

        if (FuncList.is_nil(s)) {
	    r = null;
        } else {
	    r = (Person) FuncList.head(s);
        }

	return r;
    }

    private static FuncList booksLentTo(Person p)
    /*:
      requires "valid & p ~= null & p : persons..FuncList.content"
      ensures "result..FuncList.content = {b. (p,b) : borrows..AssocList.content}";
     */
    {
        return AssocList.image(p, borrows);
    }

    // ------------------------------------------------------------
    //              Public procedures
    // ------------------------------------------------------------
    
    public static void initialize()
    /*: requires "True"
        modifies valid, books, persons, borrows, "books..FuncList.content", "persons..FuncList.content", "borrows..AssocList.content"
        ensures "valid & books..FuncList.content = {} & persons..FuncList.content = {} 
	& borrows..AssocList.content = {}"
    */
     {
	 books = FuncList.nil();
	 persons = FuncList.nil();
	 borrows = AssocList.nil();
     }

    
    public static void checkOutBook(Person p, Book b) // VERIFY THIS
    /*: requires "valid & p ~= null & b ~= null & b : books..FuncList.content & p : persons..FuncList.content"
       modifies valid, borrows, "borrows..AssocList.content"
       ensures "((p,b) : borrows..AssocList.content
                | (EX q. (q,b) : old borrows..AssocList.content))"
    */
    {
        if (currentReader(b) == null) {
            borrows = AssocList.cons(p, b, borrows);
        } else {
            msg("Sorry, book is not available.");
        }
    }

    public static void returnBook(Person p, Book b)
    /*: requires "valid & p ~= null & b ~= null & b : books..FuncList.content & p : persons..FuncList.content"
       modifies borrows, "borrows..AssocList.content"
       ensures "((p,b) : old borrows..AssocList.content & (p,b) ~: borrows..AssocList.content)
              | (EX q. q ~= p & (q,b) : old borrows..AssocList.content)
              | (ALL q. (q,b) ~: old borrows..AssocList.content)"
    */
    {
	Person cr = currentReader(b);
        if (cr==p) {
	    borrows = AssocList.remove(p, b, borrows);
        } else {
	    if (cr == null) {
            msg("This book was not borrowed !");
	    }
	    else {
            msg("Someone else was supposed to have that book!");
	    }
        }
    }

    public static void printBooksLentTo(Person p)
	/*: requires "valid & p ~= null & p : persons..FuncList.content"
	    ensures "True"
	*/
    {
	msg("Books lent to person");
	p.print();
	msg("  are: ");
	FuncList bs = booksLentTo(p);
	while   /* note, this is a comment inv "valid & bs..FuncList.content \<subseteq> Book" */ 
            (!FuncList.is_nil(bs))
	    {
		Book b = (Book) FuncList.head(bs);
		bs = FuncList.remove(b, bs);
		b.print();
	    }
    }

    public static void printCurrentReader(Book b)
	/*: requires "valid & b ~= null & b : books..FuncList.content"
	    ensures "True"
	*/
    {
        Person p = currentReader(b);
        if (p==null) {
            msg("The book is in the library.");
        } else {
            msg("Person ");
            p.print();
            msg("  has checked out the book ");
            b.print();
        }
    }


    public static void printStatus()
	/*: requires "valid"
	    ensures "True"
	*/
    {
        FuncList ps = AssocList.domain(borrows);
        while /* this is a comment inv "valid & ps..FuncList.content \<subseteq> persons..FuncList.content" */ (!FuncList.is_nil(ps))
        {
            Person p = (Person)(FuncList.head(ps));
	    ps = FuncList.remove(p, ps);
            printBooksLentTo(p);
        }
    }
}
