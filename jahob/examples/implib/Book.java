class Book {
    public String title;
    public String author;
    public int year;

    public void print()
    //: ensures "Object.alloc = old Object.alloc"
    {
        System.out.println(title + ", by " + author + ", " + year + ".");
    }
}
