class Person {
    public String firstName;
    public String lastName;

    public void print()
    //: ensures "Object.alloc = old Object.alloc"
    {
        System.out.println(firstName + " " + lastName);
    }
}
