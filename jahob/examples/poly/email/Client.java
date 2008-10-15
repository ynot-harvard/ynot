class Client {

    public static void main(String[] args) 
    {
        Person p_v = new Person("Viktor");
        Email e = new Email(p_v);
        Person p_b = new Person("Bruno");
        Person p_m = new Person("Martin");
        e.addRecipient(p_b);
        e.addRecipient(p_m);
        e.setSubject(new Text("paper"));
        e.setBody(new Text("I wrote the example, let me know what you think."));
        e.removeRecipient(p_m);
        if (e.isWellFormed()) {
            e.send();
        }
    }

}
