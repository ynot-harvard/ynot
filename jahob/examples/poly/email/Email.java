class Email {
    //: public specvar init :: bool = "false";

    private Person sender;
    //: private invariant "init --> sender ~= null";

    private List recipients;
    /*: private invariant "init --> 
          (recipients ~= null) & 
          (ALL x. x : recipients..content --> x : Person)"
    */

    private Text subject;
    private Text body;

    public Email(Person sender1)
    /*: requires "sender1 ~= null"
        modifies init
        ensures init;
    */
    {
        sender = sender1;
        recipients = new List();
    }

    //: public specvar wellFormed :: bool;
    /*: vardefs "wellFormed == 
          init & 
          (card (recipients..content) >= 1) &
          (subject ~= null) &
          (body ~= null)";
    */
    //: public invariant "wellFormed --> init";

    public void addRecipient(Person recipient1)
    /*: requires "init & (recipient1 ~= null)"
        modifies wellFormed
        ensures "True";
    */
    {
        recipients.add(recipient1);
    }

    public void removeRecipient(Person recipient1)
    /*: requires "init & (recipient1 ~= null)"
        modifies wellFormed
        ensures "True";
    */
    {
        recipients.remove(recipient1);
    }

    public void setSubject(Text subject1)
    /* requires "init & (subject1 ~= null)"
       modifies wellFormed
       ensures "True";
    */
    {
        subject = subject1;
    }

    public void setBody(Text body1)
    /* requires "init & (body1 ~= null)"
       modifies wellFormed
       ensures "True";
    */
    {
        body = body1;
    }

    public boolean isWellFormed()
    /*: requires init
        ensures "result = wellFormed";
    */
    {
        return 
            !recipients.isEmpty() && 
            subject != null && 
            body != null;
    }

    public void send() 
    /*: requires wellFormed
        ensures "True";
    */
    {
    }
}
