spec module Arrayset {
    default I = setInit;
    format Node;

    specvar setInit : bool;

    specvar Content : Node set;

    proc init() 
      suspends I
      requires true 
      modifies Content, setInit 
      ensures setInit' & card(Content') = 0;

    proc add(e:Node) 
      requires card(e) = 1
      modifies Content
      ensures (Content' = Content + e);

    proc remove(e:Node) 
      modifies Content
      ensures (Content' = Content - e);

    proc contains(e:Node) returns b:bool
      requires card(e)=1 
      ensures b' <=> (e in Content);

}
