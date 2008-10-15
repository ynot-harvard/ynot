abst module Arrayset {
    use plugin "vcgen";
    Content = { x : Node | "exists j. 0 <= j & j < s & x : d[j]"};
    predvar setInit;

    invariant "0 < s";

}
