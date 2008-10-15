Require Export Finite_sets_facts.

Parameter obj : Set.
Parameter Object : Ensemble obj.

Parameter null : obj.

Axiom obj_eq_dec : forall (a b:obj), {a=b}+{a<>b}.

(* an alpha array is a [nat -> alpha] 
  an alpha ArrayState is a [obj -> [nat ->alpha]] *)

Parameter fieldWrite : forall (A:Type), (obj -> A) -> obj -> A -> (obj->A).
Implicit Arguments fieldWrite [A].

Parameter ArrayWrite : forall (A B:Set), (B -> (nat -> A)) -> B -> nat -> A -> (B -> (nat->A)).
Implicit Arguments ArrayWrite [A B].

Axiom fieldwrite_match : forall A f o c o', o=o' -> (@fieldWrite A f o c) o' = c. 
Axiom fieldwrite_not_same : forall A f o c o', o<>o' -> (@fieldWrite A f o c) o' = f o'. 

Hint Resolve fieldwrite_match fieldwrite_not_same.


Axiom arraywrite_match :  forall A B ast a a' i' i c, a=a' -> i=i' -> (@ArrayWrite A B ast a i c) a' i' = c. 
Axiom arraywrite_not_same_i :  forall A B ast a a' i' i c, i<>i' -> (@ArrayWrite A B ast a i c) a' i' = ast a' i'. 
Axiom arraywrite_not_same_a :  forall A B ast a a' i' i c, a<>a' -> (@ArrayWrite A B ast a i c) a' i' = ast a' i'. 

Hint Resolve arraywrite_match arraywrite_not_same_i  arraywrite_not_same_a.

Inductive rtrancl_pt (P : obj -> obj -> Prop) : obj -> obj -> Prop :=
  | reflex x : rtrancl_pt P x x
  | trans x z : (exists y,  (rtrancl_pt P x y /\ rtrancl_pt P y z)) -> rtrancl_pt P x z
  | justP x y : P x y -> rtrancl_pt P x y.

Hint Resolve reflex reflex justP.