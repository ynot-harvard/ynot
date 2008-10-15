open Common
open Form

(** Perform translation from formulas of type [Form.form] and first-order logic. 

    The aim is to use fast 1st-order automated theorem provers. 

    @author Charles Bouillaguet ({v charles.bouillaguet@dptinfo.ens-cachan.fr v}) *)



(** {6 The type of first-order formulas with equality and without function symbols of non-zero arity} *)
type basesort = [`I | `O | `F | `B | `Unknown]
type sort = [basesort |  `Set of basesort]

type ident = string
type boool = [`True | `False | `BoolVar of ident | `NegatedBoolVar of ident]  (** Boolean variables *)

type term = basesort * [`Int of int | `Constant of ident | `Variable of ident | `Function of ident*(term list) ]
type fol_atom = [`Predicate of ident*(term list) | `Equality of term*term]
type fol_formula = [
  boool 
| fol_atom
| `Negation of fol_formula 
| `Conjunction of fol_formula list 
| `Disjunction of fol_formula list 
| `Exists of (ident*basesort) list * fol_formula 
| `Forall of (ident*basesort) list * fol_formula]


(** {6 The main conversion function} *)


(** [fol_of_form s] gives a triplet which is made of : {ol
{- a list of axioms ensuring that, given an object [o] and a field [f], [o.f] takea at most one value.}
{- a list of assumptions. These are actually tuples of formulas. The old (untranslated) formula is given, for the sake of pretty-printing/debugging}
{- the goal of the sequent. Here again, the old formula is also given}
}
 *)
val fol_of_form : options:options_t -> sequent -> fol_formula list * (form*fol_formula) list * (form*fol_formula)

val backward_conversion_f : fol_formula -> Form.form
val awful_hack : Form.sequent -> options:options_t -> Form.sequent 
val add_guard : fol_formula -> fol_formula

val split_form : fol_formula -> fol_formula list
