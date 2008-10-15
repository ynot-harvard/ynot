(** Decide the truth value of {!Form.form} formula
    that belongs to BAPA fragment.

    Convert {!Form.form} formula into bapa formula, then apply the algorithm {!Alpha} to convert it to Presburger arithmetic formula and then
    use decision procedure for Presburger arithmetic to decide the truth value of the formula.

   Two decision procedures for Presburger arithmetic are supported: LASH and Omega.
*)

let lashIsUnsatisfiable (f : Form.form) : bool =
  let _ = print_string ("\ninput formula:\n" ^ (PrintForm.string_of_form f) ^ "\n"); flush_all () in
  let bf = Formbapa.formToBapa f in
  let _ = print_string ("\nBAPA:\n" ^ (Alpha.string_of_form bf) ^ "\n>>>\n"); flush_all () in
  let pf = Bapapres.bapaFormToPresForm (Alpha.alpha bf) in
    Presburger.lashIsUnsatisfiable pf

let valid (f : Form.form) : bool =
  let _ = print_string ("\ninput formula:\n" ^ (PrintForm.string_of_form f) ^ "\n"); flush_all () in
  let bf = Formbapa.formToBapa f in
  let _ = print_string ("\nBAPA:\n" ^ (Alpha.string_of_form bf) ^ "\n>>>\n"); flush_all () in
  let pf = Bapapres.bapaFormToPresForm (Alpha.alpha bf) in
    Presburger.omegaIsValid pf
