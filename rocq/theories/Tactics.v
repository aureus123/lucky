(* Proof automation for the formalization (Ltac2).

   The labelings of the families of graphs are defined by cases on the index, with divisions
   and remainders by constants.  lia (with mczify) decides linear arithmetic over ssreflect's
   nat, including %/ and %% by constants and the boolean tests ==, <=, <, &&, ||, ~~ and odd,
   but not if-then-else.

   - split_lia      : decides linear arithmetic goals with if-then-else, in the goal or in the
                      hypotheses.  It works on the atomic conditions of the ifs: each one that
                      lia decides from the hypotheses is reduced, the others are split, and an
                      equation x == y that holds is substituted; every branch is closed by lia.
   - nlia           : lia, after normalizing the finType instances in the goal and the
                      hypotheses (equal terms elaborated at different instances look
                      different to lia).

   They are available in ssreflect scripts through Ltac1 wrappers of the same name. *)

From Ltac2 Require Import Ltac2 Constr.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div zify.

Set Default Proof Mode "Classic".

Ltac2 lia0 () := ltac1:(lia).

(** * nlia *)

(* lia, after normalizing the goal and the hypotheses: the elaboration of finType instances
   may leave reverse_coercion wrappers and unreduced projections (Finite.sort of an
   instance) in terms, which make equal terms look different to lia *)
Ltac2 nlia0 () :=
  ltac1:(try (unfold reverse_coercion in *));
  List.iter
    (fun (x : ident * constr option * constr) =>
       let (id, _, _) := x in
       try (ltac1:(id |- rewrite /= in id) (Ltac1.of_ident id)))
    (Control.hyps ());
  try (ltac1:(rewrite /=));
  lia0 ().

(** * split_lia *)

(* the first atomic condition of a boolean combination *)
Ltac2 rec atom (b : constr) : constr :=
  lazy_match! b with
  | ?x || _ => atom x
  | ?x && _ => atom x
  | ~~ ?x => atom x
  | _ => b
  end.

(* Reduce the conditionals on the atomic boolean b: by lia if it decides b, else by cases.
   b is rewritten in the goal and in every hypothesis; if it is an equation x == y that
   holds, the equation is substituted when one side is a variable. *)
Ltac2 case_atom (b : constr) :=
  let h := Fresh.in_goal @Hif in
  first
  [ assert ($b = true) as $h by lia0 ()
  | assert ($b = false) as $h by lia0 ()
  | ltac1:(b h |- case h : b) (Ltac1.of_constr b) (Ltac1.of_ident h) ];
  Control.enter (fun () =>
  let hb := Control.hyp h in
  List.iter
    (fun (x : ident * constr option * constr) =>
       let (id, _, _) := x in
       if Ident.equal id h then () else
       try (ltac1:(hb id |- rewrite hb in id) (Ltac1.of_constr hb) (Ltac1.of_ident id)))
    (Control.hyps ());
  try (ltac1:(hb |- rewrite hb) (Ltac1.of_constr hb));
  try (ltac1:(cbn [orb andb negb] in *));
  lazy_match! Constr.type hb with
  | (_ == _) = true =>
      try (ltac1:(hb |- let e := fresh "e" in move/eqP: (hb) => e; subst) (Ltac1.of_constr hb))
  | _ => ()
  end).

Ltac2 case_bool (b : constr) := case_atom (atom b).

Ltac2 rec split_lia0 () :=
  first
  [ lia0 ()
  | ltac1:(done)
  | match! goal with
    | [ |- context [ if ?b then _ else _ ] ] => case_bool b
    | [ _ : context [ if ?b then _ else _ ] |- _ ] => case_bool b
    end;
    Control.enter split_lia0 ].

Ltac2 split_lia () := Control.enter (fun () => ltac1:(rewrite /=); split_lia0 ()).

(** * Ltac1 wrappers for ssreflect scripts *)

Ltac split_lia := ltac2:(split_lia ()).
Ltac nlia := ltac2:(Control.enter nlia0).
