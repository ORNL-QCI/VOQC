From QuickChick Require Import QuickChick.
Require Import ExtractReal.
Require Import Complex.
Require Import Optimizations.

Require Import SQIRE.

From ExtLib.Structures Require Import Monads.
Import MonadNotation. Open Scope monad_scope.

Import QcNotation. 

Instance ArbUni1 : Gen (Unitary 1) :=
  { arbitrary := 
      oneOf_ (ret U_H)
             (cons (ret U_H )
             (cons (ret U_X )
             (cons (ret U_Y )
             (cons (ret U_Z )
             (cons (liftM U_R arbitrary)
              nil)))))
  }.

Instance ArbIni2 : Gen (Unitary 2) :=
  { arbitrary := ret U_CNOT }.

Definition genUApp : G ucom :=
  bindGen (freq_ (returnGen 1%nat) (cons (5%nat, returnGen 1%nat)
                                  (cons (1%nat, returnGen 2%nat) nil))) (fun n =>
  match n with 
  | 1 => bindGen (@arbitrary (Unitary 1) _) (fun u =>
         bindGen (vectorOf 1 arbitrary) (fun l =>
         returnGen (uapp u l)))
  | 2 => bindGen (vectorOf 2 arbitrary) (fun l =>
         returnGen (uapp U_CNOT l))
  | _ => returnGen uskip
  end).
    
Fixpoint genSizedUcom (sz : nat) : G ucom :=
  match sz with
  | O => freq_ (ret uskip)
               (cons (1,ret uskip)
               (cons (6,genUApp)
                nil))
  | S sz' => freq_ (ret uskip)
                   (cons (1,ret uskip)
                   (cons (6,genUApp)
                   (cons (sz, bindGen (genSizedUcom sz') (fun uc1 =>
                              bindGen (genSizedUcom sz') (fun uc2 =>
                              returnGen (useq uc1 uc2))))
                         nil)))
  end%nat.

Instance GenSizedUcom : GenSized ucom :=
  { arbitrarySized := genSizedUcom }.

(* TODO : Fix Shrink *)
Instance ShrinkUcom : Shrink ucom :=
  { shrink := fun _ => nil }.

Require Import String.
Fixpoint show_unitary {n} (u : Unitary n) : string :=
  match u with
  | U_H => "U_H"
  | U_X => "U_X"
  | U_Y => "U_Y"
  | U_Z => "U_Z"
  | U_R r => "U_R" ++ show r
  | U_CNOT => "U_CNOT"
  end.

Instance ShowUnitary {n} : Show (Unitary n) :=
  { show := show_unitary }.

Fixpoint show_ucom (u : ucom) : string :=
  match u with
  | uskip => "SKIP"
  | useq u1 u2 => show_ucom u1 ++ ";;" ++ newline ++ show_ucom u2
  | uapp u l => "APP: " ++ show u ++ " " ++ show l
  end.

Instance ShowUcom : Show ucom :=
  { show := show_ucom }.

Fixpoint matrix_eqb {n1 n2 : nat} (m1 m2 : Matrix.Matrix n1 n2) : bool :=
  List.forallb (fun i => List.forallb (fun j => m1 i j = m2 i j?) (List.seq 0 n2))
               (List.seq 0 n1).

Axiom matrix_eqb_eq : forall {n1 n2 : nat} (m1 m2 : Matrix.Matrix n1 n2),
    matrix_eqb m1 m2 = true <-> m1 = m2.

Instance decMatrixEq (n1 n2 : nat) (m1 m2 : Matrix.Matrix n1 n2) : Dec (m1 = m2) := {}.
Proof.
  destruct (matrix_eqb m1 m2) eqn:Eq.
  - left; apply matrix_eqb_eq; auto.
  - right. intro H; apply matrix_eqb_eq in H; congruence.
Defined.    

(* TODO: Takes forever *)
(* QuickChick rm_uskips_sound. *)

(* Completely trivial injected bug: 
Fixpoint rm_uskips' (c : ucom) : ucom :=
  match c with
  | c1 ; c2 => match rm_uskips' c1, rm_uskips' c2 with
              | uskip, c2' => c2'
              | c1', _ => c1'
(*              | c1', c2'   => c1'; c2' *)
              end
  | c'      => c'
  end.

Conjecture rm_uskips_sound' 
     : forall c : ucom, UnitarySem.uc_equiv c (rm_uskips' c).

QuickChick rm_uskips_sound'.
*)
(* precondition: Fixpoint uc_well_typed_b (dim : nat) (c : ucom) : bool :=
*)