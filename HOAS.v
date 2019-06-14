Require Import SQIRE.

Open Scope ucom_scope.

(* It's probably better to use an inductive type here, I was just being lazy *)
Fixpoint vtuple (n : nat) :=
  match n with
  | 0 => unit
  | S n' => (nat * vtuple n')%type
  end.

Inductive Box n := box : (vtuple n -> ucom) -> Box n.
Arguments box {n}.

Definition boxS {n} (f : nat -> vtuple n -> ucom) : Box (S n) :=
  box (fun (v : vtuple (S n)) => let (x,v') := v in f x v').
Definition boxSS {n} (f : nat -> nat -> vtuple n -> ucom)  : Box (S (S n)) :=
  box (fun (v : vtuple (S (S n))) => let (x,v') := v in
                                     let (y,v'') := v' in
                                     f x y v'').

Notation "'box_' [] => c" := (box (fun _ => c))
  (at level 75).
Notation "'box_' ( v ) => c" := (box (fun v => c))
  (at level 75).
Notation "'box_' [ x ] => c" := 
  (box (fun (v : vtuple 1) =>
    match v with
    | (x,_) => c
    end))
  (at level 75).
Notation "'box_' ( x , v ) => c" := (boxS (fun x v => c))
  (at level 75).
Notation "'box_' [ x , y ] => c" := 
  (box (fun (v : vtuple 2) => 
    match v with
    (x,(y,_)) => c
    end))
  (at level 75).
Notation "'box_' ( x , y , v ) => c" := (boxSS (fun x y v => c))
  (at level 75).
Notation "'box_' [ x , y , z ] => c" := 
  (box (fun (v : vtuple 3) => 
     match v with
     | (x,(y,(z,_))) => c
     end))
  (at level 75).


Definition bell : Box 2 := box_ [c,b] => H c; CNOT c b.
Definition alice : Box 2 := box_ [a,c] => CNOT a c; H a.
Definition bob : Box 3 := box_ [a,c,b] => CNOT c b; CZ a b.

Definition unbox {n} (b : Box n) (v : vtuple n) : ucom :=
  match b with
  | box f => f v
  end.
Definition teleport : Box 3 := 
  box_ [a,c,b] => unbox alice (a,(c,tt)); unbox bob (a,(c,(b,tt))).


(*



foo := box_ [a0,a1,a2] => H a1; CNOT a0 a2

....

foo [b0,b4,b2]

box_ v => let [v<n,vn,vn+1,v>n+1] = split v in
          CNOT vn vn+1


*)

Definition vsplit n1 n2 (v : vtuple (n1+n2)) : vtuple n1 * vtuple n2.
Proof.
  induction n1 as [ | n1].
  * exact (tt,v).
  * destruct v as [x v'].
    destruct (IHn1 v') as [v1 v2].
    exact ((x,v1),v2).
Defined.

Definition inPar_HOAS {n1 n2 : nat} (b1 : Box n1) (b2 : Box n2) : Box (n1+n2) :=
  box (fun v => let (v1,v2) := vsplit n1 n2 v in
                unbox b1 v1; unbox b2 v2).

Require Export UnitarySem.
Local Open Scope ucom_scope.
Local Close Scope C_scope.
Local Close Scope R_scope.


Fixpoint vmap (f : nat -> nat) {n} : vtuple n -> vtuple n :=
  match n with
  | 0 => fun _ => tt
  | S n => fun v => let (x,v') := v in (f x, vmap f v')
  end.

Lemma vmap_id : forall n (v : vtuple n), vmap (fun x => x) v = v.
Proof.
  induction n; intros v; simpl in v.
  * destruct v. reflexivity.
  * destruct v as [x v].
    simpl.
    rewrite IHn.
    reflexivity.
Qed.
Lemma vmap_vmap : forall f g n (v : vtuple n),
      vmap f (vmap g v) = vmap (fun x => f (g x)) v.
Proof.
  induction n; intros v.
  * destruct v. reflexivity.
  * destruct v as [x v]. simpl.
    rewrite IHn.
    reflexivity.
Qed.
Lemma vmap_eq : forall f1 f2 n (v : vtuple n),
    (forall x, f1 x = f2 x) ->
    vmap f1 v = vmap f2 v.
Proof.
  intros f1 f2 n v H.
  generalize dependent n.
  induction n; intros v.
  - destruct v. reflexivity.
  - destruct v. simpl. rewrite H. rewrite IHn. reflexivity.
Qed.

Fixpoint vlist (n : nat) : vtuple n :=
  match n with
  | 0 => tt
  | S n' => (0,vmap (plus 1) (vlist n'))
  end.

Lemma vlistS : forall n, vlist (S n) = (0,vmap (plus 1) (vlist n)).
Proof. intros; reflexivity. Qed.

Definition beval {n} (b : Box n) : Matrix (2^n) (2^n) := 
  uc_eval n (unbox b (vlist n)).



Require Import Omega.
Lemma vlist_vsplit_vmap : forall n1 n2 f,
    vsplit n1 n2 (vmap f (vlist (n1+n2))) 
  = (vmap f (vlist n1), vmap (fun x => f(x+n1)) (vlist n2)).
Proof.
  intros n1 n2.
  induction n1; intros f; auto.
  * simpl. apply f_equal. apply vmap_eq.
    intros x. apply f_equal. omega.
  * simpl. rewrite vmap_vmap. rewrite IHn1. rewrite vmap_vmap. 
    apply f_equal. apply vmap_eq.
    intros x. apply f_equal. omega.
Qed.

Lemma vlist_vsplit : forall n1 n2, 
  vsplit n1 n2 (vlist (n1+n2)) = (vlist n1, vmap (plus n1) (vlist n2)).
Proof.
  intros n1 n2.
  rewrite <- (vmap_id _ (vlist (n1+n2))).
  rewrite vlist_vsplit_vmap. 
  rewrite vmap_id.
  apply f_equal. apply vmap_eq.
  intros x. omega.
Qed.

Require Import Compose.
(* safe use of HOAS doesn't depend on the actual values of the variables *)
Definition HOAS_abstract {n} (b : Box n) :=
  forall (v : vtuple n) (f : nat -> nat), unbox b (vmap f v) = map_qubits f (unbox b v).

(*
box [x] => if x = 0 then .... else ...
NO: H 0
Name of this property in hybrid? abstr?
*)

Lemma inPar_HOAS_correct : forall {n1 n2} (b1 : Box n1) (b2 : Box n2),
  uc_well_typed n1 (unbox b1 (vlist n1)) -> 
  HOAS_abstract b2 ->
  beval (inPar_HOAS b1 b2) = beval b1 ⊗ beval b2.
Proof.
  intros n1 n2 b1 b2 typed_b1 abstr_b2.
  unfold beval.
  unfold inPar_HOAS, unbox at 1.
  rewrite vlist_vsplit.
  simpl.
  rewrite <- (pad_dims_r (unbox b1 (vlist n1))); auto.
  rewrite abstr_b2.

  rewrite <- (pad_dims_l (unbox b2 (vlist n2))); [ | intros q; omega].

  restore_dims_strong.
  Msimpl.
  reflexivity.
Qed.


(* -- [b] -- | - | ---
   ----------| f | ---
   ----------| _ | ---
*)
(* What's the right form of composition? *)
Definition compose {m n} (b : Box m) (f : vtuple m -> vtuple n -> ucom) 
    : Box (m+n) :=
  box (fun v => let (vm,vn) := vsplit m n v in
                unbox b vm; f vm vn).


(** GHZ **)


Program Fixpoint hGHZ n : Box n :=
  match n with
  | 0    => box_ [] => uskip
  | S n' => match n' with
            | 0     => (* n = 1 *) box_ [x] => H x
            | S n'' => (* n = n''+2 *)
                       box_ (x,y,v) => unbox (hGHZ n' : Box (S n'')) (y,v); 
                                       CNOT x y
            end
  end.

Lemma hGHZ_SS : forall n, 
  hGHZ (S (S n)) = box_ (x,y,v) => unbox (hGHZ (S n)) (y,v); 
                                   CNOT x y.
Proof.
  intros n. reflexivity.
Qed.
Lemma unbox_box : forall n (f : vtuple n -> ucom) (v : vtuple n),
    unbox (box f) v = f v.
Proof.
  intros n. reflexivity.
Qed.
Lemma vmapS : forall n f x (vs : vtuple n), vmap f ((x,vs) : vtuple (S n)) = (f x, vmap f vs).
Proof. intros. reflexivity. Qed.



Require Import GHZ.

Lemma hGHZ_abstract : forall n, HOAS_abstract (hGHZ n).
Proof.
  induction n as [ | [ | n]].
  - simpl. unfold HOAS_abstract.
    intros v f. destruct v.
    reflexivity.
  - intros [ x [ ] ] f.
    simpl.
    reflexivity.
  - intros [ x [ y v ]] f.
    repeat rewrite vmapS.
    unfold HOAS_abstract in IHn.
    rewrite hGHZ_SS.
    transitivity (unbox (hGHZ (S n)) (f y, vmap f v); CNOT (f x) (f y)); [reflexivity | ].
    replace (f y, vmap f v) with (vmap f ((y,v) : vtuple (S n))) by reflexivity.
    rewrite IHn.
    reflexivity.
Qed.


(* Problem: the dependent types means that the simplification is less automatic. We could have better tactics to address this, but it'll be with rewrite rules, which is a bummer. *)
Theorem hGHZ_correct : forall n, beval (hGHZ n) × nket n ∣0⟩ = ghz n.
Proof.
  intros n.
  induction n as [ | [ | n'']].
  - simpl. solve_matrix.
  - unfold beval. simpl. solve_matrix. unfold ueval1. unfold pad. simpl.
    rewrite kron_1_r. rewrite kron_1_l. reflexivity. auto with wf_db.
  - rewrite hGHZ_SS.
    unfold beval. 
    unfold boxSS.
    rewrite unbox_box.
    rewrite vlistS.
    rewrite vlistS.
    rewrite vmapS.
    rewrite vmap_vmap.
    replace (1+0,vmap (fun x : nat => 1 + (1 + x)) (vlist n''))
       with (vmap (plus 1) (vlist (S n''))).
    2:{ rewrite vlistS. rewrite vmapS. rewrite vmap_vmap. reflexivity. }

    remember (vmap (plus 1) (vlist (S n''))) as v eqn:Hv.
    replace (1+0) with 1 by reflexivity.


    replace (uc_eval (S (S n'')) (unbox (hGHZ (S n'')) v; CNOT 0 1))
       with (uc_eval (S (S n'')) (CNOT 0 1)
           × uc_eval (S (S n'')) (unbox (hGHZ (S n'')) v))
       by reflexivity.

    subst.
    rewrite hGHZ_abstract.

    rewrite <- (pad_dims_l (unbox (hGHZ (S n'')) (vlist (S n''))) 1 (S n'')).
    2:{ intros q. omega. }

    unfold beval in IHn.

    rewrite nket_l by auto with wf_db.
    rewrite Mmult_assoc.
    restore_dims_strong.
    rewrite kron_mixed_product.

    rewrite IHn.

    (* This is true -- how to solve? *)
    replace (S (S n'')) with (2+n'') by auto.
    rewrite <- (pad_dims_r (CNOT 0 1) 2 n'').
    rewrite eval_CNOT.
    2:{ apply WT_app; auto. 
        apply in_bounds_eq; auto.
        repeat constructor. inversion 1. inversion H0. inversion H0. 
        inversion 1.
      }


    simpl.
    autorewrite with ket_db; auto with wf_db.
    restore_dims_strong.
    replace (n''-0-0) with n'' by omega.
    

Admitted.