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

Notation "'box_' [] => c" := (box (fun _ => c))
  (at level 75).
Notation "'box_' [ x ] => c" := 
  (box (fun (v : vtuple 1) =>
    match v with
    | (x,_) => c
    end))
  (at level 75).
Notation "'box_' [ x , y ] => c" := 
  (box (fun (v : vtuple 2) => 
    match v with
    (x,(y,_)) => c
    end))
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
Definition teleport : Box 3 := box_ [a,c,b] => unbox alice (a,(c,tt)); unbox bob (a,(c,(b,tt))).

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
Admitted.

Fixpoint vlist (n : nat) : vtuple n :=
  match n with
  | 0 => tt
  | S n' => (0,vmap (plus 1) (vlist n'))
  end.

Definition beval {n} (b : Box n) : Matrix (2^n) (2^n) := uc_eval n (unbox b (vlist n)).



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
Definition HOAS_correct {n} (b : Box n) :=
  forall (v : vtuple n) (f : nat -> nat), unbox b (vmap f v) = map_qubits f (unbox b v).

Lemma inPar_HOAS_correct : forall {n1 n2} (b1 : Box n1) (b2 : Box n2),
  uc_well_typed n1 (unbox b1 (vlist n1)) -> 
  HOAS_correct b2 ->
  beval (inPar_HOAS b1 b2) = beval b1 ⊗ beval b2.
Proof.
  intros n1 n2 b1 b2 typed_b1 correct_b2.
  unfold beval.
  unfold inPar_HOAS, unbox at 1.
  rewrite vlist_vsplit.
  simpl.
  rewrite <- (pad_dims_r (unbox b1 (vlist n1))); auto.
  rewrite correct_b2.

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