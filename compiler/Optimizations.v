Require Import Phase.
Require Import UnitarySem.
Require Import Representations.
Require Import Equivalences.
Require Import Proportional.
Require Import List.
Open Scope ucom.

(********************************)
(** Optimization: remove skips **)
(********************************)

Fixpoint rm_uskips {dim} (c : ucom dim) : ucom dim :=
  match c with
  | c1 ; c2 => match rm_uskips c1, rm_uskips c2 with
              | uskip, c2' => c2'
              | c1', uskip => c1'
              | c1', c2'   => c1'; c2'
              end
  | c'      => c'
  end.

(* The output of rm_uskips is well-typed.
   (Note that well-typedness is not necessary in the soundness proof.) *)
Hint Constructors uc_well_typed : type_db.
Lemma WT_rm_uskips : forall {dim} (c : ucom dim), uc_well_typed c <-> uc_well_typed (rm_uskips c).
Proof.
  intros dim c.
  split; intros H.
  - induction H.
    + constructor.
    + simpl.
      destruct (rm_uskips c1), (rm_uskips c2); auto with type_db.
    + simpl. auto with type_db.
    + simpl. auto with type_db.
  - induction c.
    + constructor.
    + destruct (rm_uskips (c1; c2)) eqn:E.
      * simpl in E.
        destruct (rm_uskips c1), (rm_uskips c2); auto with type_db; discriminate.
      * simpl in E.
        destruct (rm_uskips c1) eqn:E1, (rm_uskips c2) eqn:E2; auto with type_db;
        rewrite <- E in H; inversion H; auto with type_db.
      * simpl in E.
        destruct (rm_uskips c1) eqn:E1, (rm_uskips c2) eqn:E2; auto with type_db;
        rewrite <- E in H; inversion H; auto with type_db.
      * simpl in E.
        destruct (rm_uskips c1) eqn:E1, (rm_uskips c2) eqn:E2; auto with type_db;
        rewrite <- E in H; inversion H; auto with type_db.
    + simpl in H; easy.
    + simpl in H; easy.
Qed.      

(* rm_uskips is semantics-preserving. *)
Lemma rm_uskips_sound : forall {dim} (c : ucom dim),
  c ≡ (rm_uskips c).
Proof.
  induction c; try reflexivity.
  unfold uc_equiv; simpl.
  destruct (rm_uskips c1) eqn:E1, (rm_uskips c2) eqn:E2; trivial;
    rewrite IHc1, IHc2; simpl; Msimpl; easy.
Qed.

(* Alternate proof using congruence instead of Msimpl. *)
Lemma rm_uskips_sound' : forall {dim} (c : ucom dim),
  c ≡ (rm_uskips c).
Proof.
  induction c; try reflexivity.
  simpl.
  destruct (rm_uskips c1); destruct (rm_uskips c2);
    rewrite IHc1, IHc2;
    try apply uskip_id_l; try apply uskip_id_r;
    reflexivity.
Qed.

(* The output of rm_uskips is either a single skip intruction, or a program
   that contains no skip instructions. *)
Inductive skip_free {dim} : ucom dim -> Prop :=
  | SF_seq : forall c1 c2, skip_free c1 -> skip_free c2 -> skip_free (c1; c2)
  | SF_app1 : forall n (u : Unitary 1), skip_free (uapp1 u n)
  | SF_app2 : forall m n (u : Unitary 2), skip_free (uapp2 u m n).

Lemma rm_uskips_correct : forall {dim} (c : ucom dim),
  (rm_uskips c) = uskip \/ skip_free (rm_uskips c).
Proof.
  induction c.
  - left; easy.
  - destruct IHc1; destruct IHc2.
    + left. simpl. rewrite H. rewrite H0. reflexivity.
    + right. simpl. rewrite H. assumption.
    + right. simpl. rewrite H0. 
      destruct (rm_uskips c1); try easy.
    + right. simpl. 
      destruct (rm_uskips c1); try assumption;
      destruct (rm_uskips c2); try (apply SF_seq); easy. 
  - right; simpl. apply SF_app1.
  - right; simpl. apply SF_app2.
Qed.

(* The output of rm_uskips has no more operations than the input program. *)
Local Close Scope C_scope.
Local Close Scope R_scope.

Fixpoint count_ops {dim} (c : ucom dim) : nat :=
  match c with
  | c1; c2 => (count_ops c1) + (count_ops c2)
  | _ => 1
  end.

Lemma rm_uskips_reduces_count : forall {dim} (c : ucom dim),
  count_ops (rm_uskips c) <= count_ops c.
Proof.
  induction c; try (simpl; lia).
  simpl. destruct (rm_uskips c1); try lia; 
  destruct (rm_uskips c2); 
  simpl in *;
  lia.
Qed.


(***********************************)
(** Optimization: not propagation **)
(***********************************)

(* Propagate an X gate on qubit q as far right as possible, cancelling
   the gate if possible.
   
   This will return None if no cancellation is possible or (Some l') 
   where l' is the result of removing the appropriate X gate from l. *)
Fixpoint propagate_not {dim} (l : gate_list dim) (q : nat) : option (gate_list dim) :=
  match l with
  | (App1 fU_X q') :: t => 
      if q =? q' then Some t 
      else match propagate_not t q with
           | None => None
           | Some l' => Some ((_X q') :: l')
           end
  | (App2 fU_CNOT q1 q2) :: t => 
      if q =? q1 then None 
      else match propagate_not t q with
           | None => None
           | Some l' => Some ((_CNOT q1 q2) :: l')
           end
  | (App1 u q') :: t => 
      if (q =? q')
      then None
      else match propagate_not t q with
           | None => None
           | Some l' => Some ((App1 u q') :: l')
           end
  | _ => None
  end.

(* Call propagate_not on all X gates in the circuit. 
   
   The extra n argument is to help Coq recognize termination.
   We start with n = (length l), which is the maximum
   number of times that propagate_nots will be called. *)
Fixpoint propagate_nots {dim} (l : gate_list dim) (n: nat) : gate_list dim :=
  match n with
  | 0 => l
  | S n' => match l with
           | (App1 fU_X q) :: t => 
               match propagate_not t q with
               | None => (App1 fU_X q) :: (propagate_nots t n')
               | Some l' => propagate_nots l' n'
               end
           | h :: t => h :: (propagate_nots t n')
           | _ => l
           end
  end.

Definition rm_nots {dim} (l : gate_list dim) : gate_list dim := 
  propagate_nots l (List.length l).

(* Small test cases. *)
Definition q0 : nat := 0.
Definition q1 : nat := 1.
Definition q2 : nat := 2.
Definition example1 : gate_list 3 := (_X q0) :: (_H q1) :: (_X q0) :: (_X q1) :: (_CNOT q2 q1) :: (_X q1) :: [].
Compute (rm_nots example1).
Definition example2 : gate_list 3 := (_X q0) :: (_X q1) :: (_X q2) :: [].
Compute (rm_nots example2).

(* propagate_not preserves well-typedness. *)
Lemma propagate_not_WT : forall {dim} (l l' : gate_list dim) q,
  uc_well_typed_l l ->
  propagate_not l q = Some l' ->
  uc_well_typed_l l'.
Proof.
  intros.
  generalize dependent l'.
  induction l; try easy.
  simpl; intros.
  destruct a. 
  dependent destruction f; 
  (* u = H, Z, T, TDAG, P, PDAG *)
  try (destruct (q =? n); try easy;
       destruct (propagate_not l q); try easy;
       inversion H; inversion H0; subst;
       constructor; try apply IHl; easy).
  - (* u = X *)
    destruct (q =? n).
    + inversion H; inversion H0; subst. assumption.
    + destruct (propagate_not l q); try easy.
      inversion H; inversion H0; subst.
      constructor; try apply IHl; easy.
  - (* u = CNOT *)
    dependent destruction f.
    destruct (q =? n); try easy.
    destruct (propagate_not l q); try easy.
    inversion H; inversion H0; subst.
    constructor; try apply IHl; easy.
Qed.

(* propagate_not is semantics-preserving. *)
Lemma propagate_not_sound : forall {dim} (l l' : gate_list dim) q,
  q < dim ->
  propagate_not l q = Some l' ->
  l' =l= (App1 fU_X q) :: l.
Proof.
  intros.
  generalize dependent l'.
  induction l; try easy.
  simpl; intros.   
  destruct a.
  dependent destruction f;
  (* u = H, Z, T, TDAG, P, PDAG *)
  try (bdestruct (q =? n); try easy;
       destruct (propagate_not l q); try easy;
       inversion H0; subst;
       rewrite IHl with (l':=g); trivial;
       apply U_V_comm_l; lia).
  - (* u = X *)
    bdestruct (q =? n).
    + inversion H0; subst.
      unfold uc_equiv_l; simpl.
      rewrite <- useq_assoc.
      rewrite (useq_congruence _ uskip _ (list_to_ucom l')); 
      try rewrite uskip_id_l; 
      try reflexivity.
      symmetry; apply XX_id. 
      constructor; assumption.
    + destruct (propagate_not l q); inversion H0; subst.
      rewrite IHl with (l':=g); trivial.
      apply U_V_comm_l; lia.
  - (* u = CNOT *)
    dependent destruction f.
    bdestruct (q =? n); try easy.
    destruct (propagate_not l q); inversion H0; subst.
    rewrite IHl with (l':=g); trivial.
    bdestruct (q =? n0).
    + subst. 
      unfold uc_equiv_l; simpl.
      repeat rewrite <- useq_assoc.
      rewrite (useq_congruence (uapp2 U_CNOT n n0; uapp1 U_X n0) (uapp1 U_X n0; uapp2 U_CNOT n n0) _ (list_to_ucom l)); try reflexivity.
      symmetry; apply X_CNOT_comm.
    + unfold uc_equiv_l; simpl.
      repeat rewrite <- useq_assoc.
      rewrite (useq_congruence (uapp2 U_CNOT n n0; uapp1 U_X q) (uapp1 U_X q; uapp2 U_CNOT n n0) _ (list_to_ucom l)); try reflexivity.
      symmetry; apply U_CNOT_comm; assumption.
Qed.   

(* propagate_nots is semantics-preserving. *)
Lemma propagate_nots_sound : forall {dim} (l : gate_list dim) n, 
  uc_well_typed_l l -> l =l= propagate_nots l n.
Proof.
  intros.
  generalize dependent l.
  induction n; try easy.
  intros l WT.
  destruct l; try easy.
  destruct g.
  inversion WT; subst.
  simpl.
  dependent destruction f;
  (* u = H, Z, T, TDAG, P, PDAG *)
  try (apply (cons_congruence _ l (propagate_nots l n));
       apply IHn; assumption).
  (* u = X *)
  - specialize (@propagate_not_sound dim) as H4.
    remember (propagate_not l n0) as x.
    destruct x.
    + symmetry in Heqx.
      specialize (H4 l g n0 H1 Heqx).
      rewrite <- H4.
      apply IHn.
      apply (propagate_not_WT l g n0); assumption.
    + apply (cons_congruence _ l (propagate_nots l n));
      apply IHn; assumption.
  (* u = CNOT *)
  - inversion WT; subst. 
    apply (cons_congruence _ l (propagate_nots l n)).
    apply IHn; assumption.
Qed.

(* rm_nots is semantics-preserving. 
   
   The well-typedness constraint is required because rm_nots can actually
   return a well-typed circuit given a circuit that is not well-typed.
     ==> Consider the program X 4; X 4 where dim = 3
   The output of the denotation function may change in this case. 
*)
Lemma rm_nots_sound : forall {dim} (l : gate_list dim), 
  uc_well_typed_l l -> l =l= rm_nots l.
Proof.
  intros dim l WT.
  unfold rm_nots.
  rewrite <- propagate_nots_sound.
  reflexivity.
  assumption.
Qed.


(*****************************************************************)
(** Optimization: rewrite w/ a single-qubit circuit equivalence **)
(*****************************************************************)

(* We restrict to single-qubit circuit equivalences for now because dealing
   with multi-qubit patterns is tedious with the list representation. For
   example, say that we are looking for the sub-circuit:
       C = [ H 0; H 2; CNOT 1 2; X 0 ]
   When searching for this sub-circuit, we need to keep in mind that these
   gates may be interspersed among other gates in the circuit in any order
   that respects dependence relationships. For example, the following program
   contains C, although it may not be obvious from casual inspection.
       [X 3; H 2; H 0; X 0; CNOT 0 3; CNOT 1 2]
*)

Definition single_qubit_pattern := list (fUnitary 1).

Fixpoint single_qubit_pattern_to_program {dim} (pat : single_qubit_pattern) q : gate_list dim :=
  match pat with
  | [] => []
  | u :: t => App1 u q :: (single_qubit_pattern_to_program t q)
  end. 

(* If the next sequence of gates applied to qubit q matches 'pat', then remove
   'pat' from the program. *)
Fixpoint remove_single_qubit_pattern {dim} (l : gate_list dim) (q : nat) (pat : single_qubit_pattern) : option (gate_list dim) :=
  match pat with
  | [] => Some l
  | u :: t =>
      match next_single_qubit_gate l q with
      | Some (u', l') =>
          if match_gate u u'
          then remove_single_qubit_pattern l' q t
          else None
      | _ => None
      end
  end.

(* If the next sequence of gates applied to qubit q matches 'pat', then replace
   'pat' with 'rep'. *)
Definition replace_single_qubit_pattern {dim} (l : gate_list dim) (q : nat) (pat rep : single_qubit_pattern) : option (gate_list dim) :=
  match (remove_single_qubit_pattern l q pat) with
  | Some l' => Some ((single_qubit_pattern_to_program rep q) ++ l')
  | None => None
  end.
     
(* Simple tests *)
Definition test : gate_list 4 := (_H 1) :: (_X 0) :: (_CNOT 2 3) :: (_Z 0) :: (_H 0) :: (_Z 1) :: (_Z 2) :: (_CNOT 0 2) :: [].
Compute (next_single_qubit_gate test 0).
Compute (next_single_qubit_gate test 1).
Compute (next_single_qubit_gate test 2).
Compute (next_two_qubit_gate test 2).
Compute (next_two_qubit_gate test 3).
Compute (next_single_qubit_gate test 4).
Compute (replace_single_qubit_pattern test 0 (fU_X :: fU_PI4 4 :: []) (fU_H :: fU_H :: [])).
Compute (replace_single_qubit_pattern test 0 (fU_X :: fU_H :: []) (fU_PI4 4:: fU_PI4 4 :: [])).

Lemma remove_single_qubit_pattern_correct : forall {dim} (l l' : gate_list dim) (q : nat) (pat : single_qubit_pattern),
  remove_single_qubit_pattern l q pat = Some l' ->
  l =l= (single_qubit_pattern_to_program pat q) ++ l'.
Proof.
  intros.
  generalize dependent l'.
  generalize dependent l.
  induction pat; intros.
  - inversion H; subst. reflexivity.
  - simpl in H. 
    remember (next_single_qubit_gate l q) as next_gate.
    symmetry in Heqnext_gate.
    destruct next_gate; try easy.
    destruct p. 
    remember (match_gate a f) as gate_match.
    destruct gate_match; try easy.
    symmetry in Heqgate_match.
    rewrite match_gate_refl in Heqgate_match; subst.
    simpl.
    rewrite <- (IHpat _ _ H). 
    apply (nsqg_preserves_semantics _ _ _ _ Heqnext_gate).
Qed.

Lemma remove_single_qubit_pattern_correct' : forall {dim} (l l' : gate_list dim) (q : nat) (pat : single_qubit_pattern),
  remove_single_qubit_pattern l q pat = Some l' ->
  l ≅l≅ ((single_qubit_pattern_to_program pat q) ++ l').
Proof.
  exists 0%R. rewrite eulers0. rewrite Mscale_1_l.
  intros.
  generalize dependent l'.
  generalize dependent l.
  induction pat; intros.
  - inversion H; subst. reflexivity.
  - simpl in H. 
    remember (next_single_qubit_gate l q) as next_gate.
    symmetry in Heqnext_gate.
    destruct next_gate; try easy.
    destruct p. 
    remember (match_gate a f) as gate_match.
    destruct gate_match; try easy.
    symmetry in Heqgate_match.
    rewrite match_gate_refl in Heqgate_match; subst.
    simpl.
    rewrite <- (IHpat _ _ H). 
    apply (nsqg_preserves_semantics _ _ _ _ Heqnext_gate).
Qed.

Lemma replace_single_qubit_pattern_sound : forall {dim} (l l' : gate_list dim) (q : nat) (pat rep : single_qubit_pattern),
  @uc_equiv_l dim (single_qubit_pattern_to_program pat q) (single_qubit_pattern_to_program rep q) ->
  replace_single_qubit_pattern l q pat rep = Some l' ->
  l =l= l'.
Proof.
  intros.
  unfold replace_single_qubit_pattern in H0.
  remember (remove_single_qubit_pattern l q pat) as remove_pat.
  destruct remove_pat; try easy.
  symmetry in Heqremove_pat.
  apply remove_single_qubit_pattern_correct in Heqremove_pat.
  inversion H0; subst.
  rewrite Heqremove_pat.
  rewrite H.
  reflexivity.
Qed.

Lemma replace_single_qubit_pattern_sound' : forall {dim} (l l' : gate_list dim) (q : nat) (pat rep : single_qubit_pattern),
  @uc_cong_l dim (single_qubit_pattern_to_program pat q) (single_qubit_pattern_to_program rep q) ->
  replace_single_qubit_pattern l q pat rep = Some l' ->
  l ≅l≅ l'.
Proof.
  intros.
  unfold replace_single_qubit_pattern in H0.
  remember (remove_single_qubit_pattern l q pat) as remove_pat.
  destruct remove_pat; try easy.
  symmetry in Heqremove_pat.
  apply remove_single_qubit_pattern_correct' in Heqremove_pat.
  inversion H0; subst.
  rewrite Heqremove_pat. rewrite H. reflexivity.
Qed.

(* TODO: We might also want to prove something along the lines of: the resulting
   program contains 'rep'. *)

(* Given a list of rewrite rules, try to apply each rule until one succeeds. 
   Return None if no rewrite succeeds. *)
Fixpoint try_rewrites {dim} l (rules : list (gate_list dim -> option (gate_list dim))) :=
  match rules with
  | [] => None
  | h :: t => match (h l) with
            | Some l' => Some l'
            | None => try_rewrites l t
            end
  end.

Lemma try_apply_rewrites_sound : forall {dim} (l l' : gate_list dim) rules,
  (forall r, In r rules -> (forall l l', r l = Some l' -> l =l= l')) ->
  try_rewrites l rules = Some l' ->
  l =l= l'.
Proof.
  intros.
  induction rules.
  - inversion H0.
  - simpl in H0.
    remember (a l) as al. 
    destruct al; inversion H0; subst.
    + symmetry in Heqal.
      assert (In a (a :: rules)) by (apply in_eq).
      apply (H a H1 l l' Heqal).
    + apply IHrules; try assumption.
      intros.
      apply (H r).
      apply in_cons; assumption.
      assumption.
Qed.

Lemma try_apply_rewrites_sound_cong : forall {dim} (l l' : gate_list dim) rules,
  (forall r, In r rules -> (forall l l', r l = Some l' -> l ≅l≅ l')) ->
  try_rewrites l rules = Some l' ->
  l ≅l≅ l'.
Proof.
  intros.
  induction rules.
  - inversion H0.
  - simpl in H0.
    remember (a l) as al. 
    destruct al; inversion H0; subst.
    + symmetry in Heqal.
      assert (In a (a :: rules)) by (apply in_eq).
      apply (H a H1 l l' Heqal).
    + apply IHrules; try assumption.
      intros.
      apply (H r).
      apply in_cons; assumption.
      assumption.
Qed.


(*******************************************)
(** Optimization: hadamard gate reduction **)
(*******************************************)

(** CURRENTLY NOT VERIFIED **)

(* This optimization pass reduces the number of H gates in a program
   using a variety of rewrite rules. *)

(* Hadamard Reduction Optimization
   
   Try to apply each the following equivalences to c. If one
   of the equivalences applies, then return the circuit resulting from
   the appropriate substitution.

   #1  - H q; P q; H q ≡ P† q; H q; P† q 
   #2  - H q; P† q; H q ≡ P q; H q; P q 
   #3a - H q1; H q2; CNOT q1 q2; H q1; H q1 ≡ CNOT q2 q1 
   #3b - H q2; H q1; CNOT q1 q2; H q1; H q2 ≡ CNOT q2 q1 
   #4  - H q2; P q2; CNOT q1 q2; P† q2; H q2 ≡ P† q2; CNOT q1 q2; P q2 
   #5  - H q2; P† q2; CNOT q1 q2; P q2; H q2 ≡ P q2; CNOT q1 q2; P† q2 
*)

Definition apply_H_equivalence1 {dim} q (l : gate_list dim) := 
  replace_single_qubit_pattern l q 
    (fU_H  :: fU_P :: fU_H :: []) 
    (fU_PDAG :: fU_H :: fU_PDAG :: []).

Definition apply_H_equivalence2 {dim} q (l : gate_list dim) := 
  replace_single_qubit_pattern l q 
    (fU_H :: fU_PDAG :: fU_H :: []) 
    (fU_P :: fU_H :: fU_P :: []).

Definition apply_H_equivalence3 {dim} q (l : gate_list dim) := 
  match (next_single_qubit_gate l q) with
  | Some (fU_H, l1) =>
      match (next_two_qubit_gate l1 q) with
      | Some (l2, m, n, l3) => 
          match (next_single_qubit_gate l3 q) with
          | Some (fU_H, l4) =>
              if (q =? m)
              (* case 3a *)
              then match (next_single_qubit_gate (rev l2) n) with
                   | Some (fU_H, l5) => 
                       match (next_single_qubit_gate l4 n) with
                       | Some (fU_H, l6) => 
                           Some ((rev l5) ++ [_CNOT n m] ++ l6)
                       | _ => None
                       end
                   | _ => None
                   end
              (* case 3b *)
              else match (next_single_qubit_gate (rev l2) m) with
                   | Some (fU_H, l5) => 
                       match (next_single_qubit_gate l4 m) with
                       | Some (fU_H, l6) => 
                           Some ((rev l5) ++ [_CNOT n m] ++ l6)
                       | _ => None
                       end
                   | _ => None
                   end
          | _ => None
          end
      | _ => None
      end
  | _ => None
  end.

Definition apply_H_equivalence4 {dim} q (l : gate_list dim) :=
  match (remove_single_qubit_pattern l q (fU_H :: fU_P :: [])) with
  | None => None
  | Some l1 =>
      match (next_two_qubit_gate l1 q) with
      | None => None
      | Some (l2, q1, q2, l3) =>
          if q =? q2 
          then match (remove_single_qubit_pattern l3 q (fU_PDAG :: fU_H :: [])) with
               | None => None
               | Some l4 =>
                   Some (l2 ++ (_PDAG q2 :: _CNOT q1 q2 :: _P q2 :: []) ++ l4)
               end
          else None
      end
  end.

Definition apply_H_equivalence5 {dim} q (l : gate_list dim) :=
  match (remove_single_qubit_pattern l q (fU_H :: fU_PDAG :: [])) with
  | Some l1 =>
      match (next_two_qubit_gate l1 q) with
      | Some (l2, q1, q2, l3) =>
          if q =? q2 
          then match (remove_single_qubit_pattern l3 q (fU_P :: fU_H :: [])) with
               | Some l4 =>
                   Some (l2 ++ (_P q2 :: _CNOT q1 q2 :: _PDAG q2 :: []) ++ l4)
               | _ => None
               end
          else None
      | _ => None
      end
  | _ => None
  end.

Definition apply_H_equivalence {dim} (l : gate_list dim) (q : nat) : option (gate_list dim) :=
  try_rewrites l ((apply_H_equivalence1 q) :: (apply_H_equivalence2 q) :: (apply_H_equivalence3 q) :: (apply_H_equivalence4 q) :: (apply_H_equivalence5 q) :: []).

(* For each H gate, try to apply a rewrite rule. If some rewrite rule
   succeeds, then make the recursive call on the circuit returned by
   apply_equivalence. 
 
   The n argument is needed to convince Coq of termination. We start with
   n = 2 * (length l), which is an overapproximation of the necessary
   number of iterations. Note that the starting value of n is greater than
   (length l) because apply_equivalence will sometimes return a program
   of the same size as the input program.

   If we wanted to do a proper proof of termination, we would need to show
   that each call to apply_H_equivalence (strictly) reduces the number of H 
   gates in the program. *)
Fixpoint apply_H_equivalences {dim} (l : gate_list dim) (n: nat) : gate_list dim :=
  match n with
  | 0 => l
  | S n' => 
      match l with
      | [] => []
      | (App1 fU_H q) :: t => 
          match apply_H_equivalence l q with
          | None => (_H q) :: (apply_H_equivalences t n')
          | Some l' => apply_H_equivalences l' n'
          end
      | g :: t => g :: (apply_H_equivalences t n')
      end
  end.

Definition hadamard_reduction {dim} (l : gate_list dim) : gate_list dim := 
  apply_H_equivalences l (2 * (length l)).


(* New C_field_simplify/nonzero that deal with Ci *)
Ltac nonzero :=
  repeat split;
   try match goal with
       | |- not (@eq _ ?x (RtoC (IZR Z0))) => apply RtoC_neq
       | |- not (@eq _ Ci (RtoC (IZR Z0))) => apply C0_snd_neq; simpl
       end;
   repeat
    match goal with
    | |- not (@eq _ (sqrt ?x) (IZR Z0)) => apply sqrt_neq_0_compat
    | |- not (@eq _ (Rinv ?x) (IZR Z0)) => apply Rinv_neq_0_compat
    end; match goal with
         | |- not (@eq _ _ _) => lra
         | |- Rlt _ _ => lra
         end.

Ltac C_field_simplify := repeat field_simplify_eq [ Csqrt2_sqrt Csqrt2_inv Ci2].

Lemma apply_H_equivalence1_sound : forall {dim} (l l' : gate_list dim) q,
  apply_H_equivalence1 q l = Some l' ->
  l ≅l≅ l'. 
Proof.
  intros.
  eapply replace_single_qubit_pattern_sound'.
  2 : { apply H. }
  exists (PI / 4)%R.
  unfold uc_eval, ueval1, pad; simpl.
  bdestruct (q + 1 <=? dim); try (remove_zero_gates; trivial).
  Msimpl. 
  restore_dims_strong; repeat rewrite kron_mixed_product.
  Msimpl.
  assert (hadamard × phase_shift (2 * PI / 4) × hadamard = (Cexp (PI / 4)%R) .* (phase_shift (6 * PI / 4) × hadamard  × phase_shift (6 * PI / 4))).
  { solve_matrix. 
    all: autorewrite with Cexp_db.
    all: C_field_simplify; try nonzero.
  }
  rewrite H1.
  repeat rewrite Mscale_mult_dist_l.
  repeat rewrite Mscale_kron_dist_r.  
  rewrite Mscale_kron_dist_l.
  reflexivity.
  rewrite Mscale_0_r.
  reflexivity.
Qed.

Lemma apply_H_equivalence2_sound : forall {dim} (l l' : gate_list dim) q,
  apply_H_equivalence2 q l = Some l' ->
  l ≅l≅ l'.
Proof. 
  intros.
  eapply replace_single_qubit_pattern_sound'; try apply H.
  exists (- PI / 4)%R.
  unfold uc_eval, ueval1, pad; simpl.
  bdestruct (q + 1 <=? dim); try (remove_zero_gates; trivial).
  - Msimpl.
    restore_dims_strong; repeat rewrite kron_mixed_product.
    Msimpl.
    assert (hadamard × phase_shift (6 * PI / 4) × hadamard = (Cexp (- PI / 4)%R) .* phase_shift (2 * PI / 4) × hadamard × phase_shift (2 * PI / 4)).
    { solve_matrix. 
      all: autorewrite with Cexp_db.
      all: C_field_simplify; try nonzero.
    }
    rewrite H1.
    repeat rewrite Mscale_mult_dist_l.
    repeat rewrite Mscale_kron_dist_r.
    rewrite Mscale_kron_dist_l.
    reflexivity.
  - rewrite Mscale_0_r. reflexivity.
Qed.

Lemma apply_H_equivalence3_sound : forall {dim} (l l' : gate_list dim) q,
  apply_H_equivalence3 q l = Some l' ->
  l ≅l≅ l'.
Proof.
Admitted.

Lemma apply_H_equivalence4_sound : forall {dim} (l l' : gate_list dim) q,
  apply_H_equivalence4 q l = Some l' ->
  l ≅l≅ l'.
Proof.
Admitted.

Lemma apply_H_equivalence5_sound : forall {dim} (l l' : gate_list dim) q,
  apply_H_equivalence5 q l = Some l' ->
  l ≅l≅ l'.
Proof.
Admitted.

Lemma apply_H_equivalence_sound : forall {dim} (l l' : gate_list dim) q,
  apply_H_equivalence l q = Some l' -> 
  l ≅l≅ l'.
Proof. 
  unfold apply_H_equivalence.
  intros dim l l' q.
  apply try_apply_rewrites_sound_cong.
  intros. 
  inversion H.
  subst; apply (apply_H_equivalence1_sound _ _ _ H0).
  inversion H1. 
  subst; apply (apply_H_equivalence2_sound _ _ _ H0). 
  inversion H2. 
  subst; apply (apply_H_equivalence3_sound _ _ _ H0). 
  inversion H3. 
  subst; apply (apply_H_equivalence4_sound _ _ _ H0). 
  inversion H4. 
  subst; apply (apply_H_equivalence5_sound _ _ _ H0). 
  inversion H5.
Qed.

Lemma apply_H_equivalences_sound: forall {dim} (l : gate_list dim) n, 
  l ≅l≅ apply_H_equivalences l n.
Proof. 
  intros.
  generalize dependent l.
  induction n; try easy.
  intros.
  destruct l; try easy.
  destruct g; simpl.
  - dependent destruction f;
    remember (apply_H_equivalence (App1 fU_H n0 :: l) n0) as res; symmetry in Heqres;
    destruct res;
    rewrite <- IHn;
    try apply (apply_H_equivalence_sound _ _ _ Heqres);
    reflexivity.
  - rewrite <- IHn; reflexivity.
Qed.

Lemma hadamard_reduction_sound: forall {dim} (l : gate_list dim), 
  l ≅l≅ hadamard_reduction l.
Proof. intros. apply apply_H_equivalences_sound. Qed.

(* TODO: We should also be able to prove that the Hadamard reduction optimization 
   reduces the number of Hadamard gates in the program. *)


(*******************************************************)
(** Optimization: simple cancellation and combination **)
(*******************************************************)

(* 'cancel_gates_simple' is my first pass at the full one- and two-qubit 
   gate cancellation routines. This function cancels unitaries adjacent to 
   their inverses and combines adjacent z-rotation gates. It does not
   consider any commutation relationships. 

   The extra n argument is to help Coq recognize termination.
   We start with n = (length l). *)

Fixpoint cancel_gates_simple' {dim} (l acc : gate_list dim) (n: nat) : gate_list dim :=
  match n with
  | 0 => (rev acc) ++ l
  | S n' => match l with
           | [] => rev acc
           | App1 fU_H q :: t => 
               match next_single_qubit_gate t q with
               | Some (fU_H, t') => cancel_gates_simple' t' acc n'
               | _ => cancel_gates_simple' t (_H q :: acc) n'
               end
           | App1 fU_X q :: t => 
               match next_single_qubit_gate t q with
               | Some (fU_X, t') => cancel_gates_simple' t' acc n'
               | _ => cancel_gates_simple' t (_X q :: acc) n'
               end
           | App1 (fU_PI4 k) q :: t => 
               match next_single_qubit_gate t q with
               | Some (fU_PI4 k', t') => 
                 let k'' := (k + k')%Z in
                 if (k'' =? 8)%Z then cancel_gates_simple' t' acc n' else 
                 if (k'' <? 8)%Z then cancel_gates_simple' (_PI4 k'' q :: t') acc n'
                 else cancel_gates_simple' (_PI4 (k'' - 8)%Z q :: t') acc n' 
               | _ => cancel_gates_simple' t (_PI4 k q :: acc) n'
               end
           | App2 fU_CNOT q1 q2 :: t => 
               match next_two_qubit_gate t q1 with
               | Some (l1, q1', q2', l2) => 
                   if (q1 =? q1') && (q2 =? q2') && (does_not_reference l1 q2)
                   then cancel_gates_simple' (l1 ++ l2) acc n'
                   else cancel_gates_simple' t (_CNOT q1 q2 :: acc) n'
               | _ => cancel_gates_simple' t (_CNOT q1 q2 :: acc) n'
               end
           | _ => [] (* impossible case for well-formed gate_list *)
           end
  end.

Definition cancel_gates_simple {dim} (l : gate_list dim) : gate_list dim := 
  cancel_gates_simple' l [] (List.length l).


(* Useful identities. *)
   
(* TODO: These proofs are all just copied & pasted from each other, so
   there is definitely some cleaning that needs to be done. Once they're
   cleaned up, they should be moved to Equivalences.v *)

Lemma H_H_cancel : forall {dim} (l : gate_list dim) q, 
  q < dim -> _H q :: _H q :: l =l= l.
Proof.
  intros.
  unfold uc_equiv_l, uc_equiv; simpl.
  unfold ueval1, pad; simpl.
  bdestruct (q + 1 <=? dim); try lia.
  rewrite Mmult_assoc.
  restore_dims_strong; repeat rewrite kron_mixed_product.
  Msimpl.
  replace (hadamard × hadamard) with (I (2 ^ 1)) by solve_matrix.
  Msimpl.
  unify_pows_two.
  replace (q + 1 + (dim - 1 - q)) with dim by lia.
  apply Mmult_1_r; auto with wf_db.
Qed.

Lemma X_X_cancel : forall {dim} (l : gate_list dim) q, 
  q < dim -> _X q :: _X q :: l =l= l.
Proof.
  intros.
  unfold uc_equiv_l, uc_equiv; simpl.
  unfold ueval1, pad; simpl.
  bdestruct (q + 1 <=? dim); try lia.
  rewrite Mmult_assoc.
  restore_dims_strong; repeat rewrite kron_mixed_product.
  Msimpl.
  replace (σx × σx) with (I (2 ^ 1)) by solve_matrix.
  Msimpl.
  unify_pows_two.
  replace (q + 1 + (dim - 1 - q)) with dim by lia.
  apply Mmult_1_r; auto with wf_db.
Qed.

Lemma PI4_PI4_combine : forall {dim} (l : gate_list dim) q k k', 
  _PI4 k q :: _PI4 k' q :: l =l= _PI4 (k+k') q :: l.
Proof.
  intros.
  unfold uc_equiv_l, uc_equiv; simpl.
  unfold ueval1, pad; simpl.
  bdestruct (q + 1 <=? dim); try (remove_zero_gates; trivial).
  rewrite Mmult_assoc.
  restore_dims_strong; repeat rewrite kron_mixed_product.
  Msimpl.
  rewrite phase_mul. 
  repeat rewrite <- Rmult_div_assoc.
  rewrite <- Rmult_plus_distr_r.
  rewrite plus_IZR.
  rewrite Rplus_comm.
  reflexivity.
Qed.

Lemma PI4_PI4_m8_combine : forall {dim} (l : gate_list dim) q k k', 
  _PI4 k q :: _PI4 k' q :: l =l= _PI4 (k+k'-8) q :: l.
Proof.
  intros.
  unfold uc_equiv_l, uc_equiv; simpl.
  unfold ueval1, pad; simpl.
  bdestruct (q + 1 <=? dim); try (remove_zero_gates; trivial).
  rewrite Mmult_assoc.
  restore_dims_strong; repeat rewrite kron_mixed_product.
  Msimpl.
  rewrite phase_mul. 
  repeat rewrite <- Rmult_div_assoc.
  rewrite <- Rmult_plus_distr_r.
  rewrite <- plus_IZR.
  repeat rewrite Rmult_div_assoc.
  rewrite phase_PI4_m8.
  rewrite Zplus_comm.
  reflexivity.
Qed.
  
Lemma PI4_PI4_cancel : forall {dim} (l : gate_list dim) q k k', 
  q < dim -> 
  (k + k' = 8)%Z ->
  _PI4 k q :: _PI4 k' q :: l =l= l.
Proof.
  intros.
  unfold uc_equiv_l, uc_equiv; simpl.
  unfold ueval1, pad; simpl.
  bdestructΩ (q + 1 <=? dim); try (remove_zero_gates; trivial).
  rewrite Mmult_assoc.
  restore_dims_strong; repeat rewrite kron_mixed_product.
  Msimpl.
  rewrite phase_mul. 
  repeat rewrite <- Rmult_div_assoc.
  rewrite <- Rmult_plus_distr_r.
  rewrite <- plus_IZR.
  repeat rewrite Rmult_div_assoc.
  rewrite Zplus_comm.
  rewrite H0.
  replace (8 * PI / 4)%R with (2 * PI)%R by lra.
  rewrite phase_2pi.
  Msimpl. replace (2 ^ q * 2 * 2 ^ (dim - 1 - q))%nat with (2^dim) by unify_pows_two.
  Msimpl.
  reflexivity.
Qed.

Lemma PI4_0_rem : forall {dim} (l : gate_list dim) q, 
  q < dim -> _PI4 0 q :: l =l= l.
Proof.
  intros.
  unfold uc_equiv_l, uc_equiv; simpl.
  unfold ueval1, pad; simpl.
  bdestructΩ (q + 1 <=? dim); try (remove_zero_gates; trivial).
  unfold Rdiv. repeat rewrite Rmult_0_l. 
  rewrite phase_0.
  Msimpl. replace (2 ^ q * 2 * 2 ^ (dim - 1 - q))%nat with (2^dim) by unify_pows_two.
  Msimpl.
  reflexivity.
Qed.

  
Lemma CNOT_CNOT_cancel : forall {dim} (l1 l2 : gate_list dim) q1 q2, 
  q1 < dim -> q2 < dim -> q1 <> q2 -> l1 ++ [_CNOT q1 q2] ++ [_CNOT q1 q2] ++ l2 =l= l1 ++ l2.
Proof.
  intros.
  unfold uc_equiv_l, uc_equiv; simpl.
  rewrite list_to_ucom_append; simpl.
  unfold ueval_cnot, pad; simpl.
  bdestruct (q3 <? q4).
  - bdestruct (q3 + S (q4 - q3 - 1 + 1) <=? dim); try lia.
    replace (2 ^ (q4 - q3)) with (2 ^ (q4 - q3 - 1) * 2) by unify_pows_two.
    repeat rewrite <- id_kron.
    repeat rewrite <- kron_assoc.
    rewrite (Mmult_assoc (uc_eval (list_to_ucom l2))). 
    restore_dims_strong; repeat rewrite kron_mixed_product.
    Msimpl.
    rewrite Mmult_plus_distr_r. 
    repeat rewrite Mmult_plus_distr_l.
    restore_dims_strong; repeat rewrite kron_mixed_product.
    Msimpl.
    replace (∣1⟩⟨1∣ × ∣1⟩⟨1∣) with (∣1⟩⟨1∣) by solve_matrix.
    replace (∣1⟩⟨1∣ × ∣0⟩⟨0∣) with (@Zero 2 2) by solve_matrix.
    replace (∣0⟩⟨0∣ × ∣1⟩⟨1∣) with (@Zero 2 2) by solve_matrix.
    replace (∣0⟩⟨0∣ × ∣0⟩⟨0∣) with (∣0⟩⟨0∣) by solve_matrix.
    remove_zero_gates.
    rewrite Mplus_0_l. 
    rewrite Mplus_0_r.
    replace (σx × σx) with (I 2) by solve_matrix.
    repeat rewrite kron_assoc.
    repeat rewrite id_kron.
    unify_pows_two.
    replace (2 ^ (q4 - q3 - 1 + 1 + 1)) with (2 * 2 ^ (q4 - q3 - 1 + 1)) by unify_pows_two.
    rewrite <- kron_plus_distr_r.
    replace (∣1⟩⟨1∣ .+ ∣0⟩⟨0∣) with (I 2) by solve_matrix.
    Msimpl.
    restore_dims_strong.
    Msimpl.
    replace (2 ^ q3 * (2 * 2 ^ (q4 - q3 - 1 + 1) * 2 ^ (dim - S (q4 - q3 - 1 + 1) - q3))) with (2 ^ dim) by unify_pows_two.
    rewrite Mmult_1_r; auto with wf_db.
    rewrite list_to_ucom_append; reflexivity.
  - bdestruct (q4 <? q3); try lia.
    bdestruct (q4 + S (q3 - q4 - 1 + 1) <=? dim); try lia.
    replace (2 ^ (q3 - q4)) with (2 * 2 ^ (q3 - q4 - 1)) by unify_pows_two.
    repeat rewrite <- id_kron.
    repeat rewrite <- kron_assoc.
    rewrite (Mmult_assoc (uc_eval (list_to_ucom l2))). 
    restore_dims_strong; repeat rewrite kron_mixed_product.
    Msimpl.
    rewrite Mmult_plus_distr_r. 
    repeat rewrite Mmult_plus_distr_l.
    restore_dims_strong; repeat rewrite kron_mixed_product.
    Msimpl.
    replace (∣1⟩⟨1∣ × ∣1⟩⟨1∣) with (∣1⟩⟨1∣) by solve_matrix.
    replace (∣1⟩⟨1∣ × ∣0⟩⟨0∣) with (@Zero 2 2) by solve_matrix.
    replace (∣0⟩⟨0∣ × ∣1⟩⟨1∣) with (@Zero 2 2) by solve_matrix.
    replace (∣0⟩⟨0∣ × ∣0⟩⟨0∣) with (∣0⟩⟨0∣) by solve_matrix.
    remove_zero_gates.
    rewrite Mplus_0_l. 
    rewrite Mplus_0_r.
    replace (σx × σx) with (I 2) by solve_matrix.
    repeat rewrite id_kron.
    unify_pows_two.
    replace (2 ^ (q3 - q4 - 1 + 1 + 1)) with (2 ^ (S (q3 - q4 - 1)) * 2) by unify_pows_two.
    rewrite <- kron_plus_distr_l.
    replace (∣1⟩⟨1∣ .+ ∣0⟩⟨0∣) with (I 2) by solve_matrix.
    Msimpl.
    restore_dims_strong.
    Msimpl.
    replace (2 ^ q4 * (2 ^ S (q3 - q4 - 1) * 2) * 2 ^ (dim - S (q3 - q4 - 1 + 1) - q4)) with (2 ^ dim) by unify_pows_two.
    rewrite Mmult_1_r; auto with wf_db.
    rewrite list_to_ucom_append; reflexivity.
Qed.

Lemma cancel_gates_simple'_sound : forall {dim} (l acc : gate_list dim) n,
  uc_well_typed_l l -> (rev acc) ++ l =l= cancel_gates_simple' l acc n.
Proof.
  intros.
  generalize dependent acc.
  generalize dependent l.
  induction n; try easy.
  intros l WT; simpl.
  destruct l; intros; try (rewrite app_nil_r; reflexivity).
  destruct g.
  - dependent destruction f;
    remember (next_single_qubit_gate l n0) as next_gate;
    symmetry in Heqnext_gate; inversion WT.
    + (* H *)
      destruct next_gate.
      2: { rewrite <- IHn; try assumption.
           simpl; rewrite <- app_assoc. 
           reflexivity. }
      destruct p; dependent destruction f; rewrite <- IHn;
      try (simpl; rewrite <- app_assoc; reflexivity);
      try assumption.
      rewrite (nsqg_preserves_semantics _ _ _ _ Heqnext_gate).
      apply app_congruence; try reflexivity.
      apply H_H_cancel; assumption.
      apply (nsqg_WT _ _ _ _ Heqnext_gate H3).
    + (* X *)
      destruct next_gate.
      2: { rewrite <- IHn; try assumption.
           simpl; rewrite <- app_assoc. 
           reflexivity. }
      destruct p; dependent destruction f; rewrite <- IHn;
      try (simpl; rewrite <- app_assoc; reflexivity);
      try assumption.
      rewrite (nsqg_preserves_semantics _ _ _ _ Heqnext_gate).
      apply app_congruence; try reflexivity.
      apply X_X_cancel; assumption.
      apply (nsqg_WT _ _ _ _ Heqnext_gate H3).
    + (* PI4 *)
      destruct next_gate.
      2: { rewrite <- IHn; try assumption.
           simpl; rewrite <- app_assoc. 
           reflexivity. }
      destruct p; dependent destruction f;
      [| | destruct (k + k0 =? 8)%Z eqn:E; [|destruct (k + k0 <? 8)%Z]];
      try rewrite <- IHn;
      try rewrite (nsqg_preserves_semantics _ _ _ _ Heqnext_gate);
      try (simpl; rewrite <- app_assoc; reflexivity);
      try constructor;
      try apply (nsqg_WT _ _ _ _ Heqnext_gate);
      try assumption;
      try apply app_congruence; try reflexivity.
      apply Z.eqb_eq in E.
      apply PI4_PI4_cancel; lia.
      apply PI4_PI4_combine.
      apply PI4_PI4_m8_combine.
  - (* CNOT *)
    dependent destruction f.
    remember (next_two_qubit_gate l n0) as next_gate;
    symmetry in Heqnext_gate; 
    inversion WT.
    destruct next_gate.
    2: { rewrite <- IHn; try assumption.
         simpl; rewrite <- app_assoc. 
         reflexivity. }
    destruct p; destruct p; destruct p.
    bdestruct (n0 =? n4); bdestruct (n1 =? n3); simpl;
    try (rewrite <- IHn; try assumption; simpl; rewrite <- app_assoc; reflexivity).
    subst.
    remember (does_not_reference g0 n3) as dnr; symmetry in Heqdnr.
    destruct dnr; simpl; 
    try (rewrite <- IHn; try assumption; simpl; rewrite <- app_assoc; reflexivity).
    specialize (ntqg_preserves_semantics _ _ _ _ _ _ Heqnext_gate) as H7.
    rewrite H7.
    rewrite <- IHn.
    specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ Heqnext_gate) as H8.
    rewrite app_comm_cons.
    rewrite app_assoc.
    rewrite (does_not_reference_commutes_app2 g0 fU_CNOT n4 n3 H8 Heqdnr).
    repeat rewrite <- app_assoc.
    apply app_congruence; try reflexivity.
    apply CNOT_CNOT_cancel; assumption.
    specialize (ntqg_WT _ _ _ _ _ _ Heqnext_gate H6) as [H8 H9].
    apply uc_well_typed_l_app; assumption.
Qed.

Lemma cancel_gates_simple_sound : forall {dim} (l : gate_list dim),
  uc_well_typed_l l -> l =l= cancel_gates_simple l.
Proof. 
  intros. 
  unfold cancel_gates_simple.
  rewrite <- cancel_gates_simple'_sound.
  reflexivity. 
  assumption. 
Qed.

(* Small test *)
Definition test1 : gate_list 4 := (_H 1) :: (_P 0) :: (_CNOT 2 3) :: (_P 0) :: (_H 1) :: (_Z 1) :: (_PDAG 0) :: (_CNOT 2 3) :: (_T 0) :: [].
Compute (cancel_gates_simple test1).

(**********************************************************************)
(** Optimization: simple cancellation and combination w/ commutation **)
(**********************************************************************)

(* Cancel and combine gates, as above, but also check for cancellations
   across commuting subcircuits. We will determine whether a gate
   commutes through a subcircuit using the following circuits identities
   from Nam et al.

   - X b; CNOT a b ≡ CNOT a b; X b
   - Rz b ; H b ; CNOT a b ; H b ≡ H b ; CNOT a b ; H b ; Rz b
   - Rz b ; CNOT a b ; Rz' b ; CNOT a b ≡ CNOT a b ; Rz' b ; CNOT a b ; Rz b
   - Rz a ; CNOT a b ≡ CNOT a b ; Rz a

   Not currently verified:
   - CNOT a c ; CNOT b c ≡ CNOT b c ; CNOT a c
   - CNOT a c ; CNOT a b ≡ CNOT a b ; CNOT a c
   - CNOT a b; H b; CNOT b c; H b ≡ H b; CNOT b c; H b; CNOT a b

   This optimization is similar to Nam et al.'s single/two-qubit gate
   cancellation and not propagation.
*)

(* Commutativity rule for X *)

Definition search_for_commuting_X_pat {dim} (l : gate_list dim) q :=
  match next_two_qubit_gate l q with
  | Some (l1, q1, q2, l2) =>
      if q =? q2
      then Some (l1 ++ [_CNOT q1 q2], l2)
      else None
  | _ => None
  end.

(* Commutativity rules for Rz *)

Definition search_for_Rz_pat1 {dim} (l : gate_list dim) q :=
  match (next_single_qubit_gate l q) with
  | Some (fU_H, l') => 
      match (next_two_qubit_gate l' q) with
      | Some (l1, q1, q2, l2) =>
          if q =? q2
          then match (next_single_qubit_gate l2 q) with
               | Some (fU_H, l2') => Some ([_H q] ++ l1 ++ [_CNOT q1 q] ++ [ _H q], l2') 
               | _ => None
               end
          else None
      | _ => None
      end
  | _ => None
  end.

Definition search_for_Rz_pat2 {dim} (l : gate_list dim) q :=
  match (next_two_qubit_gate l q) with
  | Some (l1, q1, q2, l2) => 
      if q =? q2
      then match (next_single_qubit_gate l2 q) with
           | Some (fU_PI4 k as u, l2') =>
               match (next_two_qubit_gate l2' q) with
               | Some (l3, q3, q4, l4) => 
                   if (q =? q4) && (q1 =? q3) && (does_not_reference l3 q3)
                   then Some (l1 ++ [_CNOT q1 q] ++ [App1 u q] ++ l3 ++ [_CNOT q1 q], l4)
                   else None 
               | _ => None
               end
           | _ => None
           end
      else None
  | _ => None
  end.

Definition search_for_Rz_pat3 {dim} (l : gate_list dim) q :=
  match (next_two_qubit_gate l q) with
  | Some (l1, q1, q2, l2) => 
      if q =? q1
      then Some (l1 ++ [_CNOT q1 q2], l2)
      else None
  | _ => None
  end.

Definition search_for_commuting_Rz_pat {dim} (l : gate_list dim) q :=
  match search_for_Rz_pat1 l q with
  | Some (l1, l2) => Some (l1, l2)
  | None => match search_for_Rz_pat2 l q with
           | Some (l1, l2) => Some (l1, l2)
           | None => match search_for_Rz_pat3 l q with
                    | Some (l1, l2) => Some (l1, l2)
                    | None => None
                    end
           end
  end.

(* Commutativity rules for CNOT *)

Definition search_for_CNOT_pat1 {dim} (l : gate_list dim) (q1 q2 : nat) : option (gate_list dim * gate_list dim) :=
  match (next_single_qubit_gate l q1) with
  | Some (fU_PI4 k, l') => Some ([_PI4 k q1], l')
  | _ => None
  end.

Definition search_for_CNOT_pat2 {dim} (l : gate_list dim) q1 q2 :=
  match (next_two_qubit_gate l q2) with
  | Some (l1, q1', q2', l2) => 
      if q2 =? q2'
      then if (does_not_reference l1 q1) && (does_not_reference l1 q1')
           then Some (l1 ++ [_CNOT q1' q2], l2)
           else None
      else None
  | _ => None
  end.

Definition search_for_CNOT_pat3 {dim} (l : gate_list dim) q1 q2 :=
  match (next_two_qubit_gate l q1) with
  | Some (l1, q1', q2', l2) => 
      if q1 =? q1'
      then if (does_not_reference l1 q2) && (does_not_reference l1 q2')
           then Some (l1 ++ [_CNOT q1 q2'], l2)
           else None
      else None
  | _ => None
  end.

Definition search_for_CNOT_pat4 {dim} (l : gate_list dim) q1 q2 :=
  match (next_single_qubit_gate l q2) with
  | Some (fU_H, l') => 
      match (next_two_qubit_gate l' q2) with
      | Some (l1, q1', q2', l2) => 
          if (q2 =? q1') && (does_not_reference l1 q1)
          then match (next_single_qubit_gate l2 q2) with
               | Some (fU_H, l2') => Some ([_H q2] ++ l1 ++ [_CNOT q2 q2'] ++ [_H q2], l2')
               | _ => None
               end
          else None
      | _ => None
      end
  | _ => None
  end.

Definition search_for_commuting_CNOT_pat {dim} (l : gate_list dim) q1 q2 :=
  match search_for_CNOT_pat1 l q1 q2 with
  | Some (l1, l2) => Some (l1, l2)
  | None => match search_for_CNOT_pat2 l q1 q2 with
           | Some (l1, l2) => Some (l1, l2)
           | None => match search_for_CNOT_pat3 l q1 q2 with
                    | Some (l1, l2) => Some (l1, l2)
                    | None =>  match search_for_CNOT_pat4 l q1 q2 with
                              | Some (l1, l2) => Some (l1, l2)
                              | None => None
                              end
                    end
           end
  end.

(* Propagation functions for each gate type *)

Fixpoint propagate_PI4 {dim} k (l : gate_list dim) (q n : nat) : option (gate_list dim) :=
  match n with
  | O => None
  | S n' => 
      match next_single_qubit_gate l q with
      | Some (fU_PI4 k', l') => 
                 let k'' := (k + k')%Z in
                 (* Cancel *)
                 if (k'' =? 8)%Z then Some l' else 
                 (* Combine *)
                 if (k'' <? 8)%Z then Some (_PI4 k'' q :: l')
                 else Some (_PI4 (k'' - 8)%Z q :: l') 
      (* Commute *)
      | _ =>
          match search_for_commuting_Rz_pat l q with
          | Some (l1, l2) => match (propagate_PI4 k l2 q n') with
                            | Some l' => Some (l1 ++ l')
                            | None => None
                            end
          | None =>  None
          end
      end
  end.

Definition propagate_H {dim} (l : gate_list dim) (q : nat) : option (gate_list dim) :=
  match next_single_qubit_gate l q with
  (* Cancel *)
  | Some (fU_H, l') => Some l'
  (* Currently no rules for commuting H gates *)
  | _ => None
  end.

Fixpoint propagate_X {dim} (l : gate_list dim) (q n : nat) : option (gate_list dim) :=
  match n with
  | O => None
  | S n' => 
      match next_single_qubit_gate l q with
      (* Cancel *)
      | Some (fU_X, l') => Some l'
      (* Commute *)
      | _ =>
          match search_for_commuting_X_pat l q with
          | Some (l1, l2) => match (propagate_X l2 q n') with
                            | Some l' => Some (l1 ++ l')
                            | None => None
                            end
          | None =>  None
          end
      end
  end.

Definition propagate_CNOT {dim} (l : gate_list dim) (q1 q2 n : nat) : option (gate_list dim) :=
  match n with
  | O => None
  | S n' => 
      match next_two_qubit_gate l q1 with
      (* Cancel *)
      | Some (l1, q1', q2', l2) => 
          if (q1 =? q1') && (q2 =? q2') && (does_not_reference l1 q2)
          then Some (l1 ++ l2)
          else None
      (* Commute -- commented out to avoid unverified code *)
      (*| _ =>
          match search_for_commuting_CNOT_pat l q1 q2 with
          | Some (l1, l2) => match (propagate_CNOT l2 q1 q2 n') with
                            | Some l' => Some (l1 ++ l')
                            | None => None
                            end
          | None =>  None
          end
      end*)
      | _ => None
      end
  end.

Fixpoint cancel_gates' {dim} (l : gate_list dim) (n: nat) : gate_list dim :=
  match n with
  | 0 => l
  | S n' => match l with
           | App1 (fU_PI4 k) q :: t => 
               match propagate_PI4 k t q (length t) with
               | None => (_PI4 k q) :: (cancel_gates' t n')
               | Some l' => cancel_gates' l' n'
               end
           | App1 fU_H q :: t => 
               match propagate_H t q with
               | None => (_H q) :: (cancel_gates' t n')
               | Some l' => cancel_gates' l' n'
               end
           | App1 fU_X q :: t => 
               match propagate_X t q (length t) with
               | None => (_X q) :: (cancel_gates' t n')
               | Some l' => cancel_gates' l' n'
               end
           | App2 fU_CNOT q1 q2 :: t => 
               match propagate_CNOT t q1 q2 (length t) with
               | None => (_CNOT q1 q2) :: (cancel_gates' t n')
               | Some l' => cancel_gates' l' n'
               end
           | _ => []
           end
  end.

Definition cancel_gates {dim} (l : gate_list dim) := 
  cancel_gates' l (length l).


(* Proofs about commutativity *)

Lemma commuting_X_pat : forall {dim} (l : gate_list dim) q l1 l2, 
  search_for_commuting_X_pat l q = Some (l1, l2) ->
  _X q :: l =l= l1 ++ [_X q] ++ l2.
Proof.
  intros.
  unfold search_for_commuting_X_pat in H.
  remember (next_two_qubit_gate l q) as next_gate; symmetry in Heqnext_gate.
  destruct next_gate; try easy.
  do 3 destruct p.
  bdestruct (q =? n); try easy.
  inversion H; subst.
  rewrite (ntqg_preserves_semantics _ _ _ _ _ _ Heqnext_gate).
  assert (does_not_reference g0 n = true).
  { apply (ntqg_l1_does_not_reference _ _ _ _ _ _ Heqnext_gate). }
  rewrite app_comm_cons.
  rewrite (does_not_reference_commutes_app1 _ fU_X _ H0).
  repeat rewrite <- app_assoc.
  rewrite (app_assoc _ _ l2).
  rewrite (app_assoc _ [_X n] l2).
  assert (@uc_equiv_l dim ([_X n] ++ [_CNOT n0 n]) ([_CNOT n0 n] ++ [_X n])).
  { unfold uc_equiv_l; simpl.
    do 2 rewrite uskip_id_r.
    apply X_CNOT_comm. }
  rewrite H1.
  reflexivity.  
Qed.

Lemma f_equal_gen : forall {A B} (f g : A -> B) a b, f = g -> a = b -> f a = g b.
Proof. intros. subst. reflexivity. Qed.

Ltac is_nat_equality :=
  match goal with 
  | |- ?A = ?B => match type of A with
                | nat => idtac
                end
  end.

Ltac unify_matrices_light := 
  repeat (apply f_equal_gen; trivial; try (is_nat_equality; lia)).


Ltac restore_dims_rec A :=
   match A with
  | ?A × ?B   => let A' := restore_dims_rec A in 
                let B' := restore_dims_rec B in 
                match type of A' with 
                | Matrix ?m' ?n' =>
                  match type of B' with 
                  | Matrix ?n'' ?o' => constr:(@Mmult m' n' o' A' B')
                  end
                end 
  | ?A ⊗ ?B   => let A' := restore_dims_rec A in 
                let B' := restore_dims_rec B in 
                match type of A' with 
                | Matrix ?m' ?n' =>
                  match type of B' with 
                  | Matrix ?o' ?p' => constr:(@kron m' n' o' p' A' B')
                  end
                end
  | ?A †      => let A' := restore_dims_rec A in 
                match type of A' with
                | Matrix ?m' ?n' => constr:(@adjoint m' n' A')
                end
  | ?A .+ ?B => let A' := restore_dims_rec A in 
               let B' := restore_dims_rec B in 
               match type of A' with 
               | Matrix ?m' ?n' =>
                 match type of B' with 
                 | Matrix ?m'' ?n'' => constr:(@Mplus m' n' A' B')
                 end
               end
  | ?c .* ?A => let A' := restore_dims_rec A in 
               match type of A' with
               | Matrix ?m' ?n' => constr:(@scale m' n' c A')
               end
  | ?A       => A
   end.

Ltac restore_dims_fast := 
  match goal with
  | |- ?A = ?B => let A' := restore_dims_rec A in 
                let B' := restore_dims_rec B in 
                replace A with A' by unify_matrices_light; 
                replace B with B' by unify_matrices_light
  end.

Ltac distribute_plus :=
  repeat match goal with 
  | |- context [?a × (?b .+ ?c)] => rewrite (Mmult_plus_distr_l _ _ _ a b c)
  | |- context [(?a .+ ?b) × ?c] => rewrite (Mmult_plus_distr_r _ _ _ a b c)
  | |- context [?a ⊗ (?b .+ ?c)] => rewrite (kron_plus_distr_l _ _ _ _ a b c)
  | |- context [(?a .+ ?b) ⊗ ?c] => rewrite (kron_plus_distr_r _ _ _ _ a b c)
  end.


Lemma app_cons_app : forall {A} (a : A) (l1 l2 : list A), a :: l1 ++ l2 = [a] ++ l1 ++ l2.
Proof. reflexivity. Qed.


Lemma commuting_Rz_pat : forall {dim} k (l : gate_list dim) q l1 l2,
  search_for_commuting_Rz_pat l q = Some (l1, l2) ->
  _PI4 k q :: l =l= l1 ++ [_PI4 k q] ++ l2.
Proof.
(* Will require lemmas about search_for_Rz_pat1, 2, and 3. *)
  intros.
  unfold search_for_commuting_Rz_pat in H.
  destruct (search_for_Rz_pat1 l q) eqn:HS; 
  [|destruct (search_for_Rz_pat2 l q) eqn:HS2;
  [|destruct (search_for_Rz_pat3 l q) eqn:HS3]]; try discriminate.
  - unfold search_for_Rz_pat1 in HS.
    destruct p.
    inversion H; subst. clear H.
    destruct (next_single_qubit_gate l q) eqn:HN1; try discriminate.
    destruct p.
    apply nsqg_preserves_semantics in HN1.
    destruct (next_two_qubit_gate g q) eqn:HN2; try discriminate.
    2:{ dependent destruction f; discriminate. }
    repeat destruct p.
    specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ HN2) as NoRef.
    apply ntqg_preserves_semantics in HN2.
    dependent destruction f; try discriminate.
    bdestruct (q =? n); try easy.
    destruct (next_single_qubit_gate g0 q) eqn:HN1'; try discriminate.
    destruct p.
    apply nsqg_preserves_semantics in HN1'.
    dependent destruction f; try discriminate.
    inversion HS; subst.
    rewrite HN1, HN2, HN1'.
    rewrite app_comm_cons.
    rewrite (does_not_reference_commutes_app1 _ fU_H _ NoRef).
    repeat rewrite <- app_assoc.
    rewrite 2 app_comm_cons.
    rewrite (does_not_reference_commutes_app1 _ (fU_PI4 k) _ NoRef).
    rewrite (does_not_reference_commutes_app1 _ fU_H _ NoRef).    
    repeat rewrite <- app_assoc.
    apply app_congruence; try reflexivity.
    replace ( App1 fU_H n :: l2) with ([App1 fU_H n] ++ l2) by easy.
    repeat rewrite app_assoc.
    apply app_congruence; try reflexivity.
    unfold uc_equiv_l; simpl.
    unfold uc_equiv; simpl. unfold ueval1, ueval_cnot.
    bdestruct (n0 <? n).
    + unfold pad.
      bdestructΩ (n + 1 <=? dim).
      bdestructΩ (n0 + S (n - n0 - 1 + 1) <=? dim).
      remember (n - n0 - 1) as m.
      remember (dim - 1 - n) as p.
      replace (n - n0) with (m + 1) by lia.
      replace (dim - S (m + 1) - n0) with p by lia.
      replace dim with (n + 1 + p) by lia.
      replace n with (n0 + 1 + m) by lia.
      clear. rename n0 into n.
      repeat rewrite Nat.pow_add_r.
      Msimpl.
      repeat rewrite <- id_kron. simpl (2^1).
      remember (2^n) as a. remember (2^m) as b. remember (2^p) as c. clear.
      restore_dims_fast.
      repeat rewrite mult_assoc.
      repeat rewrite kron_mixed_product.
      repeat rewrite <- kron_assoc.
      repeat rewrite Mmult_1_l; auto with wf_db.
      distribute_plus.
      repeat rewrite <- kron_assoc.
      restore_dims_fast.
      repeat rewrite kron_mixed_product.
      Msimpl.
      apply f_equal2.
      replace (hadamard × σx × hadamard) with σz by solve_matrix.
      repeat rewrite Mmult_assoc.
      replace (hadamard × (σx × hadamard)) with σz by solve_matrix.
      rewrite <- phase_pi, 2 phase_mul.
      replace (PI + IZR k * PI / 4)%R with (IZR k * PI / 4 + PI)%R by lra.
      reflexivity.
      Search hadamard.
      rewrite (Mmult_assoc _ _ hadamard).
      replace (hadamard × hadamard) with (I 2) by solve_matrix.
      Msimpl.
      reflexivity.
      restore_dims_fast.
      remove_zero_gates; easy.
    + unfold pad.
      bdestructΩ (n + 1 <=? dim).
      bdestructΩ (n <? n0).
      bdestructΩ (n + S (n0 - n - 1 + 1) <=? dim).
      all: remove_zero_gates; try easy.      
      remember (n0 - n - 1) as x.
      replace (n0 - n) with (1 + x) by lia.
      remember (dim - S (x + 1) - n) as y.      
      replace dim with (n + 1 + x + 1 + y) by lia.
      replace ((n + 1 + x + 1 + y - 1 - n)) with (x + 1 + y) by lia.
      clear. 
      repeat rewrite Nat.pow_add_r.
      simpl (2^1).
      remember (2^n) as a. remember (2^x) as b. remember (2^y) as c. clear.
      restore_dims_fast.
      repeat rewrite <- id_kron.
      restore_dims_fast.
      distribute_plus.
      repeat rewrite kron_assoc.
      restore_dims_fast.
      repeat rewrite kron_mixed_product.
      Msimpl.
      apply f_equal2.
      replace (hadamard × σx × hadamard) with σz by solve_matrix.
      repeat rewrite Mmult_assoc.
      replace (hadamard × (σx × hadamard)) with σz by solve_matrix.
      rewrite <- phase_pi, 2 phase_mul.
      replace (PI + IZR k * PI / 4)%R with (IZR k * PI / 4 + PI)%R by lra.
      reflexivity.
      rewrite (Mmult_assoc _ _ hadamard).
      replace (hadamard × hadamard) with (I 2) by solve_matrix.
      Msimpl.
      reflexivity.
  - unfold search_for_Rz_pat2 in HS2.
    destruct p.
    inversion H; subst. clear H HS.
    destruct (next_two_qubit_gate l q) eqn:HN2; try discriminate.
    repeat destruct p.
    specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ HN2) as NoRef.
    apply ntqg_preserves_semantics in HN2.
    bdestruct (q =? n); try discriminate.
    subst.
    destruct (next_single_qubit_gate g n) eqn:HN1; try discriminate.
    repeat destruct p.
    dependent destruction f; try discriminate.
    apply nsqg_preserves_semantics in HN1.
    destruct (next_two_qubit_gate g1 n) eqn:HN2'; try discriminate.
    repeat destruct p.
    specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ HN2') as NoRef'.
    apply ntqg_preserves_semantics in HN2'.
    bdestruct (n =? n1); try discriminate.
    bdestruct (n0 =? n2); try discriminate.
    destruct (does_not_reference g3 n2) eqn:NoRef''; try discriminate.
    simpl in HS2.
    inversion HS2; subst. clear HS2.
    rewrite HN2, HN1, HN2'.
    rewrite app_comm_cons.
    rewrite (does_not_reference_commutes_app1 _ (fU_PI4 k) _ NoRef).
    repeat rewrite <- app_assoc.
    apply app_congruence; try reflexivity. 
    repeat rewrite app_cons_app.
    repeat rewrite app_assoc.
    apply app_congruence; try reflexivity. 
    repeat rewrite <- app_assoc.    
    rewrite <- (does_not_reference_commutes_app2 _ fU_CNOT _ _ NoRef'' NoRef').
    rewrite (app_assoc g3).
    rewrite <- (does_not_reference_commutes_app2 _ fU_CNOT _ _ NoRef'' NoRef').
    rewrite <- app_assoc.
    rewrite <- (does_not_reference_commutes_app1 _ (fU_PI4 k) _ NoRef').
    repeat rewrite app_assoc.    
    apply app_congruence; try reflexivity.
    unfold uc_equiv_l; simpl.
    unfold uc_equiv; simpl. unfold ueval1, ueval_cnot.
    bdestruct (n2 <? n1).
    + unfold pad.
      bdestruct (n2 + (1 + (n1 - n2 - 1) + 1) <=? dim).
      2: remove_zero_gates; try easy.      
      bdestructΩ (n1 + 1 <=? dim).
      remember (n1 - n2 - 1) as x.
      replace (n1 - n2) with (x+1) by lia.
      remember (dim - S (x + 1) - n2) as y.
      replace dim with (n2 + 1 + x + 1 + y) by lia.
      replace n1 with (n2 + 1 + x) by lia. 
      replace (n2 + 1 + x + 1 + y - 1 - (n2 + 1 + x)) with y by lia.
      repeat rewrite Nat.pow_add_r.
      simpl (2^1).
      remember (2^n2) as a. remember (2^x) as b. remember (2^y) as c. clear.
      restore_dims_fast.
      repeat rewrite <- id_kron. 
      distribute_plus.
      repeat rewrite kron_assoc.
      restore_dims_fast.
      repeat rewrite kron_mixed_product.
      remove_id_gates.
      restore_dims_fast.
      repeat rewrite kron_assoc.
      restore_dims_fast.
      repeat rewrite kron_mixed_product.
      Msimpl.
      do 2 apply f_equal2.
      * replace (σx × phase_shift (IZR k0 * PI / 4) × σx × phase_shift (IZR k * PI / 4))
        with (phase_shift (IZR k * PI / 4) × σx × phase_shift (IZR k0 * PI / 4) × σx) by
        solve_matrix.
        reflexivity.
      * replace (∣0⟩⟨0∣ × ∣1⟩⟨1∣) with (@Zero 2 2) by solve_matrix.
        remove_zero_gates; try easy.      
      * replace (∣1⟩⟨1∣ × ∣0⟩⟨0∣) with (@Zero 2 2) by solve_matrix.
        remove_zero_gates; try easy.      
      * rewrite 2 phase_mul. rewrite Rplus_comm. reflexivity.
    + unfold pad.
      bdestruct(n1 <? n2).
      2: remove_zero_gates; try easy.   
      rename n1 into n, n2 into n1. rename n into n2.
      bdestruct (n2 + (1 + (n1 - n2 - 1) + 1) <=? dim).
      2: remove_zero_gates; try easy.      
      bdestructΩ (n2 + 1 <=? dim).
      remember (n1 - n2 - 1) as x.
      replace (n1 - n2) with (1+x) by lia.
      remember (dim - S (x + 1) - n2) as y.
      replace dim with (n2 + 1 + x + 1 + y) by lia.
      replace (n2 + 1 + x + 1 + y - 1 - n2) with (x + 1 + y) by lia.
      repeat rewrite Nat.pow_add_r.
      simpl (2^1).
      remember (2^n2) as a. remember (2^x) as b. remember (2^y) as c. clear.
      restore_dims_fast.
      repeat rewrite <- id_kron. 
      distribute_plus.
      repeat rewrite kron_assoc.
      restore_dims_fast.
      repeat rewrite kron_mixed_product.
      remove_id_gates.
      do 2 apply f_equal2.
      * replace (σx × phase_shift (IZR k0 * PI / 4) × σx × phase_shift (IZR k * PI / 4))
        with (phase_shift (IZR k * PI / 4) × σx × phase_shift (IZR k0 * PI / 4) × σx) by
        solve_matrix.
        reflexivity.
      * replace (∣0⟩⟨0∣ × ∣1⟩⟨1∣) with (@Zero 2 2) by solve_matrix.
        remove_zero_gates; try easy.      
      * replace (∣1⟩⟨1∣ × ∣0⟩⟨0∣) with (@Zero 2 2) by solve_matrix.
        remove_zero_gates; try easy.      
      * rewrite 2 phase_mul. rewrite Rplus_comm. reflexivity.
  - clear HS HS2.
    unfold search_for_Rz_pat3 in HS3. 
    destruct p.
    inversion H; subst. clear H.
    destruct (next_two_qubit_gate l q) eqn:HN2; try discriminate.
    repeat destruct p.
    specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ HN2) as NoRef.
    apply ntqg_preserves_semantics in HN2.
    bdestruct (q =? n0); try discriminate.
    subst.
    inversion HS3. subst.
    rewrite HN2.
    repeat rewrite app_cons_app.
    repeat rewrite app_assoc.
    apply app_congruence; try reflexivity. 
    rewrite (does_not_reference_commutes_app1 _ (fU_PI4 k) _ NoRef).
    repeat rewrite <- app_assoc.
    apply app_congruence; try reflexivity. 
    (* simple slide lemma: should exist already? *)
    unfold uc_equiv_l; simpl.
    unfold uc_equiv; simpl. 
    rewrite 2 Mmult_1_l; auto with wf_db.
    unfold ueval1, ueval_cnot.
    bdestruct (n0 <? n).
    + unfold pad. (* pad lemma should work *)
      rename n0 into n2. rename n into n1. 
      bdestruct (n2 + (1 + (n1 - n2 - 1) + 1) <=? dim).
      2: remove_zero_gates; try easy.      
      bdestructΩ (n1 + 1 <=? dim).
      remember (n1 - n2 - 1) as x.
      replace (n1 - n2) with (x+1) by lia.
      remember (dim - S (x + 1) - n2) as y.
      replace dim with (n2 + 1 + x + 1 + y) by lia.
      replace (n2 + 1 + x + 1 + y - 1 - n2) with (x + 1 + y) by lia.
      bdestructΩ (n2 + 1 <=? n2 + 1 + x + 1 + y).
      repeat rewrite Nat.pow_add_r.
      simpl (2^1).
      remember (2^n2) as a. remember (2^x) as b. remember (2^y) as c. clear.
      restore_dims_fast.
      repeat rewrite <- id_kron. 
      distribute_plus.
      repeat rewrite kron_assoc.
      restore_dims_fast.
      repeat rewrite kron_mixed_product.
      remove_id_gates.
      restore_dims_fast.
      repeat rewrite kron_assoc.
      restore_dims_fast.
      repeat rewrite kron_mixed_product.
      Msimpl.
      apply f_equal2.
      * replace  (∣1⟩⟨1∣ × phase_shift (IZR k * PI / 4))
        with (phase_shift (IZR k * PI / 4) × ∣1⟩⟨1∣) by solve_matrix.
        reflexivity.
      * replace  (∣0⟩⟨0∣ × phase_shift (IZR k * PI / 4))
        with (phase_shift (IZR k * PI / 4) × ∣0⟩⟨0∣) by solve_matrix.
        reflexivity.
    + unfold pad. (* pad lemma should work *)
      bdestruct (n <? n0).
      2: remove_zero_gates; try easy.      
      rename n into n2. rename n0 into n1. 
      bdestruct (n2 + (1 + (n1 - n2 - 1) + 1) <=? dim).
      2: remove_zero_gates; try easy.      
      bdestructΩ (n1 + 1 <=? dim).
      remember (n1 - n2 - 1) as x.
      replace (n1 - n2) with (1+x) by lia.
      replace n1 with (n2 + 1 +x) by lia.
      remember (dim - S (x + 1) - n2) as y.      
      replace (dim - 1 - (n2 + 1 + x)) with y by lia.
      replace dim with (n2 + 1 + x + 1 + y) by lia.      
      repeat rewrite Nat.pow_add_r.
      simpl (2^1).
      remember (2^n2) as a. remember (2^x) as b. remember (2^y) as c. clear.
      restore_dims_fast.
      repeat rewrite <- id_kron. 
      distribute_plus.
      repeat rewrite kron_assoc.
      restore_dims_fast.
      repeat rewrite kron_mixed_product.
      remove_id_gates.
      restore_dims_fast.
      repeat rewrite kron_assoc.
      restore_dims_fast.
      repeat rewrite kron_mixed_product.
      Msimpl.
      apply f_equal2.
      * replace  (∣1⟩⟨1∣ × phase_shift (IZR k * PI / 4))
        with (phase_shift (IZR k * PI / 4) × ∣1⟩⟨1∣) by solve_matrix.
        reflexivity.
      * replace  (∣0⟩⟨0∣ × phase_shift (IZR k * PI / 4))
        with (phase_shift (IZR k * PI / 4) × ∣0⟩⟨0∣) by solve_matrix.
        reflexivity.
Qed.

Lemma commuting_CNOT_pat : forall {dim} (l : gate_list dim) q1 q2 l1 l2,
  search_for_commuting_CNOT_pat l q1 q2 = Some (l1, l2) ->
  _CNOT q1 q2 :: l =l= l1 ++ [_CNOT q1 q2] ++ l2.
Proof.
(* Will require lemmas about search_for_CNOT_pat1, 2, 3, and 4. *)
  intros.
  unfold search_for_commuting_CNOT_pat in H.
  destruct (search_for_CNOT_pat1 l q3 q4) eqn:HS; 
  [|clear HS; destruct (search_for_CNOT_pat2 l q3 q4) eqn:HS;
  [|clear HS; destruct (search_for_CNOT_pat3 l q3 q4) eqn:HS; 
  [|clear HS; destruct (search_for_CNOT_pat4 l q3 q4) eqn:HS]]]; try discriminate.
  - unfold search_for_CNOT_pat1 in HS.
    destruct p.
    inversion H; subst. clear H.
    destruct (next_single_qubit_gate l q3) eqn:HN1; try discriminate.
    destruct p.
    apply nsqg_preserves_semantics in HN1.
    dependent destruction f; try discriminate.
    inversion HS; subst. clear HS.
    rewrite HN1. (* Wasn't this the last case of Rz *)
    repeat rewrite app_cons_app.
    replace (_CNOT q3 q4 :: App1 (fU_PI4 k) q3 :: l2) with
        ([_CNOT q3 q4] ++ [_PI4 k q3] ++ l2) by reflexivity.
    repeat rewrite app_assoc.
    apply app_congruence; try reflexivity.
    unfold uc_equiv_l; simpl.
    unfold uc_equiv; simpl. 
    Msimpl.
    unfold ueval1, ueval_cnot.
    bdestruct (q3 <? q4).
    + unfold pad. 
      rename q3 into n2. rename q4 into n1. 
      bdestruct (n2 + (1 + (n1 - n2 - 1) + 1) <=? dim).
      2: remove_zero_gates; try easy.      
      bdestructΩ (n2 + 1 <=? dim).
      remember (n1 - n2 - 1) as x.
      replace (n1 - n2) with (x+1) by lia.
      remember (dim - S (x + 1) - n2) as y.
      replace dim with (n2 + 1 + x + 1 + y) by lia.
      replace (n2 + 1 + x + 1 + y - 1 - n2) with (x + 1 + y) by lia.
      repeat rewrite Nat.pow_add_r.
      simpl (2^1).
      remember (2^n2) as a. remember (2^x) as b. remember (2^y) as c. clear.
      restore_dims_fast.
      repeat rewrite <- id_kron. 
      distribute_plus.
      repeat rewrite kron_assoc.
      restore_dims_fast.
      repeat rewrite kron_mixed_product.
      remove_id_gates.
      restore_dims_fast.
      repeat rewrite kron_assoc.
      restore_dims_fast.
      repeat rewrite kron_mixed_product.
      Msimpl.
      apply f_equal2.
      * replace  (∣1⟩⟨1∣ × phase_shift (IZR k * PI / 4))
        with (phase_shift (IZR k * PI / 4) × ∣1⟩⟨1∣) by solve_matrix.
        reflexivity.
      * replace  (∣0⟩⟨0∣ × phase_shift (IZR k * PI / 4))
        with (phase_shift (IZR k * PI / 4) × ∣0⟩⟨0∣) by solve_matrix.
        reflexivity.
    + unfold pad. (* exactly the final case of previous lemma *)
      rename q4 into n2. rename q3 into n1. 
      bdestruct (n2 <? n1).
      2: remove_zero_gates; try easy.      
      bdestruct (n2 + (1 + (n1 - n2 - 1) + 1) <=? dim).
      2: remove_zero_gates; try easy.      
      bdestructΩ (n1 + 1 <=? dim).
      remember (n1 - n2 - 1) as x.
      replace (n1 - n2) with (1+x) by lia.
      replace n1 with (n2 + 1 +x) by lia.
      remember (dim - S (x + 1) - n2) as y.      
      replace (dim - 1 - (n2 + 1 + x)) with y by lia.
      replace dim with (n2 + 1 + x + 1 + y) by lia.      
      repeat rewrite Nat.pow_add_r.
      simpl (2^1).
      remember (2^n2) as a. remember (2^x) as b. remember (2^y) as c. clear.
      restore_dims_fast.
      repeat rewrite <- id_kron. 
      distribute_plus.
      repeat rewrite kron_assoc.
      restore_dims_fast.
      repeat rewrite kron_mixed_product.
      remove_id_gates.
      restore_dims_fast.
      repeat rewrite kron_assoc.
      restore_dims_fast.
      repeat rewrite kron_mixed_product.
      Msimpl.
      apply f_equal2.
      * replace  (∣1⟩⟨1∣ × phase_shift (IZR k * PI / 4))
        with (phase_shift (IZR k * PI / 4) × ∣1⟩⟨1∣) by solve_matrix.
        reflexivity.
      * replace  (∣0⟩⟨0∣ × phase_shift (IZR k * PI / 4))
        with (phase_shift (IZR k * PI / 4) × ∣0⟩⟨0∣) by solve_matrix.
        reflexivity.
  - unfold search_for_CNOT_pat2 in HS.
    destruct p.
    inversion H; subst. clear H.
    destruct (next_two_qubit_gate l q4) eqn:HN2; try discriminate.
    repeat destruct p.
    specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ HN2) as NoRef.
    apply ntqg_preserves_semantics in HN2.
    bdestruct (q4 =? n); try discriminate. subst.   
    destruct (does_not_reference g0 q3) eqn:NoRef'; try discriminate. 
    destruct (does_not_reference g0 n0) eqn:NoRef''; try discriminate.
    simpl in HS. inversion HS; subst. clear HS.
    rewrite HN2. 
    repeat rewrite app_cons_app.
    repeat rewrite app_assoc.
    rewrite (does_not_reference_commutes_app2 _ fU_CNOT _ _ NoRef' NoRef).
    apply app_congruence; try reflexivity.
    repeat rewrite <- app_assoc.
    apply app_congruence; try reflexivity.
    
    unfold uc_equiv_l; simpl.
    unfold uc_equiv; simpl. 
    Msimpl.
    unfold ueval_cnot.
    bdestruct (n0 <? n); bdestruct (q3 <? n);
    bdestructΩ (n <? n0); bdestructΩ (n <? q3); remove_zero_gates; trivial.       
    + unfold pad. 
      bdestruct (n0 + S (n - n0 - 1 + 1) <=? dim).
      2: remove_zero_gates; easy.      
      bdestruct (q3 + S (n - q3 - 1 + 1) <=? dim).
      2: remove_zero_gates; easy.      
      bdestruct (n0 <? q3).
      
      remember (n - n0 - 1) as x.
      replace n with (n0 + x + 1) by lia. 
      replace (n0 + x + 1 - n0) with (x + 1) by lia.
      remember (dim - S (x + 1) - n0) as y.
      replace dim with (n0 + 1 + x + 1 + y) by lia.
      rewrite Nat.sub_add by lia.
      replace (n0 + 1 + x + 1 + y - S (n0 + x + 1 - q3) - q3)
        with y by lia.

      (* hadran alach *)
Admitted.


(* Proofs about propagation functions *)

Lemma propagate_H_sound : forall {dim} (l : gate_list dim) q l',
  q < dim ->
  propagate_H l q = Some l' ->
  _H q :: l =l= l'.
Proof. 
  intros.
  unfold propagate_H in H0; simpl in H0.
  remember (next_single_qubit_gate l q) as next_gate; symmetry in Heqnext_gate.
  destruct next_gate; try easy.
  destruct p; dependent destruction f; try easy.
  inversion H0; subst.
  rewrite (nsqg_preserves_semantics _ _ _ _ Heqnext_gate).
  apply H_H_cancel; assumption.
Qed.

Lemma propagate_H_WT : forall {dim} (l : gate_list dim) q l',
  q < dim ->
  uc_well_typed_l l -> 
  propagate_H l q = Some l' ->
  uc_well_typed_l l'.
Proof.
  intros.
  specialize (propagate_H_sound l q l' H H1) as H2.
  apply (uc_equiv_l_implies_WT _ _ H2).
  constructor; assumption.
Qed.

Lemma propagate_X_sound : forall {dim} (l : gate_list dim) q n l',
  q < dim ->
  propagate_X l q n = Some l' ->
  _X q :: l =l= l'.
Proof.
  intros.
  generalize dependent l'.
  generalize dependent l.
  induction n; try easy.
  simpl.
  intros.
  remember (next_single_qubit_gate l q) as next_gate; symmetry in Heqnext_gate.
  destruct next_gate.
  - destruct p.
    dependent destruction f. 
    2: { (* Cancel case *)
         inversion H0; subst.
         rewrite (nsqg_preserves_semantics _ _ _ _ Heqnext_gate).
         apply X_X_cancel; assumption. }
    (* Commute cases *)
    + (* copy & paste #1 *)
      remember (search_for_commuting_X_pat l q) as pat; symmetry in Heqpat.
      destruct pat; try easy.
      destruct p.    
      remember (propagate_X g0 q n) as prop; symmetry in Heqprop.
      destruct prop; try easy.    
      inversion H0; subst.
      rewrite (commuting_X_pat _ _ _ _ Heqpat).
      rewrite (IHn _ _ Heqprop).
      reflexivity.
    + (* copy & paste #2 *)
      remember (search_for_commuting_X_pat l q) as pat; symmetry in Heqpat.
      destruct pat; try easy.
      destruct p.    
      remember (propagate_X g0 q n) as prop; symmetry in Heqprop.
      destruct prop; try easy.    
      inversion H0; subst.
      rewrite (commuting_X_pat _ _ _ _ Heqpat).
      rewrite (IHn _ _ Heqprop).
      reflexivity.
  - (* copy & paste #3 *)
    remember (search_for_commuting_X_pat l q) as pat; symmetry in Heqpat.
    destruct pat; try easy.
    destruct p.    
    remember (propagate_X g q n) as prop; symmetry in Heqprop.
    destruct prop; try easy.    
    inversion H0; subst.
    rewrite (commuting_X_pat _ _ _ _ Heqpat).
    rewrite (IHn _ _ Heqprop).
    reflexivity.
Qed.

Lemma propagate_X_WT : forall {dim} (l : gate_list dim) q n l',
  q < dim ->
  uc_well_typed_l l ->
  propagate_X l q n = Some l' ->
  uc_well_typed_l l'.
Proof.
  intros.
  specialize (propagate_X_sound l q n l' H H1) as H2.
  apply (uc_equiv_l_implies_WT _ _ H2).
  constructor; assumption.
Qed.

Lemma propagate_PI4_sound : forall {dim} k (l : gate_list dim) q n l',
  q < dim ->
  propagate_PI4 k l q n = Some l' ->
  _PI4 k q :: l =l= l'.
Proof.
  intros.
  generalize dependent l'.
  generalize dependent l.
  induction n; try easy.
  simpl.
  intros.
  remember (next_single_qubit_gate l q) as next_gate; symmetry in Heqnext_gate.
  destruct next_gate.
  - destruct p.
    dependent destruction f. 
    3: { (* Cancel/combine case *)
         remember (k + k0 =? 8)%Z as k_k0_8.
         destruct k_k0_8; symmetry in Heqk_k0_8.
         apply Z.eqb_eq in Heqk_k0_8.
         inversion H0; subst.
         rewrite (nsqg_preserves_semantics _ _ _ _ Heqnext_gate).
         apply PI4_PI4_cancel; assumption. 
         destruct (k + k0 <? 8)%Z; inversion H0; subst;
         rewrite (nsqg_preserves_semantics _ _ _ _ Heqnext_gate).
         apply PI4_PI4_combine.
         apply PI4_PI4_m8_combine. }
    (* Commute cases *)
    + (* copy & paste #1 *)
      remember (search_for_commuting_Rz_pat l q) as pat; symmetry in Heqpat.
      destruct pat; try easy.
      destruct p.    
      remember (propagate_PI4 k g0 q n) as prop; symmetry in Heqprop.
      destruct prop; try easy.    
      inversion H0; subst.
      rewrite (commuting_Rz_pat _ _ _ _ _ Heqpat).
      rewrite (IHn _ _ Heqprop).
      reflexivity.
    + (* copy & paste #2 *)
      remember (search_for_commuting_Rz_pat l q) as pat; symmetry in Heqpat.
      destruct pat; try easy.
      destruct p.    
      remember (propagate_PI4 k g0 q n) as prop; symmetry in Heqprop.
      destruct prop; try easy.    
      inversion H0; subst.
      rewrite (commuting_Rz_pat _ _ _ _ _ Heqpat).
      rewrite (IHn _ _ Heqprop).
      reflexivity.
  - (* copy & paste #3 *)
    remember (search_for_commuting_Rz_pat l q) as pat; symmetry in Heqpat.
    destruct pat; try easy.
    destruct p.    
    remember (propagate_PI4 k g q n) as prop; symmetry in Heqprop.
    destruct prop; try easy.    
    inversion H0; subst.
    rewrite (commuting_Rz_pat _ _ _ _ _ Heqpat).
    rewrite (IHn _ _ Heqprop).
    reflexivity.
Qed.

Lemma propagate_PI4_WT : forall {dim} k (l : gate_list dim) q n l',
  q < dim ->
  uc_well_typed_l l ->
  propagate_PI4 k l q n = Some l' ->
  uc_well_typed_l l'.
Proof.
  intros.
  specialize (propagate_PI4_sound k l q n l' H H1) as H2.
  apply (uc_equiv_l_implies_WT _ _ H2).
  constructor; assumption.
Qed.

Lemma propagate_CNOT_sound : forall {dim} (l : gate_list dim) q1 q2 n l',
  q1 < dim ->
  q2 < dim -> 
  q1 <> q2 ->
  propagate_CNOT l q1 q2 n = Some l' ->
  _CNOT q1 q2 :: l =l= l'.
Proof. 
  intros.
  unfold propagate_CNOT in H2; simpl in H2.
  remember (next_two_qubit_gate l q3) as next_gate; symmetry in Heqnext_gate.
  destruct next_gate; destruct n; try easy.
  destruct p; destruct p; destruct p. 
  remember (does_not_reference g0 q4) as DNR; symmetry in HeqDNR.
  destruct DNR; bdestruct (q3 =? n1); bdestruct (q4 =? n0); 
  simpl in H2; inversion H2; subst.
  rewrite (ntqg_preserves_semantics _ _ _ _ _ _ Heqnext_gate).
  specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ Heqnext_gate) as H3.
  rewrite app_cons_app.
  rewrite (app_assoc _ _ g).
  rewrite <- (does_not_reference_commutes_app2 _ fU_CNOT _ _ H3 HeqDNR).
  simpl.
  specialize (CNOT_CNOT_cancel [] (g0 ++ g) _ _ H H0 H1) as H4.
  simpl in H4.
  assumption.
Qed.

Lemma propagate_CNOT_WT : forall {dim} (l : gate_list dim) q1 q2 n l',
  q1 < dim ->
  q2 < dim -> 
  q1 <> q2 ->
  uc_well_typed_l l ->
  propagate_CNOT l q1 q2 n = Some l' ->
  uc_well_typed_l l'.
Proof.
  intros.
  specialize (propagate_CNOT_sound l q3 q4 n l' H H0 H1 H3) as H4.
  apply (uc_equiv_l_implies_WT _ _ H4).
  constructor; assumption.
Qed.

Lemma cancel_gates'_sound : forall {dim} (l : gate_list dim) n,
  uc_well_typed_l l -> cancel_gates' l n =l= l.
Proof.
  intros.
  generalize dependent l.
  induction n; intros; try reflexivity.
  destruct l; try reflexivity.
  destruct g.
  - inversion H; subst. 
    dependent destruction f.
    + (* fU_H *) 
      simpl.
      remember (propagate_H l n0) as prop; symmetry in Heqprop.
      destruct prop; rewrite IHn; try reflexivity; try assumption.
      rewrite (propagate_H_sound _ _ _ H2 Heqprop).
      reflexivity.
      apply (propagate_H_WT _ _ _ H2 H4 Heqprop).
    + (* fU_X *)
      simpl.
      remember (propagate_X l n0 (length l)) as prop; symmetry in Heqprop.
      destruct prop; rewrite IHn; try reflexivity; try assumption.
      rewrite (propagate_X_sound _ _ _ _ H2 Heqprop).
      reflexivity.
      apply (propagate_X_WT _ _ _ _ H2 H4 Heqprop).
    + (* fU_PI4 *)
      simpl.
      remember (propagate_PI4 k l n0 (length l)) as prop; symmetry in Heqprop.
      destruct prop; rewrite IHn; try reflexivity; try assumption.
      rewrite (propagate_PI4_sound _ _ _ _ _ H2 Heqprop).
      reflexivity.
      apply (propagate_PI4_WT _ _ _ _ _ H2 H4 Heqprop).
  - (* fU_CNOT *)
    dependent destruction f; simpl.
    inversion H; subst. 
    remember (propagate_CNOT l n0 n1 (length l)) as prop; symmetry in Heqprop.
    destruct prop; rewrite IHn; try reflexivity; try assumption.
    rewrite (propagate_CNOT_sound _ _ _ _ _ H4 H5 H6 Heqprop).
    reflexivity.
    apply (propagate_CNOT_WT _ _ _ _ _ H4 H5 H6 H7 Heqprop).
Qed.

Lemma cancel_gates_sound : forall {dim} (l : gate_list dim), 
  uc_well_typed_l l -> cancel_gates l =l= l.
Proof. intros. apply cancel_gates'_sound; assumption. Qed.