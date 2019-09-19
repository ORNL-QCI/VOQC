Require Import UnitarySem.
Require Import Utilities.
Require Import PI4GateSet.

(* Combine rotations that act on the same terms in the phase polynomial 
   representation of a program. For a thorough description of this optimization, 
   see the "Rotation merging using phase polynomials" section of [1], Sec. 6.4 
   of [2], or Sec. 3 of [3].
 
   [1] Nam et al., "Automated optimization of large quantum circuits with continuous parameters"
   [2] Amy et al., "A meet-in-the-middle algorithm for fast synthesis of depth-optimal
quantum circuits"
   [3] Amy et al., "Polynomial-time T-depth Optimization of Clifford+T circuits via
Matroid Partitioning"
*)
  
(** Find a {CNOT, X, Rz} subcircuit. **)

(* Find a subcircuit consisting of {CNOT, X, Rz} gates, starting from a 
   particular qubit q. Our algorithm is different from the one used in 
   Nam et al. (see [1, Eq. 8]) and results in smaller subcircuits because 
   we want to maintain the following property:
       get_subcircuit l q = (l1, s, l2)-> l ≡ l1 ++ s ++ l2
   To see the difference, compare our example 'test4' to [1, Eq. 8]. *)

Definition add x l :=
  if inb x l then l else (x :: l).

(* l = gate list
   qs1 = list of qubits to include in the subcircuit
   qs2 = list of qubits to exclude from the subcircuit 
   n = a dummy argument to convince Coq of termination; we start with n large
       enough that the O case will never be reached.

   Find a subcircuit in l that involves qubits in qs1, but not qubits
   in qs2, and only uses CNOT, X, and Rz gates. Return (l1, s, l2) s.t.
   s is the desired subcircuit and l ≡ l1 ++ s ++ l2. *)
Fixpoint get_subcircuit' {dim} (l : PI4_list dim) (qs1 qs2 : list nat) n
             : (PI4_list dim * PI4_list dim * PI4_list dim) :=
  match n with
  | O => ([], [], l)
  | S n' => match next_gate l qs1 with
           | Some (l1, App1 UPI4_H q, l2) =>
               let (tmp, l2') := get_subcircuit' l2 qs1 (add q qs2) n' in
               let (l1', s) := tmp in
               (l1 ++ l1', s, [App1 UPI4_H q] ++ l2')
           | Some (l1, App1 u q, l2) =>
               let (tmp, l2') := get_subcircuit' l2 qs1 qs2 n' in
               let (l1', s) := tmp in
               if inb q qs2
               then (l1 ++ l1', s, [App1 u q] ++ l2')
               else (l1 ++ l1', [App1 u q] ++ s, l2')
           | Some (l1, App2 u q1 q2, l2) =>
               if (inb q1 qs2) || (inb q2 qs2)
               then let (tmp, l2') := get_subcircuit' l2 (add q1 (add q2 qs1)) (add q1 (add q2 qs2)) n' in
                    let (l1', s) := tmp in
                    (l1 ++ l1', s, [App2 u q1 q2] ++ l2')
               else let (tmp, l2') := get_subcircuit' l2 (add q1 (add q2 qs1)) qs2 n' in
                    let (l1', s) := tmp in
                    (l1 ++ l1', [App2 u q1 q2] ++ s, l2')
           | _ => ([], [], l)
           end
  end.

Definition get_subcircuit {dim} (l : PI4_list dim) q := 
  get_subcircuit' l [q] [] (List.length l).

(* Proofs *)

Lemma add_In_x : forall x l, List.In x (add x l).
Proof.
  intros.
  unfold add.
  destruct (inb x l) eqn:Hinb.
  apply inb_true; assumption.
  left; reflexivity.
Qed.

Lemma add_In_l : forall x y l, List.In x l -> List.In x (add y l).
Proof.
  intros.
  unfold add.
  destruct (inb y l);
  try right; assumption.
Qed.

Lemma get_subcircuit'_l1_does_not_reference : forall {dim} (l : PI4_list dim) qs1 qs2 n l1 s l2,
  get_subcircuit' l qs1 qs2 n = (l1, s, l2) ->
  forall q, List.In q qs1 -> does_not_reference l1 q = true.
Proof. 
  intros dim l qs1 qs2 n l1 s l2 H.
  generalize dependent s.
  generalize dependent qs2.
  generalize dependent qs1.
  generalize dependent l2.
  generalize dependent l1.
  generalize dependent l.
  induction n; intros l l1 l2 qs1 qs2 s H; simpl in H.
  - inversion H; subst. constructor.
  - destruct (next_gate l qs1) eqn:ng.
    2: { inversion H; subst. constructor. }
    repeat destruct p.
    destruct g1.
    + dependent destruction p;
      [ destruct (get_subcircuit' g qs1 (add n0 qs2) n) eqn:subc
      | destruct (get_subcircuit' g qs1 qs2 n) eqn:subc
      | destruct (get_subcircuit' g qs1 qs2 n) eqn:subc ];
      destruct p;
      try destruct (inb n0 qs2);
      inversion H; subst.
      all: intros q Hq;
           apply does_not_reference_app;
           apply andb_true_intro;
           split.
      all: try (apply (next_gate_l1_does_not_reference _ _ _ _ _ ng); assumption).
      all: eapply IHn; try apply subc; assumption.
    + destruct (inb n0 qs2 || inb n1 qs2);
      [ destruct (get_subcircuit' g (add n0 (add n1 qs1)) (add n0 (add n1 qs2)) n) eqn:subc
      | destruct (get_subcircuit' g (add n0 (add n1 qs1)) qs2 n) eqn:subc ];
      destruct p0;
      inversion H; subst.
      all: intros q Hq;
           apply does_not_reference_app;
           apply andb_true_intro;
           split.
      all: try (apply (next_gate_l1_does_not_reference _ _ _ _ _ ng); assumption).
      all: eapply IHn; try apply subc; repeat apply add_In_l; assumption.
    + dependent destruction p.
Qed.

Lemma get_subcircuit'_s_does_not_reference : forall {dim} (l : PI4_list dim) qs1 qs2 n l1 s l2,
  get_subcircuit' l qs1 qs2 n = (l1, s, l2) ->
  forall q, List.In q qs2 -> does_not_reference s q = true.
Proof.
  intros dim l qs1 qs2 n l1 s l2 H.
  generalize dependent s.
  generalize dependent qs2.
  generalize dependent qs1.
  generalize dependent l2.
  generalize dependent l1.
  generalize dependent l.
  induction n; intros l l1 l2 qs1 qs2 s H; simpl in H.
  - inversion H; subst. constructor.
  - destruct (next_gate l qs1) eqn:ng.
    2: { inversion H; subst. constructor. }
    repeat destruct p.
    destruct g1.
    + dependent destruction p;
      [ destruct (get_subcircuit' g qs1 (add n0 qs2) n) eqn:subc
      | destruct (get_subcircuit' g qs1 qs2 n) eqn:subc
      | destruct (get_subcircuit' g qs1 qs2 n) eqn:subc ];
      destruct p;
      try destruct (inb n0 qs2) eqn:Hinb;
      inversion H; subst.
      all: intros q Hq.
      all: try (simpl; apply andb_true_intro; split).
      all: try (eapply IHn; [apply subc |] ).
      all: try apply add_In_l; try assumption.
      all: apply negb_true_iff; apply eqb_neq; 
           apply (inb_false _ _ Hinb); assumption.
    + destruct (inb n0 qs2 || inb n1 qs2) eqn:Hinb;
      [ destruct (get_subcircuit' g (add n0 (add n1 qs1)) (add n0 (add n1 qs2)) n) eqn:subc
      | destruct (get_subcircuit' g (add n0 (add n1 qs1)) qs2 n) eqn:subc ];
      destruct p0;
      inversion H; subst.
      all: intros q Hq.
      all: try (simpl; apply andb_true_intro; split).
      all: try (eapply IHn; [apply subc |] ).
      all: repeat apply add_In_l; try assumption.
      apply orb_false_elim in Hinb as [Hinb1 Hinb2].
      apply negb_true_iff; apply orb_false_intro; apply eqb_neq.
      apply (inb_false _ _ Hinb1); assumption.
      apply (inb_false _ _ Hinb2); assumption.
    + dependent destruction p.
Qed.

Lemma cons_to_app : forall {A} (h : A) (t : list A), h :: t = [h] ++ t.
Proof. reflexivity. Qed.

Lemma get_subcircuit'_preserves_semantics : forall {dim} (l : PI4_list dim) qs1 qs2 n l1 s l2,
  get_subcircuit' l qs1 qs2 n = (l1, s, l2) ->
  l =l= l1 ++ s ++ l2.
Proof.
  intros.
  generalize dependent s.
  generalize dependent qs2.
  generalize dependent qs1.
  generalize dependent l2.
  generalize dependent l1.
  generalize dependent l.
  induction n; intros l l1 l2 qs1 qs2 s H.
  - inversion H; subst. reflexivity.
  - simpl in H.
    destruct (next_gate l qs1) eqn:ng.
    2: { inversion H; subst. reflexivity. }
    repeat destruct p.
    destruct g1.
    + dependent destruction p;
      [ destruct (get_subcircuit' g qs1 (add n0 qs2) n) eqn:subc
      | destruct (get_subcircuit' g qs1 qs2 n) eqn:subc
      | destruct (get_subcircuit' g qs1 qs2 n) eqn:subc];
      destruct p;
      try destruct (inb n0 qs2) eqn:Hinb;
      inversion H; subst.
      all: assert (dnr1 : does_not_reference p n0 = true) by
           (eapply get_subcircuit'_l1_does_not_reference;
            [ apply subc | eapply next_gate_app1_returns_q; apply ng]).
      all: try assert (dnr2 : does_not_reference s n0 = true) by
           (eapply get_subcircuit'_s_does_not_reference;
            [ apply subc 
            | try (apply add_In_x);
              try (apply inb_true; assumption) ]).
      all: apply next_gate_preserves_structure in ng;
           rewrite ng;
           apply IHn in subc;
           rewrite subc.
      all: try rewrite (cons_to_app _ p0).
      all: try rewrite (cons_to_app _ p1).
      all: repeat rewrite <- app_assoc;
           apply app_congruence; try reflexivity;
           repeat rewrite app_assoc;
           apply app_congruence; try reflexivity;
           rewrite does_not_reference_commutes_app1; try assumption;
           try reflexivity.
      all: repeat rewrite <- app_assoc;
           rewrite does_not_reference_commutes_app1; try assumption;
           reflexivity.
    + destruct (inb n0 qs2 || inb n1 qs2) eqn:Hinb;
      [ destruct (get_subcircuit' g (add n0 (add n1 qs1)) (add n0 (add n1 qs2)) n) eqn:subc
      | apply orb_false_elim in Hinb as [Hinb1 Hinb2];
        destruct (get_subcircuit' g (add n0 (add n1 qs1)) qs2 n) eqn:subc];
      destruct p0;
      inversion H; subst.
      * assert (dnr1 : does_not_reference p0 n0 = true).
        { eapply get_subcircuit'_l1_does_not_reference.
          apply subc.
          apply add_In_x. }
        assert (dnr2 : does_not_reference s n0 = true).
        { eapply get_subcircuit'_s_does_not_reference.
          apply subc.
           apply add_In_x. }
        assert (dnr3 : does_not_reference p0 n1 = true).
        { eapply get_subcircuit'_l1_does_not_reference.
          apply subc.
          apply add_In_l. apply add_In_x. }
        assert (dnr4 : does_not_reference s n1 = true).
        { eapply get_subcircuit'_s_does_not_reference.
          apply subc.
          apply add_In_l. apply add_In_x. }
        apply next_gate_preserves_structure in ng.
        rewrite ng.
        apply IHn in subc.
        rewrite subc.
        rewrite (cons_to_app _ p1).
        repeat rewrite <- app_assoc.
        apply app_congruence; try reflexivity.
        repeat rewrite app_assoc.
        apply app_congruence; try reflexivity.
        rewrite does_not_reference_commutes_app2; try assumption.
        repeat rewrite <- app_assoc.
        rewrite does_not_reference_commutes_app2; try assumption.
        reflexivity.
      * assert (dnr1 : does_not_reference p0 n0 = true).
        { eapply get_subcircuit'_l1_does_not_reference.
          apply subc.
          apply add_In_x. }
        assert (dnr2 : does_not_reference p0 n1 = true).
        { eapply get_subcircuit'_l1_does_not_reference.
          apply subc.
          apply add_In_l. apply add_In_x. }
        apply next_gate_preserves_structure in ng.
        rewrite ng.
        apply IHn in subc.
        rewrite subc.
        rewrite (cons_to_app _ p2).
        repeat rewrite <- app_assoc.
        apply app_congruence; try reflexivity.
        repeat rewrite app_assoc.
        apply app_congruence; try reflexivity.
        rewrite does_not_reference_commutes_app2; try assumption.
        reflexivity.
    + dependent destruction p.
Qed.

Lemma get_subcircuit_l1_does_not_reference : forall {dim} (l : PI4_list dim) q l1 s l2,
  get_subcircuit l q = (l1, s, l2) ->
  does_not_reference l1 q = true.
Proof.
  intros dim l q l1 s l2 H.
  unfold get_subcircuit in H.
  eapply get_subcircuit'_l1_does_not_reference in H.
  apply H.
  left; reflexivity.
Qed.

Lemma get_subcircuit_preserves_semantics : forall {dim} (l : PI4_list dim) q l1 s l2,
  get_subcircuit l q = (l1, s, l2) ->
  l =l= l1 ++ s ++ l2.
Proof. 
  intros dim l q l1 s l2 H.
  unfold get_subcircuit in H.
  eapply get_subcircuit'_preserves_semantics in H.
  assumption.
Qed.

(* Examples *)

Definition test1 : PI4_list 1 := T 0 :: H 0 :: [].
Definition test2 : PI4_list 2 := T 0 :: CNOT 0 1 :: H 0 :: T 1 :: H 1 :: [].
Definition test3 : PI4_list 3 := T 0 :: H 1 :: H 2 :: X 1 :: CNOT 0 2 :: T 0 :: X 2 :: CNOT 2 1 :: H 1 :: T 2 :: [].
Definition test4 : PI4_list 3 := T 1 :: T 2 :: CNOT 1 0 :: T 0 :: CNOT 1 2 :: CNOT 0 1 :: H 2 :: CNOT 1 2 :: CNOT 0 1 :: T 1 :: H 0 :: H 1 :: [].

(* Result: l1 = [], s = [T 0], l2 = [H 0] *)
Compute (get_subcircuit test1 O). 
(* Result: l1 = [], s = [T 0; CNOT 0 1; T 1], l2 = [H 0; H 1] *)
Compute (get_subcircuit test2 0).
(* Result: l1 = [T 0], s = [CNOT 0 1; T 1], l2 = [H 0; H 1] *)
Compute (get_subcircuit test2 1).
(* Result: l1 = [H 1; H 2; X 1]
           s = [T 0; CNOT 0 2; T 0; X 2; CNOT 2 1; T 2]
           l2 = [H 1] *)
Compute (get_subcircuit test3 0).
(* Result: l1 = [T 0]
           s = []
           l2 = [H 1; H 2; X 1; CNOT 0 2; T 0; X 2; CNOT 2 1; H 1; T 2] *)
Compute (get_subcircuit test3 1).
(* Result: l1 = [T 1; T 2]
           s = [CNOT 1 0; T 0; CNOT 1 2; CNOT 0 1]
           l2 = [H 2; CNOT 1 2; CNOT 0 1; T 1; H 0; H 1] *)
Compute (get_subcircuit test4 0).
(* Result: l1 = [T 2]
           s = [T 1; CNOT 1 0; T 0; CNOT 1 2; CNOT 0 1]
           l2 = [H 2; CNOT 1 2; CNOT 0 1; T 1; H 0; H 1] *)
Compute (get_subcircuit test4 1).
(* Result: l1 = [T 1; CNOT 1 0; T 0]
           s = [T 2; CNOT 1 2; CNOT 0 1]
           l2 = [H 2; CNOT 1 2; CNOT 0 1; T 1; H 0; H 1] *)
Compute (get_subcircuit test4 2).

(** Merge a single rotation gate. **)

(* To perform rotation merging, we will need to keep track of the current 
   (boolean) state of each qubit. We will do this using the (nat -> A) type
   defined in core/Utilities.v. Because we are considering {CNOT, X, Rz}
   subcircuits, we only need to consider boolean expressions of the form
   x ⊕ y ⊕ ... ⊕ 1, where each term in the XOR is optional.  

   To represent a boolean expression, we use (nat -> bool) w/ upper bound N.
   - For i <= N - 1, the element at index i indicates whether variable
     i is involved in the XOR. The element at index N indicates whether
     the XOR includes a 1 term (i.e. is negated).

   To represent a list of boolean functions, we use (nat -> (nat -> bool))
   w/ upper bound (N - 1).
   - The element at index i describes the current boolean function on
     qubit i. 
*)

(* Check for equality of two functions, up to (n - 1). *)
Fixpoint f_eqb {A} (f1 f2 : nat -> A) (eq : A -> A -> bool) n := 
  match n with
  | O => true
  | S n' => eq (f1 n') (f2 n') && (f_eqb f1 f2 eq n')
  end.

(* Negate a boolean expression. *)
Definition neg f dim :=
  fun i => if i =? dim then negb (f i) else (f i).

(* Compute the XOR of two boolean expressions. *)
Definition xor f1 f2 :=
  fun (i : nat) => xorb (f1 i) (f2 i).

(* s = {CNOT, X, Rx} subcircuit
   k = phase of original rotation gate
   q = target of original rotation gate
   f = list of boolean function applied to every qubit *)
Fixpoint merge' {dim} (s : PI4_list dim) k q f :=
  match s with
  | (App1 UPI4_X q') :: t => 
      let f' := update f q' (neg (f q') dim) in
      match merge' t k q f' with
      | Some l => Some (App1 UPI4_X q' :: l)
      | _ => None
      end
  | (App1 (UPI4_PI4 k') q') :: t =>
      if f_eqb (f q') (fun x => if x =? q then true else false) eqb (dim + 1)
      then let k'' := (k + k')%Z in
           if (k'' =? 8)%Z then Some t 
           else if (k'' <? 8)%Z then Some (App1 (UPI4_PI4 k'') q' :: t)
                else Some (App1 (UPI4_PI4 (k'' - 8)%Z) q' :: t) 
      else match merge' t k q f with
           | Some l => Some (App1 (UPI4_PI4 k') q' :: l)
           | _ => None
           end
  | (App2 UPI4_CNOT q1 q2) :: t =>
      let f' := update f q2 (xor (f q1) (f q2)) in
      match merge' t k q f' with
      | Some l => Some (App2 UPI4_CNOT q1 q2 :: l)
      | _ => None
      end
  | _ => None
  end.

Definition merge {dim} (s : PI4_list dim) k q :=
  let finit := fun i => fun j => if j =? i then true else false in
  merge' s k q finit.

(* Proofs *)

Lemma equal_on_basis_states_implies_equal : forall {dim} (A B : Square (2 ^ dim)),
  WF_Matrix A -> (* WF may or may not be necessary *)
  WF_Matrix B ->
  (forall f, A × (f_to_vec 0 dim f) = B × (f_to_vec 0 dim f)) ->
  A = B.
Proof.
  intros dim A B WFA WFB H.
  prep_matrix_equality.
  unfold WF_Matrix in *.
  unfold Mmult in H.
 Admitted.

(* Convert from our representation of a boolean expression (b) to
   an actual boolean expression, using the mapping from variables
   to boolean values given in f. *)
Fixpoint get_boolean_expr' (b : nat -> bool) f n :=
  match n with
  | 0 => false
  | S n' => if (b n') 
           then xorb (f n') (get_boolean_expr' b f n')
           else get_boolean_expr' b f n'
  end.

Definition get_boolean_expr (b : nat -> (nat -> bool)) f n :=
  fun i =>
    if (b i n) 
    then negb (get_boolean_expr' (b i) f n)
    else get_boolean_expr' (b i) f n.

Lemma get_boolean_expr_update_neg : forall dim b f n,
  get_boolean_expr (update b n (neg (b n) dim)) f dim =
  update (get_boolean_expr b f dim) n (¬ (get_boolean_expr b f dim n)).
Proof. 
  intros.
  apply functional_extensionality.
  intros x.
  unfold get_boolean_expr, update, neg.
  bdestruct (x =? n).
  - subst.
    bdestructΩ (dim =? dim).
    assert (H1: forall f1 f2 f n, (forall i, (i < n)%nat -> f1 i = f2 i) -> 
                get_boolean_expr' f1 f n = get_boolean_expr' f2 f n).
    { clear. intros.
      induction n; try reflexivity.
      simpl.
      rewrite H; try lia.
      destruct (f2 n);
      rewrite IHn; try reflexivity;
      intros; apply H; lia. }      
    destruct (b n dim) eqn:bvn; simpl.
    + rewrite negb_involutive.
      apply H1.
      intros.
      bdestructΩ (i =? dim); reflexivity.
    + erewrite H1; try reflexivity.
      intros.
      bdestructΩ (i =? dim); reflexivity.
  - destruct (b x dim); reflexivity.
Qed.

Lemma get_boolean_expr'_xor : forall b1 b2 f n,
  get_boolean_expr' (xor b1 b2) f n = xorb (get_boolean_expr' b1 f n) (get_boolean_expr' b2 f n) .
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    unfold xor. 
    destruct (b1 n) eqn:b1n; destruct (b2 n) eqn:b2n; simpl.
    + rewrite xorb_assoc. 
      rewrite <- (xorb_assoc _ (f n)).
      rewrite (xorb_comm _ (f n)).
      repeat rewrite <- xorb_assoc. 
      rewrite xorb_nilpotent.
      rewrite xorb_false_l.
      apply IHn.
    + rewrite xorb_assoc.
      rewrite <- IHn.
      reflexivity.
    + rewrite <- xorb_assoc.
      rewrite (xorb_comm _ (f n)).
      rewrite xorb_assoc.
      rewrite <- IHn.
      reflexivity.
    + apply IHn.
Qed.

Lemma get_boolean_expr_update_xor : forall dim b f n1 n2,
  get_boolean_expr (update b n1 (xor (b n2) (b n1))) f dim =
  update (get_boolean_expr b f dim) n1
         (get_boolean_expr b f dim n1 ⊕ get_boolean_expr b f dim n2).
Proof.
  intros.
  apply functional_extensionality.
  intros x.
  replace (xor (b n2) (b n1)) with (xor (b n1) (b n2)).
  2: { unfold xor; apply functional_extensionality; intros.
       apply xorb_comm. }
  unfold get_boolean_expr, update, xor.
  bdestruct (x =? n1).
  - destruct (b n1 dim) eqn:bn1; destruct (b n2 dim) eqn:bn2; simpl.
    + rewrite xorb_negb_negb.
      apply get_boolean_expr'_xor.
    + rewrite <- negb_xorb_l. 
      rewrite <- get_boolean_expr'_xor.
      reflexivity.
    + rewrite <- negb_xorb_r. 
      rewrite <- get_boolean_expr'_xor.
      reflexivity.
    + apply get_boolean_expr'_xor.
  - reflexivity.
Qed.

Lemma f_eqb_eq : forall {A} (f1 f2 : nat -> A) (eq: A -> A -> bool) n,
  (forall x y, reflect (x = y) (eq x y)) ->
  f_eqb f1 f2 eq n = true -> 
  forall x, (x < n)%nat -> f1 x = f2 x.
Proof.
  intros A f1 f2 eq n Href H x Hx.
  induction n; try lia.
  simpl in H. 
  apply andb_prop in H as [H1 H2].
  bdestruct (x =? n).
  - subst.
    eapply reflect_iff in Href.
    apply Href; assumption.
  - apply IHn; try assumption.
    lia.
Qed.

Lemma f_eqb_same : forall {A} (f : nat -> A) (eq: A -> A -> bool) n,
  (forall x y, reflect (x = y) (eq x y)) ->
  f_eqb f f eq n = true.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl. apply andb_true_intro.
    split. eapply reflect_iff in X.
    apply X; reflexivity.
    assumption.
Qed.

Lemma get_boolean_expr'_finit_q_large : forall b f n q,
  let finit := fun x : nat => if x =? q then true else false in
  (q >= n)%nat ->
  (forall x, (x < n)%nat -> b x = finit x) ->
  get_boolean_expr' b f n = false.
Proof.
  intros.
  induction n; try reflexivity.
  subst finit; simpl in *.
  destruct q; try lia.
  destruct (b n) eqn:bn.
  rewrite H0 in bn; try lia.
  bdestruct (n =? S q); [lia | discriminate].
  apply IHn; try lia.  
  intros. apply H0. lia.
Qed.

Lemma get_boolean_expr_finit : forall dim b f n q,
  let finit := fun x : nat => if x =? q then true else false in
  (q < dim)%nat ->
  f_eqb (b n) finit eqb (dim + 1) = true ->
  get_boolean_expr b f dim n = f q.
Proof.
  intros.
  unfold get_boolean_expr.
  assert (forall x y : bool, reflect (x = y) (eqb x y)) by apply eqb_spec.
  specialize (f_eqb_eq _ _ _ _ H1 H0) as feqb.
  clear - H feqb.
  subst finit; simpl in *.
  destruct (b n dim) eqn:bn.
  - rewrite feqb in bn; try lia.
    bdestruct (dim =? q); [lia | discriminate].
  - clear bn.
    induction dim; try lia.
    simpl.
    destruct (b n dim) eqn:bndim.
    + rewrite feqb in bndim; try lia.
      bdestruct (dim =? q); try discriminate; subst.
      erewrite get_boolean_expr'_finit_q_large.
      apply xorb_false_r.
      2: { intros. apply feqb. lia. }
      lia.
    + rewrite feqb in bndim; try lia. 
      bdestruct (dim =? q); try discriminate.
      apply IHdim.
      lia.
      intros. apply feqb. lia.
Qed.

Lemma merge'_preserves_semantics_on_basis_vecs : forall {dim} (s : PI4_list dim) k q b l' f,
  (q < dim)%nat ->
  uc_well_typed_l s ->
  merge' s k q b = Some l' ->
  let A := uc_eval (list_to_ucom (PI4_to_base_l l')) in
  let B := uc_eval (list_to_ucom (PI4_to_base_l s)) in
  let v := f_to_vec 0 dim (get_boolean_expr b f dim) in
  A × v = (Cexp (f q * (IZR k * PI / 4))) .* B × v.
Proof.
  intros dim s k q b l' f Hq WT H A B v.
  subst A B v.
  generalize dependent l'.
  generalize dependent b.
  induction s; try discriminate.
  intros b l' H.
  simpl in H.
  destruct a.
  - dependent destruction p; try discriminate.
    + destruct (merge' s k q (update b n (neg (b n) dim))) eqn:mer; try discriminate.
      inversion H; inversion WT; subst.
      apply (IHs H5) in mer.
      rewrite get_boolean_expr_update_neg in mer.
      simpl PI4_to_base_l; simpl list_to_ucom.
      replace (uapp1 (U_R PI 0 PI) n) with (@SQIRE.X dim n) by reflexivity.
      simpl.
      rewrite Mscale_mult_dist_l.
      repeat rewrite Mmult_assoc.
      rewrite f_to_vec_X; try assumption.
      rewrite mer.
      repeat rewrite Mscale_mult_dist_l.
      reflexivity.
    + simpl PI4_to_base_l; simpl list_to_ucom. 
      replace (uapp1 (U_R 0 0 (IZR k * PI / 4)) n) with (@SQIRE.Rz dim (IZR k * PI / 4) n) by reflexivity.
      simpl.
      rewrite Mscale_mult_dist_l.
      repeat rewrite Mmult_assoc.
      inversion WT; subst.
      rewrite f_to_vec_Rz; try assumption.
      rewrite Mscale_mult_dist_r.
      rewrite Mscale_assoc.
      destruct (f_eqb (b n) (fun x : nat => if x =? q then true else false) eqb (dim + 1)) eqn:feqb.
      * destruct (k0 + k =? 8)%Z eqn:k0k8;
        [ | destruct (k0 + k <? 8)%Z eqn:k0k];
        inversion H; subst;
        simpl PI4_to_base_l; simpl list_to_ucom.
        2: replace (uapp1 (U_R 0 0 (IZR (k0 + k) * PI / 4)) n) with (@SQIRE.Rz dim (IZR (k0 + k) * PI / 4) n) by reflexivity.
        3: replace (uapp1 (U_R 0 0 (IZR (k0 + k - 8) * PI / 4)) n) with (@SQIRE.Rz dim (IZR (k0 + k - 8) * PI / 4) n) by reflexivity.
        2, 3: simpl; repeat rewrite Mmult_assoc; rewrite f_to_vec_Rz; try assumption.
        2, 3: rewrite Mscale_mult_dist_r.
        all: eapply get_boolean_expr_finit in feqb; 
             try assumption;
             rewrite feqb;
             rewrite <- Cexp_add.
        all: repeat rewrite <- Rmult_div_assoc;
             rewrite <- Rmult_plus_distr_l;
             rewrite <- Rmult_plus_distr_r.
        all: repeat rewrite <- Rmult_div_assoc; 
             rewrite <- plus_IZR.
        rewrite Z.eqb_eq in k0k8.
        rewrite k0k8.
        replace (8 * (PI / 4))%R with (2 * PI)%R by lra.
        destruct (f q); simpl; autorewrite with R_db; autorewrite with Cexp_db;
        Msimpl_light; reflexivity.
        reflexivity.
        apply f_equal2; try reflexivity. 
        rewrite minus_IZR.
        unfold Rminus.
        rewrite Rmult_plus_distr_r.
        rewrite Rmult_plus_distr_l.
        replace (- (8) * (PI / 4))%R with (-(2 * PI))%R by lra.
        rewrite Cexp_add.
        destruct (f q); simpl;
        repeat rewrite Rmult_0_l;
        repeat rewrite Rmult_1_l.
        rewrite Cexp_neg, Cexp_2PI.
        lca. 
        rewrite Cexp_0. lca.
      * destruct (merge' s k0 q b) eqn:mer; try discriminate.
        inversion H; subst.
        apply (IHs H4) in mer.
        simpl PI4_to_base_l; simpl list_to_ucom.
        replace (uapp1 (U_R 0 0 (IZR k * PI / 4)) n) with (@SQIRE.Rz dim (IZR k * PI / 4) n) by reflexivity.
        simpl.
        repeat rewrite Mmult_assoc.
        rewrite f_to_vec_Rz; try assumption.
        rewrite Mscale_mult_dist_r.
        rewrite mer.
        rewrite Mscale_mult_dist_l.
        rewrite Mscale_assoc.
        apply f_equal2; try reflexivity.
        lca.
  - dependent destruction p.
    destruct (merge' s k q (update b n0 (xor (b n) (b n0)))) eqn:mer; try discriminate.
      inversion H; inversion WT; subst.
      apply (IHs H8) in mer.
      rewrite get_boolean_expr_update_xor in mer.
      simpl PI4_to_base_l; simpl list_to_ucom.
      replace (uapp2 U_CNOT n n0) with (@SQIRE.CNOT dim n n0) by reflexivity.
      simpl.
      rewrite Mscale_mult_dist_l.
      repeat rewrite Mmult_assoc.
      rewrite f_to_vec_CNOT; try assumption.
      rewrite mer.
      repeat rewrite Mscale_mult_dist_l.
      reflexivity.
  - dependent destruction p.
Qed.

(* TODO: move to Utilities *)
Lemma f_to_vec_eq : forall f1 f2 base dim,
  (forall x, (x < base + dim)%nat -> f1 x = f2 x) ->
  f_to_vec base dim f1 = f_to_vec base dim f2.
Proof.
  intros.
  induction dim; try reflexivity.
  simpl.  
  rewrite H; try lia.
  rewrite IHdim. 
  reflexivity.
  intros.
  apply H; lia.
Qed.

Lemma merge_preserves_semantics : forall {dim} (s : PI4_list dim) k q l',
  uc_well_typed_l (App1 (UPI4_PI4 k) q :: s) ->
  merge s k q = Some l' ->
  l' =l= App1 (UPI4_PI4 k) q :: s.
Proof.
  intros dim s k q l' WT H.
  inversion WT; subst.
  unfold merge in H.
  unfold uc_equiv_l, uc_equiv.
  eapply equal_on_basis_states_implies_equal; auto with wf_db.
  intros f.
  remember (fun i j : nat => if j =? i then true else false) as finit.
  assert (forall x, (x < dim)%nat -> get_boolean_expr finit f dim x = f x).
  { clear - Heqfinit.
    intros.
    apply get_boolean_expr_finit; try assumption.
    subst finit; simpl. apply f_eqb_same.
    apply eqb_spec. }
  assert (f_to_vec 0 dim f = f_to_vec 0 dim (get_boolean_expr finit f dim)).
  { clear - Heqfinit H0.
    apply f_to_vec_eq.
    intros.
    symmetry; apply H0; lia. } 
  rewrite H1. 
  simpl PI4_to_base_l; simpl list_to_ucom.
  replace (uapp1 (U_R 0 0 (IZR k * PI / 4)) q) with (@SQIRE.Rz dim (IZR k * PI / 4) q) by reflexivity.
  simpl.
  repeat rewrite Mmult_assoc.
  rewrite f_to_vec_Rz; try assumption.
  rewrite Mscale_mult_dist_r.
  rewrite <- Mscale_mult_dist_l.
  rewrite H0; try assumption.
  apply merge'_preserves_semantics_on_basis_vecs; assumption.
Qed.

(* Examples *)

Definition test5 : PI4_list 3 := CNOT 0 2 :: T 0 :: X 2 :: CNOT 2 1 :: T 2 :: [].

(* Result: Some [CNOT 0 2; P 0; X 2; CNOT 2 1; T 2] *)
Compute (merge test5 1 0).

(** Final optimization definition. **)

Definition merge_rotation {dim} (l : PI4_list dim) k q :=
  let (tmp, l2) := get_subcircuit l q in
  let (l1, s) := tmp in
  match merge s k q with
  | Some s' => Some (l1 ++ s' ++ l2)
  | _ => None
  end.

Fixpoint merge_rotations' {dim} (l : PI4_list dim) n :=
  match n with
  | O => l
  | S n' => match l with
           | [] => []
           | App1 (UPI4_PI4 k) q :: t =>
               match merge_rotation t k q with
               | None => App1 (UPI4_PI4 k) q :: (merge_rotations' t n') 
               | Some l' => merge_rotations' l' n'
               end
           | g :: t => g :: (merge_rotations' t n')
           end
  end.

Definition merge_rotations {dim} (l : PI4_list dim) := 
  merge_rotations' l (List.length l).

(* Proofs *)

Lemma merge_rotation_preserves_semantics : forall {dim} (l : PI4_list dim) k q l',
  (q < dim)%nat ->
  uc_well_typed_l l ->
  merge_rotation l k q = Some l' ->
  l' =l= App1 (UPI4_PI4 k) q :: l.
Proof.
  intros dim l k q l' Hq WT H.
  unfold merge_rotation in H. 
  destruct (get_subcircuit l q) eqn:subc.
  destruct p.
  destruct (merge p1 k q) eqn:mer; try discriminate.
  specialize (get_subcircuit_l1_does_not_reference _ _ _ _ _ subc) as dnr.
  apply get_subcircuit_preserves_semantics in subc.
  apply merge_preserves_semantics in mer.
  2: { constructor; try assumption.
       apply (uc_equiv_l_implies_WT _ _ subc) in WT. 
       apply uc_well_typed_l_app in WT as [_ WT].
       apply uc_well_typed_l_app in WT as [WT _].
       assumption. }
  inversion H; subst.
  rewrite subc.
  rewrite mer.
  rewrite app_comm_cons.
  rewrite (cons_to_app _ p1).
  rewrite (cons_to_app _ p).
  rewrite (does_not_reference_commutes_app1 _ _ _ dnr).
  repeat rewrite app_assoc.
  reflexivity.
Qed.   

Lemma merge_rotations_preserves_semantics : forall {dim} (l : PI4_list dim),
  uc_well_typed_l l ->
  merge_rotations l =l= l.
Proof.
  intros.
  unfold merge_rotations.
  (* the value of n is unimportant for correctness *)
  remember (length l) as n; clear Heqn. 
  generalize dependent l.
  induction n; try reflexivity.
  intros. simpl.
  destruct l; try reflexivity.
  inversion H; subst.
  dependent destruction u. 
  all: try (rewrite IHn; try assumption; reflexivity).
  destruct (merge_rotation l k n0) eqn:mr.
  2: rewrite IHn; try assumption; reflexivity.
  apply merge_rotation_preserves_semantics in mr; try assumption.
  rewrite IHn.
  apply mr.
  eapply uc_equiv_l_implies_WT. 
  symmetry in mr; apply mr.
  constructor; assumption.
Qed.

(* Examples *)

Definition test6 : PI4_list 4 := T 3 :: CNOT 0 3 :: P 0 :: CNOT 1 2 :: CNOT 0 1 :: TDAG 2 :: T 0 :: CNOT 1 2 :: CNOT 2 1 :: TDAG 1 :: CNOT 3 0 :: CNOT 0 3 :: T 0 :: T 3 :: [].
Definition test7 : PI4_list 2 := T 1 :: CNOT 0 1 :: Z 1 :: CNOT 0 1 :: Z 0 :: T 1 :: CNOT 1 0 :: [].
Definition test8 : PI4_list 4 := CNOT 2 3 :: T 0 :: T 3 :: CNOT 0 1 :: CNOT 2 3 :: CNOT 1 2 :: CNOT 1 0 :: CNOT 3 2 :: CNOT 1 2 :: CNOT 0 1 :: T 2 :: TDAG 1 :: [].

(* Result: [CNOT 1 2; CNOT 0 3; CNOT 0 1; CNOT 1 2; CNOT 2 1; PDAG 1; CNOT 3 0; CNOT 0 3; P 0; Z 3] *)
Compute (merge_rotations test6).
(* Result: [CNOT 0 1; Z 1; CNOT 0 1; Z 0; P 1; CNOT 1 0] *)
Compute (merge_rotations test7).
(* Result: [CNOT 2 3 ; CNOT 0 1 ; CNOT 2 3 ; CNOT 1 2 ; CNOT 1 0 ; CNOT 3 2 ; CNOT 1 2 ; CNOT 0 1 ; P 2] *)
Compute (merge_rotations test8).