Require Export VectorStates.
Require Export Equivalences.
Require Export List.
Open Scope ucom.

Local Close Scope C_scope.
Local Close Scope R_scope.

(* Simplest possible strategy for mapping a program to a CNOT connectivity 
   DAG. When a CNOT occurs between non-adjacent qubits: (1) insert SWAPs to 
   make the qubits adjacent, (2) perform the CNOT, (3) move the qubits back
   to their original locations. In cases where a CNOT is between adjacent
   qubits but in the wrong orientation, insert H gates on the target and
   control. 

   We've chosen to leave the implementation of the CNOT connectivity DAG 
   unspecified. Instead, the mapping algorithm requires two functions:

   - get_path, which returns an undirected path between two nodes in the
     graph; this function must satisfy 
         forall n1 n2, valid_path (get_path n1 n2)

   - is_in_graph, which indicates whether there is a directed edge between 
     two nodes; this function must satisfy
         valid_graph dim is_in_graph
   
   Examples of get_path and is_in_graph for particular graphs can be found
   at the end of the file. *)

(****************************)
(** General Simple Mapping **)
(****************************)

(** Definition **)

(* NOTE: This assumes that paths are oriented from control --> target. *)

Fixpoint do_cnot_along_path dim p : base_ucom dim :=
  match p with
  | n1 :: n2 :: [] => CNOT n1 n2
  | n1 :: ((n2 :: _) as t) => SWAP n1 n2 ; do_cnot_along_path dim t ; SWAP n1 n2
  | _ => SKIP (* bad input case *)
  end.

(* At this point all CNOTs should be between adjacent qubits, but
   they may not respect the direction of the edges in the connectivity
   graph. We can fix this by insert Hadamard gates before and after
   each offending CNOT. *)
Fixpoint fix_cnots {dim} (c : base_ucom dim) (is_in_graph_b : nat -> nat -> bool) :=
  match c with
  | c1; c2 => fix_cnots c1 is_in_graph_b ; fix_cnots c2 is_in_graph_b
  | uapp2 U_CNOT n1 n2 => 
      if is_in_graph_b n1 n2
      then CNOT n1 n2
      else H n1; H n2; CNOT n2 n1; H n1; H n2
  | _ => c
  end.

Fixpoint simple_map {dim} (c : base_ucom dim) (get_path : nat -> nat -> list nat) (is_in_graph_b : nat -> nat -> bool) :=
  match c with
  | c1; c2 => simple_map c1 get_path is_in_graph_b ; 
             simple_map c2 get_path is_in_graph_b
  | uapp2 U_CNOT n1 n2 => let p := do_cnot_along_path dim (get_path n1 n2) in
                         fix_cnots p is_in_graph_b
  | _ => c
  end.

(** Proofs **)

(* Loose formalism for describing paths in a graph - a proper graph 
   library would have more precise definitions. We will represent
   a path between n1 and n2 as a list of nodes with the following 
   properties:
   1. The path must begin with n1.
   2. The path must end with n2.
   3. For every n1' and n2' adjacent in the path, there must exist an 
      undirected edge between n1' and n2'.  
   4. The path does not go through n2 twice.

   Restriction #4 is really just to make the proof easier, we could
   probably remove it. However, if we were defining proper graph-theoretic 
   paths then this restriction would be implied because a path cannot
   go through a vertex multiple times. *)

Inductive begins_with : nat -> list nat -> Prop :=
  | begins_with_cons : forall h t, begins_with h (h :: t).

Inductive ends_with : nat -> list nat -> Prop :=
  | end_with_single_elmt : forall x, ends_with x [x]
  | ends_with_cons : forall x h t, ends_with x t -> ends_with x (h :: t).

Inductive path_is_in_graph : list nat -> (nat -> nat -> Prop) -> Prop :=
  | path_in_graph_two_elmts : forall n1 n2 is_in_graph, 
      (is_in_graph n1 n2) \/ (is_in_graph n2 n1) -> 
      path_is_in_graph (n1 :: n2 :: []) is_in_graph
  | path_in_graph_cons : forall n1 n2 t is_in_graph, 
      (is_in_graph n1 n2) \/ (is_in_graph n2 n1) -> 
      path_is_in_graph (n2 :: t) is_in_graph -> 
      path_is_in_graph (n1 :: n2 :: t) is_in_graph.

Inductive not_in_interior : nat -> list nat -> Prop :=
  | not_in_interior_two_elmts : forall n n1 n2,
      n1 <> n -> not_in_interior n (n1 :: n2 :: [])
  | not_in_interior_cons : forall n n1 n2 t,
      n1 <> n -> 
      not_in_interior n (n2 :: t) ->
      not_in_interior n (n1 :: n2 :: t).

Definition valid_path n1 n2 is_in_graph p :=
  (begins_with n1 p) /\ (ends_with n2 p) 
    /\ (path_is_in_graph p is_in_graph) /\ (not_in_interior n2 p).

Definition get_path_valid dim get_path is_in_graph :=
  forall n1 n2, n1 < dim -> n2 < dim -> n1 <> n2 -> 
           valid_path n1 n2 is_in_graph (get_path n1 n2).

Lemma valid_path_subpath : forall n1 n2 a b is_in_graph p,
  valid_path n1 n2 is_in_graph (n1 :: a :: b :: p) ->
  valid_path a n2 is_in_graph (a :: b :: p).
Proof.
  intros.
  destruct H as [_ [H1 [H2 H3]]].
  split; split; try split. 
  - inversion H1; assumption.
  - inversion H2; assumption.
  - inversion H3; assumption.
Qed.

Fixpoint merge_path (p1 : list nat) p2 :=
  match p1 with
  | [] | [_] => p2
  | h :: t => h :: (merge_path t p2)
  end.

Lemma valid_path_extend_path : forall a n1 n2 (is_in_graph : nat -> nat -> Prop) p,
  n1 <> n2 ->
  is_in_graph n1 a \/ is_in_graph a n1 ->
  valid_path a n2 is_in_graph p ->
  valid_path n1 n2 is_in_graph (n1 :: p).
Proof.
  intros.
  destruct p.
  destruct H1 as [H2 _]; inversion H2.
  destruct p.
  destruct H1 as [_ [_ [_ H2]]]; inversion H2.
  destruct H1 as [H2 [H3 [H4 H5]]].
  inversion H2; subst.
  repeat split; constructor; assumption.
Qed.  

Lemma valid_path_merge_path : forall a b c is_in_graph p1 p2, 
  valid_path a b is_in_graph p1 -> 
  valid_path b c is_in_graph p2 -> 
  not_in_interior c p1 ->
  valid_path a c is_in_graph (merge_path p1 p2).
Proof.
  intros a b c f p1 p2 Hp1 Hp2 NIp1.
  (* Because p1 and p2 are valid paths, we know something about their
     structure. Invert some hypotheses here for use later. *)
  destruct p1; [| destruct p1].
  1, 2: inversion NIp1.
  destruct Hp1 as [H1 [H2 [H3 H4]]].
  inversion H1; subst; clear H1.
  destruct p2.
  destruct Hp2 as [H _]; inversion H.
  destruct Hp2 as [H [H1 [H5 H6]]].
  inversion H; subst; clear H.
  (* now a standard proof by induction *)
  generalize dependent n0.
  generalize dependent n.
  induction p1.
  - intros.
    inversion H2; subst. inversion H7; subst.
    2: inversion H8.
    inversion H3; subst.
    2: inversion H11.
    simpl. 
    repeat split; constructor; try assumption.
    inversion NIp1; assumption.
  - intros.
    replace (merge_path (n :: n0 :: a :: p1) (n1 :: p2)) with (n :: (merge_path (n0 :: a :: p1) (n1 :: p2))) by reflexivity.
    apply valid_path_extend_path with (a:=n0).
    inversion NIp1; assumption.
    inversion H3; assumption.
    apply IHp1.
    inversion H2; assumption.
    inversion H3; assumption.
    inversion H4; assumption.
    inversion NIp1; assumption.
Qed.

(* Restrictions on the structure of the graph to ensure that the chain
   of SWAPs constructed from a path form a well-typed program. If we 
   had defined proper paths (above), then only the n1 < dim and n2 < dim
   constraints would be required. *)
Definition valid_graph dim (is_in_graph : nat -> nat -> Prop) := 
  forall n1 n2, is_in_graph n1 n2 -> (n1 < dim /\ n2 < dim /\ n1 <> n2).

(* Formalisms for describing correct mappings. *)

Inductive respects_constraints_undirected {dim} : (nat -> nat -> Prop) -> base_ucom dim -> Prop :=
  | res_und_seq : forall f c1 c2, 
      respects_constraints_undirected f c1 -> 
      respects_constraints_undirected f c2 -> 
      respects_constraints_undirected f (c1; c2)
  | res_und_app_u : forall f u n, 
      respects_constraints_undirected f (uapp1 u n)
  | res_und_app_cnot : forall (f : nat -> nat -> Prop) n1 n2, 
      f n1 n2 \/ f n2 n1 -> (* undirected *)
      respects_constraints_undirected f (CNOT n1 n2).

Inductive respects_constraints {dim} : (nat -> nat -> Prop) -> base_ucom dim -> Prop :=
  | res_seq : forall f c1 c2, 
      respects_constraints f c1 -> 
      respects_constraints f c2 -> 
      respects_constraints f (c1; c2)
  | res_app_u : forall f u n, 
      respects_constraints f (uapp1 u n)
  | res_app_cnot : forall (f : nat -> nat -> Prop) n1 n2, 
      f n1 n2 -> (* directed *)
      respects_constraints f (CNOT n1 n2).

(* Proof about the relationship between CNOT & SWAP *)

Local Transparent SWAP.
Lemma swap_cnot_control : forall {dim} a b c,
  (* well-typedness constraints *)
  a < dim -> b < dim -> c < dim ->
  a <> b -> b <> c -> a <> c ->
  (* main equivalence *)
  @uc_equiv dim (SWAP a b; CNOT b c; SWAP a b) (CNOT a c).
Proof.
  intros.
  eapply equal_on_basis_states_implies_equal; auto with wf_db.
  intro f.
  unfold SWAP.
  simpl uc_eval.
  repeat rewrite Mmult_assoc.
  repeat rewrite f_to_vec_CNOT by auto.
  repeat (try rewrite update_index_eq; try rewrite update_index_neq by auto).
  repeat rewrite (update_twice_neq _ a) by auto. 
  repeat rewrite update_twice_eq. 
  repeat rewrite (update_twice_neq _ b) by auto.
  rewrite update_twice_eq. 
  rewrite (update_same _ a).
  rewrite (update_same _ b).
  destruct (f a); destruct (f b); reflexivity.
  rewrite update_index_neq by auto.
  destruct (f a); destruct (f b); reflexivity.
  rewrite update_index_neq by auto.
  destruct (f a); destruct (f b); reflexivity.
Qed.

(* Correctness of do_cnot_along_path *)

Local Transparent SWAP CNOT H ID.
Lemma do_cnot_along_path_sound : forall dim n1 n2 is_in_graph p,
  valid_graph dim is_in_graph ->
  valid_path n1 n2 is_in_graph p ->
  @uc_well_typed _ dim (CNOT n1 n2) ->
  do_cnot_along_path dim p ??? CNOT n1 n2.
Proof.
  intros dim n1 n2 is_in_graph p Hgraph Hpath WT.
  generalize dependent n1.
  induction p; intros.
  - (* invalid case: path can't be empty *)
    destruct Hpath as [H1 _].
    inversion H1.
  - destruct p. 
    + (* invalid case: path can't have only one element *)
      destruct Hpath as [_ [_ [H1 _]]].
      inversion H1.
    + simpl; destruct p.
      * (* base case: exactly two elements in the path *)
        destruct Hpath as [H1 [H2 [_ _]]]. 
        inversion H1; subst.
        inversion H2; subst. 
        inversion H3; subst.
        reflexivity. 
        inversion H4.
      * (* inductive case *) 
        inversion Hpath as [H1 Hpath']. 
        destruct Hpath' as [_ [H2 H3]].
        inversion H1; subst.
        inversion WT; subst.
        assert (n < dim).
        { inversion H2; subst.
          destruct H9; apply Hgraph in H; easy. }
        assert (a <> n).
        { inversion H2; subst.
          destruct H10; apply Hgraph in H0; try easy.
          apply not_eq_sym; easy. }
        assert (n <> n2).
        { inversion H3; subst.
          inversion H12; subst; easy. }
        rewrite IHp with (n1:=n).
        apply swap_cnot_control; assumption.    
        apply (valid_path_subpath _ _ _ _ _ _ Hpath).
        constructor; assumption.
Qed.

(* This has roughly the same structure as the soundness proof, but it's
   shorter and relies on fewer assumptions because we don't need to
   worry about well-typedness. *)
Lemma do_cnot_along_path_respects_undirected : forall dim n1 n2 is_in_graph p,
  valid_path n1 n2 is_in_graph p ->
  respects_constraints_undirected is_in_graph (do_cnot_along_path dim p).
Proof.
  intros dim n1 n2 is_in_graph p Hpath.
  generalize dependent n1.
  induction p; intro; try constructor.
  destruct p; try constructor. 
  destruct p; intros Hpath.
  - destruct Hpath as [_ [_ [H1 _]]]. 
    inversion H1; subst.
    constructor; assumption.
    inversion H5.
  - inversion Hpath as [H1 Hpath']. 
    inversion H1; subst.
    destruct Hpath' as [_ [H2 _]].
    inversion H2; subst.
    repeat apply res_und_seq; try apply res_und_app_cnot;
      try assumption;
      try (destruct H5; [right | left]; assumption).
    apply IHp with (n1:=n). 
    apply (valid_path_subpath _ _ _ _ _ _ Hpath).
Qed.

(* Correctness of fix_cnots *)

Lemma fix_cnots_sound : forall dim (c : base_ucom dim) is_in_graph_b,
  fix_cnots c is_in_graph_b ??? c.
Proof.
  intros.
  induction c; try reflexivity; simpl.
  - rewrite IHc1, IHc2. reflexivity.
  - dependent destruction u.
    destruct (is_in_graph_b n n0).
    reflexivity.
    apply H_swaps_CNOT.
Qed.

Lemma fix_cnots_respects_constraints : forall dim (c : base_ucom dim) is_in_graph is_in_graph_b,
  (forall n1 n2, reflect (is_in_graph n1 n2) (is_in_graph_b n1 n2)) ->
  respects_constraints_undirected is_in_graph c ->
  respects_constraints is_in_graph (fix_cnots c is_in_graph_b).
Proof.
  intros.
  induction H0; try constructor.
  apply IHrespects_constraints_undirected1; assumption.
  apply IHrespects_constraints_undirected2; assumption.
  destruct H0; simpl.
  - assert (is_in_graph_b n1 n2 = true).
    { rewrite <- reflect_iff. apply H0. apply H. }
    rewrite H1; simpl.  
    constructor; assumption.
  - bdestruct (is_in_graph_b n1 n2). 
    constructor; assumption. 
    repeat constructor; assumption.
Qed.

(* Correctness of simple_map *)

Lemma simple_map_sound : forall dim (c : base_ucom dim) get_path is_in_graph is_in_graph_b,
  valid_graph dim is_in_graph ->
  get_path_valid dim get_path is_in_graph ->
  (forall n1 n2, reflect (is_in_graph n1 n2) (is_in_graph_b n1 n2)) ->
  uc_well_typed c ->
  simple_map c get_path is_in_graph_b ??? c.
Proof.
  intros.
  induction c; try reflexivity; simpl.
  - inversion H2.
    rewrite IHc1, IHc2; try assumption.
    reflexivity.
  - dependent destruction u.
    rewrite fix_cnots_sound.
    inversion H2; subst.
    eapply do_cnot_along_path_sound.
    apply H.
    apply H0; assumption.
    constructor; assumption.
Qed.

Lemma simple_map_respect_constraints : forall dim (c : base_ucom dim) get_path is_in_graph is_in_graph_b,
  valid_graph dim is_in_graph ->
  get_path_valid dim get_path is_in_graph ->
  (forall n1 n2, reflect (is_in_graph n1 n2) (is_in_graph_b n1 n2)) ->
  uc_well_typed c ->
  respects_constraints is_in_graph (simple_map c get_path is_in_graph_b).
Proof.
  intros.
  induction c; try dependent destruction u; simpl;
  try constructor; inversion H2; subst.  
  apply IHc1; assumption. 
  apply IHc2; assumption.
  apply fix_cnots_respects_constraints; try assumption.
  eapply do_cnot_along_path_respects_undirected.
  apply H0; assumption.
Qed.

