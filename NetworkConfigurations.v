Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.

Section Node.
  Variable Node : Set.

  Record flow := {
    Src : Node;
    Dest : Node
  }.

  Definition network_topology := Node -> Node -> Prop.

  Definition network_policy := flow -> bool.

  Definition next_node := Node -> Node -> Node -> Prop.

  Fixpoint is_next_node_path (next : next_node) path src dest :=
    match path with
    | nil => src = dest
    | cons hop_target cdr =>
        next src dest hop_target /\
        is_next_node_path next cdr hop_target dest
    end.

  Record next_node_valid (topology : network_topology) (policy : network_policy) (next : next_node) := {
    all_hops_in_topology : forall src dest hop_target,
      next src dest hop_target -> topology src hop_target;

    path_exists_for_valid_flows : forall flow,
      policy flow = true
        -> exists path, is_next_node_path next path flow.(Src) flow.(Dest);

    no_black_holes : forall src dest hop_target,
      next src dest hop_target
        -> exists path, is_next_node_path next path hop_target dest;

    all_paths_acyclic : forall node path,
      is_next_node_path next path node node -> path = nil
  }.

  Fixpoint is_path_in_topology (topology : network_topology) src dest path :=
    match path with
    | nil => src = dest
    | cons hop_target cdr =>
      topology src hop_target /\
      is_path_in_topology topology hop_target dest cdr
    end.

  Record behaved_topology (topology : network_topology) := {
    connected : forall n1 n2,
      exists path, is_path_in_topology topology n1 n2 path;
    undirected : forall n1 n2,
      topology n1 n2 -> topology n2 n1;
    no_self_loops : forall n,
      ~topology n n;
  }.

  Fixpoint contains_no_duplicates {A} (l : list A) :=
    match l with
    | nil => True
    | cons car cdr => ~In car cdr /\ contains_no_duplicates cdr
    end.

  Definition next_node_generator := network_topology -> network_policy -> next_node.

  Definition next_node_generator_valid (generator : next_node_generator) (topology_filter : network_topology -> Prop) := forall topology policy,
    topology_filter topology
      -> next_node_valid topology policy (generator topology policy).

  Record is_spanning_tree (topology reduced_topology : network_topology) := {
    is_subgraph : forall n1 n2,
      reduced_topology n1 n2 -> topology n1 n2;
    is_tree : forall src dest,
      exists! path,
        is_path_in_topology reduced_topology src dest path /\
        contains_no_duplicates (cons src path)
  }.

  Definition spanning_tree_next_node_generator' topology (_ : network_policy) src dest target :=
    exists path,
      is_path_in_topology topology src dest path /\
      contains_no_duplicates (src :: path) /\
      match path with
      | nil => False
      | car :: _ => car = target
      end.

  Lemma spanning_tree_next_node_generator'_valid : forall topology reduced_topology policy,
    is_spanning_tree topology reduced_topology
      -> next_node_valid reduced_topology policy (spanning_tree_next_node_generator' reduced_topology policy).
  Proof.
    intros.
    constructor; intros.
    unfold spanning_tree_next_node_generator' in H0.
    destruct H0.
    destruct H0.
    destruct H1.
    destruct x.
    tauto.
    subst.
    simpl in H0.
    destruct H0.
    assumption.
    destruct flow0.
    simpl.
    apply is_tree with (src := Src0) (dest := Dest0) in H.
    destruct H.
    unfold unique in H.
    apply proj1 in H.
    destruct H.
    exists x.
    clear H0.
    dependent induction x generalizing Src0.
    assumption.
    simpl.
    constructor.
    exists (cons a x).
    tauto.
    simpl in H, H1.
    apply IHx; simpl; tauto.
    apply is_tree with (src := src) (dest := dest) in H.
    unfold spanning_tree_next_node_generator' in H0.
    destruct H0.
    destruct H0.
    destruct H1.
    destruct x.
    tauto.
    subst.
    exists x.
    destruct H.
    destruct H.
    destruct H.
    clear H2.
    simpl in H0, H1.
    destruct H0, H1.
    clear H0.
    dependent induction x generalizing hop_target.
    simpl in H2.
    simpl.
    assumption.
    simpl.
    constructor.
    exists (cons a x).
    constructor; try assumption.
    constructor; try assumption.
    reflexivity.
    simpl in H4.
    destruct H4.
    destruct H4.
    simpl in H2.
    destruct H2.
    apply IHx; try tauto.
    unfold not.
    intros.
    destruct H7; subst.
    apply H1.
    simpl.
    tauto.
    apply H1.
    simpl.
    tauto.
    apply is_tree with (src := node) (dest := node) in H.
    destruct H.
    assert (x = nil).
    unfold unique in H.
    destruct H.
    apply H1.
    constructor.
    constructor.
    simpl.
    tauto.
    subst.
    simpl in H.
    destruct path; try reflexivity.
    exfalso.
    simpl in H0.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H2.
    unfold unique in H.
    destruct H.
    assert (nil = x); subst; try tauto.
    destruct x; try tauto.
    subst.
    simpl in H0.
    apply H4.
    constructor; assumption.
  Qed.

  Lemma next_node_subgraph_weakening : forall (sparse_topology dense_topology : network_topology) policy next,
    next_node_valid sparse_topology policy next
      -> (forall n1 n2, sparse_topology n1 n2 -> dense_topology n1 n2)
      -> next_node_valid dense_topology policy next.
  Proof.
    intros.
    destruct H.
    constructor; eauto.
  Qed.

  Variable make_spanning_tree : network_topology -> network_topology.

  Definition spanning_tree_generator_valid topology_filter := forall topology,
    topology_filter topology -> is_spanning_tree topology (make_spanning_tree topology).

  Definition spanning_tree_next_node_generator topology policy :=
    spanning_tree_next_node_generator' (make_spanning_tree topology) policy.

  Theorem spanning_tree_next_node_generator_valid (topology_filter : network_topology -> Prop) :
    spanning_tree_generator_valid topology_filter
      -> next_node_generator_valid spanning_tree_next_node_generator topology_filter.
  Proof.
    unfold next_node_generator_valid, spanning_tree_next_node_generator.
    intros.
    assert (H' := H0).
    apply H in H0.
    apply next_node_subgraph_weakening with (sparse_topology := make_spanning_tree topology).
    apply spanning_tree_next_node_generator'_valid with (topology := topology); eauto.
    apply is_subgraph; assumption.
  Qed.
End Node.

Require Import ZArith.
Section NetworkExample.
  Local Inductive ExampleVertex :=
  | A
  | B
  | C
  | D
  .

  (*
    example_topology:

        B
      / | \
     A  |  D
      \ | /
        C
  *)
  Local Definition example_topology n1 n2 :=
    match (n1, n2) with
    | (A, B) | (B, A) => True
    | (A, C) | (C, A) => True
    | (B, C) | (C, B) => True
    | (B, D) | (D, B) => True
    | (C, D) | (D, C) => True
    | _ => False
    end.

  (*
    example_spanning_tree:

        B
      /   \
     A     D
      \
        C
  *)

  Local Definition example_spanning_tree n1 n2 :=
    match (n1, n2) with
    | (A, B) | (B, A) => True
    | (A, C) | (C, A) => True
    | (B, D) | (D, B) => True
    | _ => False
    end.

  Local Definition make_example_spanning_tree (_ : network_topology ExampleVertex) := example_spanning_tree.

  Local Definition example_policy (_ : flow ExampleVertex) := true.

  Local Definition next : next_node ExampleVertex :=
    spanning_tree_next_node_generator ExampleVertex make_example_spanning_tree example_topology example_policy.

  Ltac t := match goal with
  | [ n : ExampleVertex |- False ] => destruct n
  | [ Hx : _ -> False |- False ] => apply Hx
  | [ n : ExampleVertex |- ?n = ?n \/ _ ] => apply or_introl; reflexivity
  | [ n : ExampleVertex |- _ \/ _ ] => apply or_intror
  | [ Hx : _ |- In _ _ ] => exfalso
  end.

  Lemma long_paths_have_duplicates : forall (path : list ExampleVertex),
    length path < 5 \/ ~contains_no_duplicates path.
  Proof.
    intros.
    destruct path.
    apply or_introl; simpl; omega.
    destruct path.
    apply or_introl; simpl; omega.
    destruct path.
    apply or_introl; simpl; omega.
    destruct path.
    apply or_introl; simpl; omega.
    destruct path.
    apply or_introl; simpl; omega.
    apply or_intror.
    unfold contains_no_duplicates.
    unfold not.
    intros.
    simpl in H.
    destruct e, e0, e1, e2, e3; tauto.
  Qed.

  Definition get_example_path n1 n2 :=
    match (n1, n2) with
    | (A, A) | (B, B) | (C, C) | (D, D) => nil
    | (A, B) | (D, B) => cons B nil
    | (C, B) => cons A (cons B nil)
    | (B, A) | (C, A) => cons A nil
    | (D, A) => cons B (cons A nil)
    | (A, C) => cons C nil
    | (B, C) => cons A (cons C nil)
    | (D, C) => cons B (cons A (cons C nil))
    | (B, D) => cons D nil
    | (A, D) => cons B (cons D nil)
    | (C, D) => cons A (cons B (cons D nil))
    end.

  Lemma negation_distribution : forall (P1 P2 : Prop), ~(P1 \/ P2) -> ~P1 /\ ~P2.
  Proof.
    tauto.
  Qed.

  Local Theorem validity : next_node_valid ExampleVertex example_topology example_policy next.
  Proof.
    assert (next_node_generator_valid ExampleVertex (fun _ _ => next) (fun t => t = example_topology)); try auto.
    apply spanning_tree_next_node_generator_valid.
    unfold spanning_tree_generator_valid.
    intros.
    unfold make_example_spanning_tree.
    subst.
    constructor.
    intros; destruct n1, n2; try constructor; inversion H.
    intros.
    unfold unique.
    exists (get_example_path src dest).
    apply conj.
    apply conj.
    unfold example_spanning_tree.
    destruct src, dest; simpl; tauto.
    destruct src, dest; simpl; repeat match goal with
    | [ H : _ \/ _ |- _ ] => destruct H
    | [ |- _ /\ _ ] => constructor
    | [ |- ~_ ] => unfold not; intros
    | _ => tauto
    end; discriminate.
    intros.
    destruct H.
    assert (length x' < 5 \/ ~contains_no_duplicates x') by (apply long_paths_have_duplicates).
    simpl in H0.
    destruct H1; try tauto.
    unfold get_example_path.
    unfold is_path_in_topology, example_spanning_tree in H.
    destruct src, dest; repeat match goal with
    | _ => reflexivity
    | _ => discriminate
    | [ H : _ /\ _ |- _ ] => destruct H
    | [ H : ~(_ \/ _) |- _ ] => apply negation_distribution in H
    | [ e : ExampleVertex |- _ ] => destruct e; try tauto
    | [ H : length (_ :: _ :: _ :: _ :: _ :: _) < 5 |- _ ] => simpl in H; omega
    | [ H : contains_no_duplicates (_ :: _) |- _ ] => simpl in H
    | [ H : ~In _ (_ :: _) |- _ ] => simpl in H
    | [ x' : list ExampleVertex |- _ ] => destruct x'
    | _ => tauto
    end.
  Qed.
End NetworkExample.
