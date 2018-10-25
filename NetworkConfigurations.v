Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import ZArith.

Section Node.
  Variable Node : Set.

  Record flow := {
    Src : Node;
    Dest : Node
  }.

  Definition network_topology := Node -> Node -> Prop.

  Definition network_policy := flow -> bool.

  Definition next_node := Node -> flow -> Node -> Prop.

  Fixpoint is_next_node_path (next : next_node) path here current_flow :=
    match path with
    | nil => here = current_flow.(Dest)
    | cons hop_target cdr =>
        next here current_flow hop_target /\
        is_next_node_path next cdr hop_target current_flow
    end.

  Fixpoint contains_no_duplicates {A} (l : list A) :=
    match l with
    | nil => True
    | cons car cdr => ~In car cdr /\ contains_no_duplicates cdr
    end.

  Record next_node_valid (topology : network_topology) (policy : network_policy) (next : next_node) := {
    all_hops_in_topology : forall here current_flow hop_target,
      next here current_flow hop_target -> topology here hop_target;

    path_exists_only_for_valid_flows : forall current_flow,
      current_flow.(Src) <> current_flow.(Dest)
        -> (policy current_flow = true <-> exists path,
              is_next_node_path next path current_flow.(Src) current_flow);

    no_black_holes : forall src current_flow hop_target,
      next src current_flow hop_target
        -> exists path, is_next_node_path next path hop_target current_flow;

    all_paths_acyclic : forall path here current_flow,
      is_next_node_path next path here current_flow -> contains_no_duplicates (here :: path)
  }.

  Fixpoint is_path_in_topology (topology : network_topology) src dest path :=
    match path with
    | nil => src = dest
    | cons hop_target cdr =>
      topology src hop_target /\
      is_path_in_topology topology hop_target dest cdr
    end.

  Definition next_node_generator := network_topology -> network_policy -> next_node.

  Definition next_node_generator_valid (generator : next_node_generator) := forall topology policy,
    next_node_valid topology policy (generator topology policy).

  Definition all_pairs_paths := Node -> Node -> option (list Node).

  Definition all_pairs_paths_next_node_generator
    (paths : all_pairs_paths)
    (topology : network_topology)
    (policy : network_policy)
    here
    current_flow
    hop_target
  :=
    policy current_flow = true /\
    match paths here current_flow.(Dest) with
    | Some (hop_target' :: _) => hop_target = hop_target'
    | _ => False
    end.

  Record all_pairs_paths_valid paths topology policy := {
    paths_in_topology : forall src dest,
      match paths src dest with
      | Some path => is_path_in_topology topology src dest path
      | _ => True
      end;
    paths_exist_for_valid_flows : forall current_flow,
      policy current_flow = true
        ->
          match paths current_flow.(Src) current_flow.(Dest) with
          | Some _ => True
          | None => False
          end;
    paths_move_closer_to_destination : forall src dest,
      match paths src dest with
      | Some (hop_target :: cdr) =>
        match paths hop_target dest with
        | Some path => length path <= length cdr
        | None => False
        end
      | _ => True
      end
  }.

  Lemma all_pairs_paths_next_node_generator_creates_next_node_paths : forall paths topology policy current_flow hop_target,
    all_pairs_paths_valid paths topology policy
      -> policy current_flow = true
      -> match paths hop_target current_flow.(Dest) with | Some _ => True | None => False end
      -> exists path,
        is_next_node_path (all_pairs_paths_next_node_generator paths topology policy) path hop_target current_flow.
  Proof.
    intros.
    remember (paths hop_target current_flow.(Dest)) as x.
    destruct x; try tauto.
    remember (length l) as len.
    clear H1.
    assert (match paths hop_target current_flow.(Dest) with | Some p => length p <= len | _ => False end) by (rewrite <- Heqx; omega).
    assert (len = 0 -> hop_target = current_flow.(Dest)) by (intros; subst; destruct l; simpl in H2; try omega; eapply paths_in_topology in H; rewrite <- Heqx in H; tauto).
    clear Heqlen.
    clear Heqx.
    dependent induction len generalizing hop_target; try (exists nil; tauto).
    clear H2.
    remember (paths hop_target current_flow.(Dest)) as p.
    destruct p; try tauto.
    destruct l0; try (exists nil; simpl; eapply paths_in_topology in H; rewrite <- Heqp in H; simpl in H; subst; reflexivity).
    assert (H' := H).
    eapply paths_move_closer_to_destination in H; rewrite <- Heqp in H.
    specialize (IHlen n).
    destruct (paths n current_flow.(Dest)); try tauto.
    simpl in H1.
    assert (length l1 <= len) by omega.
    apply IHlen in H2.
    - destruct H2.
      exists (n :: x).
      simpl.
      constructor; try assumption.
      unfold all_pairs_paths_next_node_generator.
      constructor; try assumption.
      rewrite <- Heqp.
      reflexivity.
    - intros.
      assert (length l0 = 0) by omega.
      destruct l0; simpl in H4; try omega.
      eapply paths_in_topology in H'.
      rewrite <- Heqp in H'.
      simpl in H'.
      tauto.
  Qed.

  Fixpoint has_strictly_decreasing_distances (paths : all_pairs_paths) l dest bound :=
    match l with
    | nil => True
    | node :: cdr =>
      match paths node dest with
      | Some l' => length l' < bound /\ has_strictly_decreasing_distances paths cdr dest (length l')
      | None => False
      end
    end.

  Lemma strictly_decreasing_distances_strengthening : forall paths l dest small_bound big_bound,
    has_strictly_decreasing_distances paths l dest small_bound
      -> small_bound <= big_bound
      -> has_strictly_decreasing_distances paths l dest big_bound.
  Proof.
    intros.
    destruct l; simpl; try tauto.
    simpl in H.
    destruct (paths n dest); try tauto.
    destruct H.
    constructor; try tauto; omega.
  Qed.

  Lemma all_pairs_paths_generate_strictly_decreasing_distances : forall (paths : all_pairs_paths) topology policy here current_flow path path',
    all_pairs_paths_valid paths topology policy
      -> paths here current_flow.(Dest) = Some path'
      -> is_next_node_path (all_pairs_paths_next_node_generator paths topology policy) path here current_flow
      -> has_strictly_decreasing_distances paths path current_flow.(Dest) (length path').
  Proof.
    intros.
    dependent induction path generalizing here; try (simpl; tauto).
    simpl.
    simpl in H1.
    destruct H1.
    unfold all_pairs_paths_next_node_generator in H1.
    destruct H1.
    rewrite H0 in H3.
    destruct path'; try tauto.
    subst.
    assert (H' := H).
    eapply paths_move_closer_to_destination in H; rewrite H0 in H.
    remember (paths n current_flow.(Dest)) as p.
    apply eq_sym in Heqp.
    destruct p; try tauto.
    constructor; try (simpl; omega).
    eapply IHpath; eassumption.
  Qed.


  Lemma decreasing_distances_implies_nonmember : forall (paths : all_pairs_paths) path dest node path',
    paths node dest = Some path'
      -> has_strictly_decreasing_distances paths path dest (length path')
      -> ~In node path.
  Proof.
    intros.
    dependent induction path; intros; simpl; try tauto.
    simpl in H0.
    remember (paths a dest) as l.
    destruct l; try tauto.
    destruct H0.
    unfold not.
    intros.
    destruct H2.
    - subst.
      rewrite <- Heql in H.
      injection H.
      intros.
      subst.
      omega.
    - assert (~(In node path)); try tauto.
      assert (length l <= length path') by omega.
      apply strictly_decreasing_distances_strengthening with (big_bound := length path') in H1; try assumption.
      eapply IHpath; eassumption.
  Qed.

  Theorem all_pairs_paths_generator_valid : forall paths topology policy,
    all_pairs_paths_valid paths topology policy
      -> next_node_valid topology policy (all_pairs_paths_next_node_generator paths topology policy).
  Proof.
    intros.
    constructor; intros.
    - unfold all_pairs_paths_next_node_generator in H0.
      destruct H0.
      apply paths_in_topology with (src := here) (dest := current_flow.(Dest)) in H.
      destruct (paths here current_flow.(Dest)); try tauto.
      destruct l; try tauto.
      subst.
      simpl in H.
      tauto.
    - constructor.
      + intros.
        apply all_pairs_paths_next_node_generator_creates_next_node_paths; try assumption.
        eapply paths_exist_for_valid_flows in H; eassumption.
      + intros.
        destruct H1.
        destruct x; simpl in H1; try tauto.
        destruct H1.
        unfold all_pairs_paths_next_node_generator in H1.
        tauto.
    - unfold all_pairs_paths_next_node_generator in H0.
      destruct H0.
      apply all_pairs_paths_next_node_generator_creates_next_node_paths; try tauto.
      remember (paths src current_flow.(Dest)) as p.
      destruct p; try tauto.
      destruct l; try tauto.
      subst.
      eapply paths_move_closer_to_destination in H.
      rewrite <- Heqp in H.
      destruct (paths n current_flow.(Dest)); tauto.
    - dependent induction path; try (simpl; tauto).
      simpl in H0.
      destruct H0.
      unfold all_pairs_paths_next_node_generator in H0.
      destruct H0.
      remember (paths here current_flow.(Dest)) as p.
      destruct p; try tauto.
      destruct l; try tauto.
      subst.
      assert (H1' := H1).
      apply IHpath in H1.
      simpl.
      simpl in H1.
      constructor; try tauto.
      unfold not.
      intros.
      destruct H2.
      + subst.
        eapply paths_move_closer_to_destination in H; repeat rewrite <- Heqp in H.
        simpl in H.
        omega.
      + assert (~(In here path)); try tauto.
        eapply decreasing_distances_implies_nonmember.
        * apply eq_sym.
          eassumption.
        * assert (H' := H).
          eapply paths_move_closer_to_destination in H.
          rewrite <- Heqp in H.
          remember (paths n current_flow.(Dest)) as p.
          destruct p; try tauto.
          apply strictly_decreasing_distances_strengthening with (small_bound := length l0); try (simpl; omega).
          apply eq_sym in Heqp0.
          eapply all_pairs_paths_generate_strictly_decreasing_distances; eassumption.
  Qed.
End Node.

Require Import ZArith.
Section NetworkExample.
  Local Inductive ExampleVertex :=
  | A
  | B
  | C
  | D
  | E
  | F
  .

  (*
    example_topology:

        B ------> E
      / | \       ↑
     A  |  D <--- F
      \ | /
        C
  *)
  Local Definition example_topology n1 n2 :=
    match (n1, n2) with
    | (A, B) | (B, A) => True
    | (A, C) | (C, A) => True
    | (B, C) | (C, B) => True
    | (B, D) | (D, B) => True
    | (B, E) => True
    | (C, D) | (D, C) => True
    | (F, D) => True
    | (F, E) => True
    | _ => False
    end.

  Local Definition example_all_pairs_paths n1 n2 :=
    match (n1, n2) with
    | (A, A) | (B, B) | (C, C) | (D, D) | (E, E) | (F, F) => Some nil
    | (A, B) => Some (C :: B :: nil)
    | (A, C) => Some (C :: nil)
    | (A, D) => Some (B :: D :: nil)
    | (A, E) => Some (B :: E :: nil)
    | (A, F) => None
    | (B, A) => Some (A :: nil)
    | (B, C) => Some (C :: nil)
    | (B, D) => Some (D :: nil)
    | (B, E) => Some (E :: nil)
    | (B, F) => None
    | (C, A) => Some (A :: nil)
    | (C, B) => Some (B :: nil)
    | (C, D) => Some (D :: nil)
    | (C, E) => Some (A :: B :: E :: nil)
    | (C, F) => None
    | (D, A) => Some (C :: A :: nil)
    | (D, B) => Some (B :: nil)
    | (D, C) => Some (C :: nil)
    | (D, E) => Some (B :: E :: nil)
    | (D, F) => None
    | (E, _) => None
    | (F, A) => Some (D :: B :: A :: nil)
    | (F, B) => Some (D :: B :: nil)
    | (F, C) => Some (D :: C :: nil)
    | (F, D) => Some (D :: nil)

    (* circuitous route which won't actually get followed because D will route to B *)
    | (F, E) => Some (D :: C :: A :: B :: E :: nil)
    end.

  Local Theorem validity : forall (policy : network_policy ExampleVertex),
    (forall n1 n2, policy {| Src := n1; Dest := n2 |} = true -> example_all_pairs_paths n1 n2 <> None)
      -> next_node_valid ExampleVertex example_topology policy
        (all_pairs_paths_next_node_generator ExampleVertex example_all_pairs_paths example_topology policy).
  Proof.
    intros.
    apply all_pairs_paths_generator_valid.
    constructor; intros.
    - destruct src, dest; unfold example_topology; simpl; tauto.
    - destruct current_flow.
      simpl.
      apply H in H0.
      destruct (example_all_pairs_paths Src0 Dest0); tauto.
    - destruct src, dest; simpl; try omega; tauto.
  Qed.
End NetworkExample.
