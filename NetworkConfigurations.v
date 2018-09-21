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

    no_dead_ends : forall src dest hop_target,
      next src dest hop_target
        -> exists path, is_next_node_path next path hop_target dest;

    all_paths_acyclic : forall node path,
      is_next_node_path next path node node -> path = nil
  }.
End Node.

Require Import ZArith.
Section NatNetworkExample.
  Local Definition nat_topology src dest := src - dest < 10.
  Local Definition nat_policy (f : flow nat) := Dest nat f <=? Src nat f.
  Local Inductive nat_next_node : next_node nat :=
  | MinusOne : forall next_src dest,
    next_src >= dest -> nat_next_node (S next_src) dest next_src
  | MinusTwo : forall next_src dest,
    next_src >= dest -> nat_next_node (S (S next_src)) dest next_src.

  Local Lemma reducing_exists : forall src dest,
    src >= dest
      -> exists path, is_next_node_path nat nat_next_node path src dest.
  Proof.
    intros.
    induction src.
    assert (dest = 0) by omega; subst.
    exists nil.
    reflexivity.
    assert (dest <= src \/ dest = S src) by omega.
    case H0; intros.
    assert (H' := H1).
    apply IHsrc in H1.
    destruct H1.
    exists (cons src x).
    simpl.
    apply conj; try assumption.
    constructor.
    omega.
    subst.
    exists nil.
    reflexivity.
  Qed.

  Local Theorem nat_next_node_valid : next_node_valid nat nat_topology nat_policy nat_next_node.
  Proof.
    constructor; intros.
    unfold nat_topology.
    inversion H; omega.
    unfold nat_policy in H.
    apply Nat.leb_le in H.
    apply reducing_exists.
    omega.
    inversion H; apply reducing_exists; assumption.
    destruct path.
    reflexivity.
    simpl in H.
    destruct H.
    inversion H; omega.
  Qed.
End NatNetworkExample.
