Require Import Coq.Lists.List.
Import ListNotations.
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
    | [] => here = current_flow.(Dest)
    | hop_target :: cdr =>
        next here current_flow hop_target /\
        is_next_node_path next cdr hop_target current_flow
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
      is_next_node_path next path here current_flow -> NoDup (here :: path)
  }.

  Definition dec_next_node := Node -> flow -> option Node.

  Definition dec_next_node_valid (topology : network_topology) (policy : network_policy) (dec_next : dec_next_node) :=
    next_node_valid topology policy (fun here current_flow hop_target => dec_next here current_flow = Some hop_target).

  Fixpoint is_path_in_topology (topology : network_topology) src dest path :=
    match path with
    | [] => src = dest
    | hop_target :: cdr =>
      topology src hop_target /\
      is_path_in_topology topology hop_target dest cdr
    end.

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

  Definition edge_costs := Node -> Node -> nat.
  (* NOTE: All pairs of nodes have an edge cost, even
     pairs that don't have an edge between them in the topology.
     This is logically consistent (the costs for the pairs that
     aren't in the topology won't get used), but perhaps unintuitive. *)

  Definition only_positive_costs (costs : edge_costs) := forall n1 n2,
    costs n1 n2 > 0.

  Fixpoint path_cost (costs : edge_costs) src path :=
    match path with
    | [] => 0
    | car :: cdr => costs src car + path_cost costs car cdr
    end.

  Definition generates_decreasing_costs (paths : all_pairs_paths) costs :=
    only_positive_costs costs /\
    forall src dest,
      match paths src dest with
      | Some (hop_target :: cdr) =>
        match paths hop_target dest with
        | Some path => path_cost costs hop_target path < path_cost costs src (hop_target :: cdr)
        | None => False
        end
      | _ => True
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

    (* The consumer needs to show that some global cost function exists
       for which every hop on a path generated by `paths` will decrease
       the estimated total cost of the remainder the path. This is a
       sufficient condition to show prove the absence of cycles.
       (In practice, the consumer would likely start out with the cost function
       as an input based on environmental factors, then use it to generate
       a valid all-pairs paths function.) *)
    paths_move_closer_to_destination : exists (costs : edge_costs),
      generates_decreasing_costs paths costs
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
    clear H1.
    assert (H' := H).
    apply paths_move_closer_to_destination in H'.
    destruct H'.
    destruct H1.
    remember (path_cost x hop_target l) as cost.
    assert (match paths hop_target current_flow.(Dest) with | Some p => path_cost x hop_target p <= cost | _ => False end) by (rewrite <- Heqx; omega).
    assert (cost = 0 -> hop_target = current_flow.(Dest)).
    - intros.
      subst.
      destruct l.
      + eapply paths_in_topology in H.
        rewrite <- Heqx in H.
        tauto.
      + simpl in H4.
        unfold only_positive_costs in H1.
        specialize (H1 hop_target).
        specialize (H1 n).
        omega.
    - clear Heqcost.
      clear Heqx.
      dependent induction cost generalizing hop_target; try (exists []; tauto).
      clear H4.
      remember (paths hop_target current_flow.(Dest)) as p.
      destruct p; try tauto.
      destruct l0; try (exists []; simpl; eapply paths_in_topology in H; rewrite <- Heqp in H; simpl in H; subst; reflexivity).
      specialize (H2 hop_target).
      specialize (H2 current_flow.(Dest)).
      rewrite <- Heqp in H2.
      specialize (IHcost n).
      destruct (paths n current_flow.(Dest)); try tauto.
      assert (path_cost x n l1 <= cost) by omega.
      apply IHcost in H4.
      + destruct H4.
        exists (n :: x0).
        simpl.
        constructor; try assumption.
        unfold all_pairs_paths_next_node_generator.
        constructor; try assumption.
        rewrite <- Heqp.
        reflexivity.
      + intros.
        subst.
        simpl in H3.
        assert (x hop_target n > 0) by (apply H1).
        assert (path_cost x n l0 = 0) by omega.
        destruct l0; simpl in H6.
        * eapply paths_in_topology in H.
          rewrite <- Heqp in H.
          simpl in H.
          tauto.
        * assert (x n n0 > 0) by (apply H1).
          omega.
  Qed.

  Fixpoint has_strictly_decreasing_costs (paths : all_pairs_paths) (costs : edge_costs) l dest bound :=
    match l with
    | [] => True
    | node :: cdr =>
      match paths node dest with
      | Some l' => path_cost costs node l' < bound /\ has_strictly_decreasing_costs paths costs cdr dest (path_cost costs node l')
      | None => False
      end
    end.

  Lemma strictly_decreasing_costs_strengthening : forall paths costs l dest small_bound big_bound,
    has_strictly_decreasing_costs paths costs l dest small_bound
      -> small_bound <= big_bound
      -> has_strictly_decreasing_costs paths costs l dest big_bound.
  Proof.
    intros.
    destruct l; simpl; try tauto.
    simpl in H.
    destruct (paths n dest); try tauto.
    destruct H.
    constructor; try tauto; omega.
  Qed.

  Lemma all_pairs_paths_generate_strictly_decreasing_costs : forall (paths : all_pairs_paths) costs topology policy here current_flow path path',
    generates_decreasing_costs paths costs
      -> paths here current_flow.(Dest) = Some path'
      -> is_next_node_path (all_pairs_paths_next_node_generator paths topology policy) path here current_flow
      -> has_strictly_decreasing_costs paths costs path current_flow.(Dest) (path_cost costs here path').
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
    destruct H'.
    specialize (H4 here).
    specialize (H4 current_flow.(Dest)).
    rewrite H0 in H4.
    remember (paths n current_flow.(Dest)) as p.
    apply eq_sym in Heqp.
    destruct p; try tauto.
    constructor; try assumption.
    apply IHpath; assumption.
  Qed.


  Lemma decreasing_costs_implies_nonmember : forall (paths : all_pairs_paths) costs path dest node path',
    paths node dest = Some path'
      -> has_strictly_decreasing_costs paths costs path dest (path_cost costs node path')
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
      apply strictly_decreasing_costs_strengthening with (big_bound := path_cost costs node path') in H1; try omega.
      eapply IHpath; eassumption.
  Qed.

  Lemma NoDup_single : forall A (el : A), NoDup [el].
  Proof.
    intros.
    constructor.
    - unfold not; intros.
      inversion H.
    - constructor.
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
      apply paths_move_closer_to_destination in H.
      destruct H.
      destruct H.
      specialize (H1 src).
      specialize (H1 current_flow.(Dest)).
      rewrite <- Heqp in H1.
      destruct (paths n current_flow.(Dest)); tauto.
    - dependent induction path; try apply NoDup_single.
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
      constructor; try assumption.
      unfold not.
      intros.
      destruct H2.
      + subst.
        apply paths_move_closer_to_destination in H.
        destruct H.
        destruct H.
        specialize (H2 here).
        specialize (H2 current_flow.(Dest)).
        rewrite <- Heqp in H2.
        rewrite <- Heqp in H2.
        simpl in H2.
        omega.
      + assert (~(In here path)); try tauto.
        apply paths_move_closer_to_destination in H.
        destruct H.
        eapply decreasing_costs_implies_nonmember with (costs := x).
        * apply eq_sym.
          eassumption.
        * assert (H' := H).
          destruct H'.
          specialize (H4 here).
          specialize (H4 current_flow.(Dest)).
          rewrite <- Heqp in H4.
          remember (paths n current_flow.(Dest)) as p.
          destruct p; try tauto.
          apply strictly_decreasing_costs_strengthening with (small_bound := path_cost x n l0); try omega.
          apply eq_sym in Heqp0.
          eapply all_pairs_paths_generate_strictly_decreasing_costs; eassumption.
  Qed.

  Definition all_pairs_paths_dec_next_node_generator
    (paths : all_pairs_paths)
    (topology : network_topology)
    (policy : network_policy)
    here
    current_flow
  :=
    if policy current_flow then
      match paths here current_flow.(Dest) with
      | Some (hop_target :: _) => Some hop_target
      | _ => None
      end
    else None.

  Lemma is_next_node_path_weakening : forall (strict_next lenient_next : next_node) path here current_flow,
    is_next_node_path strict_next path here current_flow
      -> (forall here' current_flow' hop_target, strict_next here' current_flow' hop_target -> lenient_next here' current_flow' hop_target)
      -> is_next_node_path lenient_next path here current_flow.
  Proof.
    intros.
    dependent induction path; simpl; simpl in H; try assumption.
    destruct H.
    assert (H0' := H0).
    apply IHpath with (here := a) (current_flow := current_flow) in H0; try tauto.
    constructor; try tauto.
    apply H0'; assumption.
  Qed.

  Lemma next_node_extensionality : forall next1 next2 topology policy,
    (forall here current_flow hop_target, next1 here current_flow hop_target <-> next2 here current_flow hop_target)
      -> next_node_valid topology policy next1
      -> next_node_valid topology policy next2.
  Proof.
    intros.
    constructor; intros; destruct H0.
    - eapply all_hops_in_topology0.
      apply H.
      eassumption.
    - constructor; intros.
      + apply path_exists_only_for_valid_flows0 in H0; try assumption.
        destruct H0.
        exists x.
        eapply is_next_node_path_weakening; try eassumption; apply H.
      + apply path_exists_only_for_valid_flows0 in H1.
        destruct H1.
        apply H2.
        destruct H0.
        exists x.
        eapply is_next_node_path_weakening; try eassumption; apply H.
    - apply H in H1.
      apply no_black_holes0 in H1.
      destruct H1.
      exists x.
      eapply is_next_node_path_weakening; try eassumption; apply H.
    - eapply is_next_node_path_weakening in H1; try apply H.
      apply all_paths_acyclic0 in H1.
      assumption.
  Qed.

  Theorem all_pairs_paths_dec_generator_valid : forall paths topology policy,
    all_pairs_paths_valid paths topology policy
      -> dec_next_node_valid topology policy (all_pairs_paths_dec_next_node_generator paths topology policy).
  Proof.
    intros.
    apply all_pairs_paths_generator_valid in H.
    eapply next_node_extensionality; try eassumption.
    unfold all_pairs_paths_next_node_generator, all_pairs_paths_dec_next_node_generator.
    constructor; intros; repeat match goal with
    | [ H : _ /\ _ |- _ ] => destruct H
    | [ _ : _ |- _ /\ _ ] => constructor
    | [ H : context[match ?x with _ => _ end] |- _ ] => destruct x
    | [ H : ?x = _ |- context[?x] ] => rewrite H
    | [ H : _ ?a = _ ?b |- ?b = ?a ] => injection H; apply eq_sym
    | _ => tauto
    | _ => discriminate
    end.
  Qed.

  Definition routing_tables := Node -> list (flow * Node).

  Record routing_tables_valid (tables : routing_tables) (dec_next : dec_next_node) := {
    no_duplicate_entries : forall here,
      NoDup (tables here);

    entries_match_next_node_result : forall here current_flow hop_target,
      dec_next here current_flow = Some hop_target
        <-> In (current_flow, hop_target) (tables here)
  }.

  Definition routing_tables_generator := dec_next_node -> list Node -> routing_tables.

  Definition valid_node_enumeration (all_nodes : list Node) := forall node, In node all_nodes.

  Definition routing_tables_generator_valid (generator : routing_tables_generator) := forall dec_next all_nodes,
    valid_node_enumeration all_nodes
      -> NoDup all_nodes
      -> routing_tables_valid
        (generator dec_next all_nodes)
        dec_next.

  Fixpoint map_filter {A} {B} (mapper : A -> option B) (l : list A) :=
    match l with
    | [] => []
    | car :: cdr =>
      match mapper car with
      | Some car' => car' :: map_filter mapper cdr
      | None => map_filter mapper cdr
      end
    end.

  Lemma map_filter_in_preservation : forall A B mapper l (element : A) (result : B),
    (forall (x y : A), {x = y} + {x <> y})
      -> mapper element = Some result
      -> In element l
      -> In result (map_filter mapper l).
  Proof.
    intros.
    dependent induction l; try (simpl in H0; tauto).
    assert ({a = element} + {a <> element}) by apply X.
    destruct H1.
    - subst.
      simpl.
      rewrite H.
      constructor.
      reflexivity.
    - simpl.
      assert (In result (map_filter mapper l)).
      + simpl in H0.
        destruct H0; try tauto.
        eapply IHl; eassumption.
      + destruct (mapper a); simpl; tauto.
  Qed.

  Lemma map_filter_in_filtering : forall A B mapper l (result : B),
    (forall (x y : B), {x = y} + {x <> y})
      -> In result (map_filter mapper l)
      -> {element : A | mapper element = Some result}.
  Proof.
    intros.
    dependent induction l; try (simpl in H; tauto).
    simpl in H.
    remember (mapper a) as mapped_a.
    destruct mapped_a.
    - assert ({b = result} + {b <> result}) by apply X.
      destruct H0.
      + subst.
        apply exist with (x := a).
        apply eq_sym.
        assumption.
      + simpl in H.
        apply IHl; try assumption.
        destruct H; tauto.
    - apply IHl; assumption.
  Qed.

  Definition fst {A} {B} (pair : A * B) := match pair with | (l, _) => l end.
  Definition snd {A} {B} (pair : A * B) := match pair with | (_, r) => r end.

  Hypothesis Node_eq_dec : forall x y : Node, {x = y} + {x <> y}.
  Definition Node_pair_eq_dec : forall x y : (Node * Node), {x = y} + {x <> y}.
  Proof.
    intros.
    destruct x, y, Node_eq_dec with (x := n) (y := n1), Node_eq_dec with (x := n0) (y := n2); subst; try (constructor 1; reflexivity); constructor 2; unfold not; intros; injection H; tauto.
  Defined.

  Definition flow_Node_pair_eq_dec : forall x y : (flow * Node), {x = y} + {x <> y}.
  Proof.
    intros.
    destruct x, y, f, f0, Node_eq_dec with (x := Src0) (y := Src1), Node_eq_dec with (x := Dest0) (y := Dest1), Node_eq_dec with (x := n) (y := n0); subst; try (constructor 1; reflexivity); constructor 2; unfold not; intros; injection H; tauto.
  Defined.

  Definition exhaustive_routing_tables_generator (dec_next : dec_next_node) (all_nodes : list Node) (here : Node) :=
    map_filter (fun pair =>
      match dec_next here {| Src := fst pair; Dest := snd pair |} with
      | Some hop_target => Some ({| Src := fst pair; Dest := snd pair |}, hop_target)
      | None => None
      end
    ) (nodup Node_pair_eq_dec (list_prod all_nodes all_nodes)).

  Theorem exhaustive_routing_tables_generator_valid : routing_tables_generator_valid exhaustive_routing_tables_generator.
  Proof.
    unfold exhaustive_routing_tables_generator.
    constructor; intros.
    - remember (nodup Node_pair_eq_dec (list_prod all_nodes all_nodes)) as pairs.
      assert (NoDup pairs) by (subst; apply NoDup_nodup).
      clear H.
      clear Heqpairs.
      dependent induction pairs; try apply NoDup_nil.
      simpl.
      inversion H1; clear H1; subst.
      destruct a; simpl.
      destruct (dec_next here {| Src := n; Dest := n0 |}); try (apply IHpairs; assumption).
      constructor; try (apply IHpairs; assumption).
      clear IHpairs.
      dependent induction pairs; try (simpl; tauto).
      inversion H4; clear H4; subst.
      simpl.
      destruct (dec_next here {| Src := fst a; Dest := snd a |}).
      + simpl.
        unfold not.
        intros.
        destruct a; simpl in H.
        destruct H.
        * injection H.
          intros.
          subst.
          apply H3.
          simpl.
          tauto.
        * apply IHpairs in H; try assumption.
          simpl in H3.
          tauto.
      + simpl in H3.
        apply IHpairs; tauto.
    - constructor; intros.
      + apply map_filter_in_preservation with (element := (current_flow.(Src), current_flow.(Dest))).
        * apply Node_pair_eq_dec.
        * destruct current_flow.
          simpl.
          rewrite H1.
          reflexivity.
        * apply nodup_In; apply in_prod; apply H.
      + apply map_filter_in_filtering in H1; try apply flow_Node_pair_eq_dec.
        destruct H1.
        assert (x = (current_flow.(Src), current_flow.(Dest))).
        * destruct (dec_next here {| Src := fst x; Dest := snd x |}); try discriminate.
          injection e.
          intros.
          subst.
          destruct x.
          simpl.
          reflexivity.
        * subst.
          destruct current_flow.
          simpl in e.
          destruct (dec_next here {| Src := Src0; Dest := Dest0 |}); try discriminate.
          injection e.
          intros.
          subst.
          reflexivity.
  Qed.

  (* TODO: Figure out how to import some of this from a separate file *)
  Section OpenFlow.
    Variable Port : Set.

    (* TODO: decide on a good representation for this *)
    Definition uint : nat -> Type.
    Proof.
      intros.
      (* FIXME: `nat` is not a fixed-width integer; this will cause problems when generating binaries *)
      exact nat.
    Defined.

    Definition ipv4_address : Type := uint 8 * uint 8 * uint 8 * uint 8.

    Record ipv4_packet := {
      IpSrc : ipv4_address;
      IpDest : ipv4_address
      (* Other fields exist but are not used here *)
    }.


    (* OpenFlow switch spec: https://www.opennetworking.org/wp-content/uploads/2013/04/openflow-spec-v1.0.0.pdf *)

    Record header_field_matcher := {
      (* TODO: support IP wildcard matchers *)
      IpSrcMatcher : option ipv4_address;
      IpDestMatcher : option ipv4_address
      (* Other header fields exist but are not used here *)
    }.

    Inductive openflow_action :=
    | ForwardToPort : Port -> openflow_action
    | Drop
    (* Other actions exist but are not used here *)
    .

    Record openflow_flow_entry := {
      header_fields : list header_field_matcher;
      actions : list openflow_action
      (* Entries also contain "counters" which are not used here *)
    }.

    Definition matches_header_field_matcher (packet : ipv4_packet) (matcher : header_field_matcher) :=
      match matcher.(IpSrcMatcher) with
      | Some src_address => src_address = packet.(IpSrc)
      | None => True
      end /\
      match matcher.(IpDestMatcher) with
      | Some dest_address => dest_address = packet.(IpDest)
      | None => True
      end.

    Definition generate_openflow_entries
      (tables : routing_tables)
      (node_ips : Node -> ipv4_address)
      (ports : Node -> Node -> option Port)
      node
    :=
      map (fun pair => {|
        header_fields := [
          {|
            IpSrcMatcher := Some (node_ips pair.(fst).(Src));
            IpDestMatcher := Some (node_ips pair.(fst).(Dest))
          |}
        ];
        actions := [
          match ports node pair.(snd) with
          | Some port => ForwardToPort port

          (* Impossible if `tables` is valid for the topology defined by `ports` *)
          | None => Drop
          end
        ]
      |}) (tables node).
  End OpenFlow.
End Node.

Ltac enumerate_finite_set Node :=
  match goal with
  | [ |- {l : list Node | valid_node_enumeration Node l} ] => idtac
  | _ => fail 1
  end;
  econstructor;
  unfold valid_node_enumeration;
  intros;
  match goal with
  | [ node : Node |- _ ] => destruct node
  end;
  unshelve (
    let cdr := fresh "cdr" in
      evar (cdr : list Node);
      let cdr' := eval unfold cdr in cdr in
        clear cdr;
        match goal with
        | [ |- In ?n _ ] => instantiate (1 := n :: cdr')
        end;
        simpl;
        tauto
  );
  exact [].


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
     A  |5 D <--- F
      \ | /
        C
  *)
  Local Definition example_topology n1 n2 :=
    match n1, n2 with
    | A, B | B, A => True
    | A, C | C, A => True
    | B, C | C, B => True
    | B, D | D, B => True
    | B, E => True
    | C, D | D, C => True
    | F, D => True
    | F, E => True
    | _, _ => False
    end.

  Local Definition example_all_pairs_paths n1 n2 :=
    match n1, n2 with
    | A, A | B, B | C, C | D, D | E, E | F, F => Some []
    | A, B => Some [C; B]
    | A, C => Some [C]
    | A, D => Some [B; D]
    | A, E => Some [B; E]
    | A, F => None
    | B, A => Some [A]
    | B, C => Some [C]
    | B, D => Some [D]
    | B, E => Some [E]
    | B, F => None
    | C, A => Some [A]
    | C, B => Some [B]
    | C, D => Some [D]
    | C, E => Some [A; B; E]
    | C, F => None
    | D, A => Some [C; A]
    | D, B => Some [B]
    | D, C => Some [C]
    | D, E => Some [C; A; B; E]
    | D, F => None
    | E, _ => None
    | F, A => Some [D; B; A]
    | F, B => Some [D; B]
    | F, C => Some [D; C]
    | F, D => Some [D]

    (* a route which won't actually get followed because D will reroute *)
    | F, E => Some [D; C; B; E]
    end.

  (* Giving all edges a cost of 1 would not satisfy the decreasing-costs
  constraint, because when routing F to E, node B would choose
  a path of [C; A; B; E] which is not shorter than the original expected
  path from F of [D; C; B; E]. However, if the (C, B) edge
  has a large cost, then the total cost of [C; A; B; E] is less
  than the cost of [D; C; B; E]. *)
  Definition example_costs n1 n2 :=
    match n1, n2 with
    | C, B => 5
    | _, _ => 1
    end.

  Definition policy_satisfiable (policy : network_policy ExampleVertex) := forall n1 n2,
    policy {| Src := n1; Dest := n2 |} = true -> example_all_pairs_paths n1 n2 <> None.

  Local Lemma paths_valid : forall policy,
    policy_satisfiable policy
      -> all_pairs_paths_valid ExampleVertex example_all_pairs_paths example_topology policy.
  Proof.
    intros.
    constructor; intros.
    - destruct src, dest; unfold example_topology; simpl; tauto.
    - destruct current_flow.
      simpl.
      apply H in H0.
      destruct (example_all_pairs_paths Src0 Dest0); tauto.
    - exists example_costs.
      constructor; try (unfold only_positive_costs, example_costs; intros; destruct n1, n2; omega).
      intros.
      destruct src, dest; simpl; try omega; tauto.
  Qed.

  Local Theorem validity : forall policy,
    policy_satisfiable policy
      -> next_node_valid ExampleVertex example_topology policy
        (all_pairs_paths_next_node_generator ExampleVertex example_all_pairs_paths example_topology policy).
  Proof.
    intros.
    apply all_pairs_paths_generator_valid.
    apply paths_valid; assumption.
  Qed.

  Local Theorem dec_validity : forall policy,
    policy_satisfiable policy
      -> dec_next_node_valid ExampleVertex example_topology policy
        (all_pairs_paths_dec_next_node_generator ExampleVertex example_all_pairs_paths example_topology policy).
    Proof.
      intros.
      apply all_pairs_paths_dec_generator_valid.
      apply paths_valid; assumption.
    Qed.

  Local Definition example_policy current_flow :=
    match Src ExampleVertex current_flow, Dest ExampleVertex current_flow with
    | A, _ | _, A | F, _ | _, F => true
    | _, _ => false
    end.

  Definition example_dec_next_node := all_pairs_paths_dec_next_node_generator ExampleVertex example_all_pairs_paths example_topology example_policy.

  Local Definition example_enumeration: {l : list ExampleVertex | valid_node_enumeration ExampleVertex l} :=
    ltac:(enumerate_finite_set ExampleVertex).

  Local Definition ExampleVertex_eq_dec : forall (n1 n2 : ExampleVertex), {n1 = n2} + {n1 <> n2}.
  Proof.
    intros; destruct n1, n2; firstorder discriminate.
  Defined.

  Local Definition example_routing_tables := exhaustive_routing_tables_generator ExampleVertex ExampleVertex_eq_dec example_dec_next_node (proj1_sig example_enumeration).

  Local Theorem example_routing_tables_valid : routing_tables_valid ExampleVertex example_routing_tables example_dec_next_node.
  Proof.
    apply exhaustive_routing_tables_generator_valid.
    - exact (proj2_sig example_enumeration).
    - repeat constructor; firstorder discriminate.
  Qed.

  Definition concrete_routing_tables := map (fun n => (n, example_routing_tables n)) (proj1_sig example_enumeration).

  Definition example_node_ips node :=
    match node with
    | A => (10, 0, 0, 1)
    | B => (10, 0, 0, 2)
    | C => (10, 0, 0, 3)
    | D => (10, 0, 0, 4)
    | E => (10, 0, 0, 5)
    | F => (10, 0, 0, 6)
    end.

  Definition example_ports n1 n2 :=
    (*
      FIXME: this is mostly copy-pasted from example_topology.
      After topologies are decidable, this won't be necessary.
    *)
    if (match n1, n2 with
    | A, B | B, A => true
    | A, C | C, A => true
    | B, C | C, B => true
    | B, D | D, B => true
    | B, E => true
    | C, D | D, C => true
    | F, D => true
    | F, E => true
    | _, _ => false
    end) then Some (n1, n2) else None.

  Definition example_openflow_entries := generate_openflow_entries ExampleVertex (ExampleVertex * ExampleVertex) example_routing_tables example_node_ips example_ports.
  Definition concrete_openflow_entries := map (fun n => (n, example_openflow_entries n)) (proj1_sig example_enumeration).
  Compute concrete_openflow_entries.
End NetworkExample.
