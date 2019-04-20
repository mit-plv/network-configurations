Require Import List.
Import ListNotations.
Require Import Equality.
Require Import FinFun.
Require Import Bool.
Require Import ZArith.
Require Import bbv.Word.

Section Node.
  Context {Switch : Set}.
  Context {Host : Set}.

  Inductive Node :=
  | SwitchNode : Switch -> Node
  | HostNode : Host -> Node
  .

  Definition Port : Set := word 16.
  Opaque Port.

  Record flow := {
    Src : Host;
    Dest : Host
  }.

  Definition network_topology := Node -> Node -> option Port.

  Record valid_topology (topology : network_topology) := {
    no_direct_host_links : forall host1 host2,
      topology (HostNode host1) (HostNode host2) = None;
    no_duplicate_ports : forall node outgoing1 outgoing2,
      match topology node outgoing1, topology node outgoing2 with
      | Some port1, Some port2 => port1 = port2 -> outgoing1 = outgoing2
      | _, _ => True
      end;
    valid_port_numbers : forall switch1 node2,
      match topology (SwitchNode switch1) node2 with
      | Some port => port <> (natToWord 16 0)
      | None => True
      end;
    no_isolated_hosts : forall host,
      exists switch,
        if topology (HostNode host) (SwitchNode switch)
        then True
        else False
  }.

  Definition static_network_policy := flow -> bool.

  Definition next_node := Switch -> flow -> Node -> Prop.

  Fixpoint is_next_node_path (next : next_node) path here current_flow :=
    match path with
    | [] => next here current_flow (HostNode current_flow.(Dest))
    | hop_target :: cdr =>
        next here current_flow (SwitchNode hop_target) /\
        is_next_node_path next cdr hop_target current_flow
    end.

  Fixpoint is_partial_next_node_path (next : next_node) path here end_switch current_flow :=
    match path with
    | [] => here = end_switch
    | hop_target :: cdr =>
        next here current_flow (SwitchNode hop_target) /\
        is_partial_next_node_path next cdr hop_target end_switch current_flow
    end.

  Lemma is_partial_next_node_path_app : forall next current_flow first_half second_half start_switch mid_switch end_switch,
    is_partial_next_node_path next first_half start_switch mid_switch current_flow
      -> is_partial_next_node_path next second_half mid_switch end_switch current_flow
      -> is_partial_next_node_path next (first_half ++ second_half) start_switch end_switch current_flow.
  Proof.
    intros.
    dependent induction first_half; simpl in *; subst; try assumption.
    constructor; try tauto.
    apply IHfirst_half with (mid_switch := mid_switch); tauto.
  Qed.

  Lemma last_app {A} : forall (l : list A) (element : A) (default : A),
    last (l ++ [element]) default = element.
  Proof.
    intros.
    dependent induction l; try reflexivity.
    simpl.
    destruct_with_eqn (l ++ [element]); try (destruct l; discriminate).
    rewrite <- Heql0.
    apply IHl.
  Qed.

  Lemma last_default_replacement {A} : forall (l : list A) (head : A) (default1 : A) (default2 : A),
    last (head :: l) default1 = last (head :: l) default2.
  Proof.
    intros.
    dependent induction l using rev_ind; try reflexivity.
    rewrite app_comm_cons.
    repeat rewrite last_app.
    reflexivity.
  Qed.

  Lemma next_node_path_has_partial : forall next path here current_flow,
    is_next_node_path next path here current_flow
      -> is_partial_next_node_path next path here (last path here) current_flow.
  Proof.
    intros.
    dependent induction path; try (simpl in *; tauto).
    simpl in H; constructor; try tauto.
    rewrite last_default_replacement with (default2 := a).
    simpl.
    destruct path; try reflexivity.
    apply IHpath.
    tauto.
  Qed.

  Record next_node_valid (topology : network_topology) (policy : static_network_policy) (next : next_node) := {
    all_hops_in_topology : forall here current_flow hop_target,
      next here current_flow hop_target -> if topology (SwitchNode here) hop_target then True else False;

    path_exists_only_for_valid_flows : forall current_flow first_switch port,
      topology (HostNode current_flow.(Src)) (SwitchNode first_switch) = Some port
        -> (
          (policy current_flow = true) <->
          exists path, is_next_node_path next path first_switch current_flow
        );

    no_black_holes : forall here current_flow hop_target,
      policy current_flow = true
        -> next here current_flow hop_target
        ->
          match hop_target with
          | HostNode dest =>
            dest = current_flow.(Dest)
          | SwitchNode next_switch =>
            exists path,
              is_next_node_path next path next_switch current_flow
          end;

    all_paths_acyclic : forall path here end_switch current_flow,
      is_partial_next_node_path next path here end_switch current_flow -> NoDup (here :: path);

    forwards_to_correct_host : forall here current_flow end_host,
      next here current_flow (HostNode end_host)
        -> end_host = current_flow.(Dest)
  }.

  Definition dec_next_node := Switch -> flow -> option Node.

  Definition dec_next_node_valid topology policy dec_next :=
    next_node_valid topology policy (fun here current_flow hop_target =>
      dec_next here current_flow = Some hop_target
    ).

  Fixpoint is_path_in_topology (topology : network_topology) src dest path :=
    match path with
    | [] => if topology (SwitchNode src) (HostNode dest) then True else False
    | hop_target :: cdr =>
      (if topology (SwitchNode src) (SwitchNode hop_target) then True else False) /\
      is_path_in_topology topology hop_target dest cdr
    end.

  Definition all_pairs_paths := Switch -> Host -> option (list Switch).

  Definition all_pairs_paths_next_node_generator
    (paths : all_pairs_paths)
    (topology : network_topology)
    (policy : static_network_policy)
    here
    current_flow
    hop_target
  :=
    policy current_flow = true /\
    match paths here current_flow.(Dest) with
    | Some (hop_target' :: _) => hop_target = SwitchNode hop_target'
    | Some [] => hop_target = HostNode current_flow.(Dest)
    | None => False
    end.

  Definition edge_costs := Node -> Port -> nat.

  Definition only_positive_costs (topology : network_topology) (costs : edge_costs) := forall n1 n2,
    match topology n1 n2 with
    | Some port => costs n1 port > 0
    | None => True
    end.

  Fixpoint path_cost (topology : network_topology) (costs : edge_costs) src dest (path : list Switch) :=
    match path with
    | [] =>
      match topology (SwitchNode src) (HostNode dest) with
      | Some port => Some (costs (SwitchNode src) port)
      | None => None
      end
    | car :: cdr =>
      match topology (SwitchNode src) (SwitchNode car), path_cost topology costs car dest cdr with
      | Some port, Some remaining_cost => Some (costs (SwitchNode src) port + remaining_cost)
      | _, _ => None
      end
    end.

  Definition generates_decreasing_costs topology (paths : all_pairs_paths) costs :=
    only_positive_costs topology costs /\
    forall src dest,
      match paths src dest with
      | Some (hop_target :: cdr) =>
        match paths hop_target dest with
        | Some path =>
          match path_cost topology costs hop_target dest path, path_cost topology costs src dest (hop_target :: cdr) with
          | Some remaining_cost, Some original_cost => remaining_cost < original_cost
          | _, _ => False
          end
        | None => False
        end
      | _ => True
      end.

  Record all_pairs_paths_valid topology policy paths := {
    paths_in_topology : forall src dest,
      match paths src dest with
      | Some path => is_path_in_topology topology src dest path
      | _ => True
      end;

    paths_exist_for_valid_flows : forall current_flow first_switch port,
      policy current_flow = true
        -> topology (HostNode current_flow.(Src)) (SwitchNode first_switch) = Some port
        ->
          match paths first_switch current_flow.(Dest) with
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
      generates_decreasing_costs topology paths costs
  }.

  Lemma all_pairs_paths_next_node_generator_creates_next_node_paths : forall paths topology policy current_flow hop_target,
    all_pairs_paths_valid topology policy paths
      -> policy current_flow = true
      -> match paths hop_target current_flow.(Dest) with | Some _ => True | None => False end
      -> exists path,
        is_next_node_path (all_pairs_paths_next_node_generator paths topology policy) path hop_target current_flow.
  Proof.
    intros.
    destruct_with_eqn (paths hop_target current_flow.(Dest)); try tauto.
    clear H1.
    assert (H' := H).
    apply paths_move_closer_to_destination in H'.
    destruct H', H1.
    assert (if path_cost topology x hop_target current_flow.(Dest) l then True else False).
    - destruct_with_eqn (path_cost topology x hop_target current_flow.(Dest) l); try tauto.
      specialize (H2 hop_target).
      specialize (H2 current_flow.(Dest)).
      rewrite Heqo in H2.
      destruct l.
      + simpl in Heqo0.
        destruct_with_eqn (topology (SwitchNode hop_target) (HostNode current_flow.(Dest))); try discriminate.
        apply paths_in_topology with (src := hop_target) (dest := current_flow.(Dest)) in H.
        rewrite Heqo in H.
        simpl in H.
        rewrite Heqo1 in H.
        tauto.
      + repeat match goal with
        | [ H : match ?x with | Some _ => _ | None => False end |- _ ] => destruct x; try tauto
        | _ => discriminate
        end.
    - destruct_with_eqn (path_cost topology x hop_target current_flow.(Dest) l); try tauto.
      assert (match paths hop_target current_flow.(Dest) with
      | Some p =>
        match path_cost topology x hop_target current_flow.(Dest) p with
        | Some cost' => cost' <= n
        | _ => False
        end
      | _ => False
      end) by (rewrite Heqo, Heqo0; omega).
      clear Heqo0 Heqo H3.
      dependent induction n generalizing hop_target.
      + destruct_with_eqn (paths hop_target current_flow.(Dest)); try tauto.
        destruct_with_eqn (path_cost topology x hop_target current_flow.(Dest) l0); try tauto.
        destruct l0.
        * apply paths_in_topology with (src := hop_target) (dest := current_flow.(Dest)) in H.
          rewrite Heqo in H.
          simpl in Heqo0, H.
          destruct_with_eqn (topology (SwitchNode hop_target) (HostNode current_flow.(Dest))); try tauto.
          assert (x (SwitchNode hop_target) p = n) by congruence.
          subst.
          specialize (H1 (SwitchNode hop_target)).
          specialize (H1 (HostNode current_flow.(Dest))).
          rewrite Heqo1 in H1.
          omega.
        * simpl in Heqo0.
          destruct_with_eqn (topology (SwitchNode hop_target) (SwitchNode s)); try discriminate.
          destruct (path_cost topology x s current_flow.(Dest) l0); try discriminate.
          specialize (H1 (SwitchNode hop_target)).
          specialize (H1 (SwitchNode s)).
          rewrite Heqo1 in H1.
          injection Heqo0; intros.
          omega.
      + destruct_with_eqn (paths hop_target current_flow.(Dest)); try tauto.
        destruct l0; try (exists []; constructor; try assumption; rewrite Heqo; reflexivity).
        specialize (H2 hop_target).
        specialize (H2 current_flow.(Dest)).
        rewrite Heqo in H2.
        specialize (IHn s).
        destruct (paths s current_flow.(Dest)); try tauto.
        destruct_with_eqn (path_cost topology x s current_flow.(Dest) l1); try tauto.
        destruct_with_eqn (path_cost topology x hop_target current_flow.(Dest) (s :: l0)); try tauto.
        simpl in Heqo1.
        assert (n0 <= n) by omega.
        apply IHn in H3.
        * destruct H3.
          exists (s :: x0).
          simpl.
          constructor; try assumption.
          unfold all_pairs_paths_next_node_generator.
          constructor; try assumption.
          rewrite Heqo.
          reflexivity.
  Qed.

  Fixpoint has_strictly_decreasing_costs topology (paths : all_pairs_paths) (costs : edge_costs) l dest bound :=
    match l with
    | [] => True
    | switch :: cdr =>
      match paths switch dest with
      | Some l' =>
        match path_cost topology costs switch dest l' with
        | Some cost => cost < bound /\ has_strictly_decreasing_costs topology paths costs cdr dest cost
        | None => False
        end
      | None => False
      end
    end.

  Lemma strictly_decreasing_costs_strengthening : forall topology paths costs l dest small_bound big_bound,
    has_strictly_decreasing_costs topology paths costs l dest small_bound
      -> small_bound <= big_bound
      -> has_strictly_decreasing_costs topology paths costs l dest big_bound.
  Proof.
    intros.
    destruct l; simpl; try tauto.
    simpl in H.
    repeat match goal with
    | [ H : match ?x with | Some _ => _ | None => False end |- _ ] => destruct x; try tauto
    end.
    destruct H.
    constructor; try tauto; omega.
  Qed.

  Lemma partial_all_pairs_paths_generate_strictly_decreasing_costs : forall (paths : all_pairs_paths) costs topology policy here end_switch current_flow path path' first_bound,
    generates_decreasing_costs topology paths costs
      -> paths here current_flow.(Dest) = Some path'
      -> path_cost topology costs here current_flow.(Dest) path' = Some first_bound
      -> is_partial_next_node_path (all_pairs_paths_next_node_generator paths topology policy) path here end_switch current_flow
      -> has_strictly_decreasing_costs topology paths costs path current_flow.(Dest) first_bound.
  Proof.
    intros.
    dependent induction path generalizing here; try (simpl; tauto).
    simpl.
    simpl in H2.
    destruct H2.
    unfold all_pairs_paths_next_node_generator in H2.
    destruct H2.
    rewrite H0 in H4.
    destruct path'; try discriminate.
    assert (a = s) by congruence; subst.
    assert (H' := H).
    destruct H'.
    specialize (H6 here).
    specialize (H6 current_flow.(Dest)).
    rewrite H0 in H6.
    destruct_with_eqn (paths s current_flow.(Dest)); try tauto.
    destruct_with_eqn (path_cost topology costs s current_flow.(Dest) l); try tauto.
    destruct_with_eqn (path_cost topology costs here current_flow.(Dest) (s :: path')); try tauto.
    assert (n0 = first_bound) by (injection H1; tauto); subst.
    constructor; try assumption.
    eapply IHpath; eassumption.
  Qed.


  Lemma decreasing_costs_implies_nonmember : forall topology (paths : all_pairs_paths) costs path dest node path' first_bound,
    paths node dest = Some path'
      -> path_cost topology costs node dest path' = Some first_bound
      -> has_strictly_decreasing_costs topology paths costs path dest first_bound
      -> ~In node path.
  Proof.
    intros.
    dependent induction path; intros; simpl; try tauto.
    simpl in H1.
    destruct_with_eqn (paths a dest); try tauto.
    destruct_with_eqn (path_cost topology costs a dest l); try tauto.
    destruct H1.
    unfold not.
    intros.
    destruct H3.
    - subst.
      rewrite Heqo in H.
      injection H.
      intros.
      subst.
      rewrite Heqo0 in H0.
      assert (n = first_bound) by (injection H0; intros; tauto).
      omega.
    - enough (~(In node path)) by tauto.
      eapply IHpath; try eassumption.
      apply strictly_decreasing_costs_strengthening with (small_bound := n); try assumption.
      omega.
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
    all_pairs_paths_valid topology policy paths
      -> next_node_valid topology policy (all_pairs_paths_next_node_generator paths topology policy).
  Proof.
    intros.
    constructor; intros.
    - unfold all_pairs_paths_next_node_generator in H0.
      destruct H0.
      apply paths_in_topology with (src := here) (dest := current_flow.(Dest)) in H.
      destruct (paths here current_flow.(Dest)); try tauto.
      destruct l; subst; try assumption.
      simpl in H.
      tauto.
    - constructor.
      + intros.
        apply all_pairs_paths_next_node_generator_creates_next_node_paths; try assumption.
        eapply paths_exist_for_valid_flows in H; try eassumption.
      + intros.
        destruct H1.
        destruct x; simpl in H1; unfold all_pairs_paths_next_node_generator in H1; tauto.
    - unfold all_pairs_paths_next_node_generator in H1.
      destruct H1.
      destruct hop_target.
      + apply all_pairs_paths_next_node_generator_creates_next_node_paths; try tauto.
        destruct_with_eqn (paths here current_flow.(Dest)); try tauto.
        destruct l; try discriminate.
        assert (s0 = s) by congruence; subst.
        apply paths_move_closer_to_destination in H.
        destruct H.
        destruct H.
        specialize (H3 here).
        specialize (H3 current_flow.(Dest)).
        rewrite Heqo in H3.
        destruct (paths s current_flow.(Dest)); tauto.
      + destruct (paths here current_flow.(Dest)); try tauto.
        destruct l; try discriminate.
        congruence.
    - dependent induction path; try apply NoDup_single.
      simpl in H0.
      destruct H0.
      unfold all_pairs_paths_next_node_generator in H0.
      destruct H0.
      destruct_with_eqn (paths here current_flow.(Dest)); try tauto.
      destruct l; try discriminate.
      assert (a = s) by congruence; subst.
      assert (H1' := H1).
      apply IHpath in H1.
      constructor; try assumption.
      unfold not.
      intros.
      destruct H3.
      + subst.
        apply paths_move_closer_to_destination in H.
        destruct H.
        destruct H.
        specialize (H3 here).
        specialize (H3 current_flow.(Dest)).
        repeat rewrite Heqo in H3.
        simpl in H3.
        destruct (topology (SwitchNode here) (SwitchNode here)); try tauto.
        destruct (path_cost topology x here current_flow.(Dest) l); try tauto.
        omega.
      + enough (~(In here path)) by tauto.
        apply paths_move_closer_to_destination in H.
        destruct H.
        assert (H' := H).
        unfold generates_decreasing_costs in H'.
        destruct H'.
        specialize (H5 here).
        specialize (H5 current_flow.(Dest)).
        rewrite Heqo in H5.
        repeat match goal with
        | [ H : match ?x with | Some _ => _ | None => False end |- _ ] => destruct_with_eqn (x); try tauto
        end.
        eapply decreasing_costs_implies_nonmember with (costs := x); try eassumption.
        apply strictly_decreasing_costs_strengthening with (small_bound := n); try omega.
        eapply partial_all_pairs_paths_generate_strictly_decreasing_costs; try eassumption.
    - unfold all_pairs_paths_next_node_generator in H0.
      destruct H0.
      destruct_with_eqn (paths here current_flow.(Dest)); try tauto.
      destruct l; try discriminate.
      congruence.
  Qed.

  Definition all_pairs_paths_dec_next_node_generator
    (paths : all_pairs_paths)
    (topology : network_topology)
    (policy : static_network_policy)
    here
    current_flow
  :=
    if policy current_flow then
      match paths here current_flow.(Dest) with
      | Some (hop_target :: _) => Some (SwitchNode hop_target)
      | Some [] => Some (HostNode current_flow.(Dest))
      | None => None
      end
    else None.

  Lemma is_next_node_path_weakening : forall (strict_next lenient_next : next_node) path here current_flow,
    is_next_node_path strict_next path here current_flow
      -> (forall here' current_flow' hop_target, strict_next here' current_flow' hop_target -> lenient_next here' current_flow' hop_target)
      -> is_next_node_path lenient_next path here current_flow.
  Proof.
    intros.
    dependent induction path; simpl; simpl in H; eauto.
    destruct H.
    assert (H0' := H0).
    apply IHpath with (here := a) (current_flow := current_flow) in H0; try tauto.
    constructor; try tauto.
    apply H0'; assumption.
  Qed.

  Lemma is_partial_next_node_path_weakening : forall (strict_next lenient_next : next_node) path here end_switch current_flow,
    is_partial_next_node_path strict_next path here end_switch current_flow
      -> (forall here' current_flow' hop_target, strict_next here' current_flow' hop_target -> lenient_next here' current_flow' hop_target)
      -> is_partial_next_node_path lenient_next path here end_switch current_flow.
  Proof.
    intros.
    dependent induction path; simpl; simpl in H; eauto.
    destruct H.
    assert (H0' := H0).
    apply IHpath with (here := a) (end_switch := end_switch) (current_flow := current_flow) in H0; try tauto.
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
      + apply path_exists_only_for_valid_flows0 in H1; try assumption.
        apply H1 in H0.
        destruct H0.
        exists x.
        eapply is_next_node_path_weakening; try eassumption; apply H.
      + apply path_exists_only_for_valid_flows0 in H1.
        apply H1.
        destruct H0.
        exists x.
        eapply is_next_node_path_weakening; try eassumption; apply H.
    - apply H in H2.
      apply no_black_holes0 in H2; try assumption.
      destruct hop_target; try assumption.
      destruct H2.
      exists x.
      eapply is_next_node_path_weakening; try eassumption; apply H.
    - eapply is_partial_next_node_path_weakening in H1; try apply H.
      apply all_paths_acyclic0 in H1.
      assumption.
    - eapply forwards_to_correct_host0; apply H; eassumption.
  Qed.

  Theorem all_pairs_paths_dec_generator_valid : forall paths topology policy,
    all_pairs_paths_valid topology policy paths
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

  Definition routing_tables := Switch -> list (flow * Node).

  Record routing_tables_valid (tables : routing_tables) (dec_next : dec_next_node) := {
    no_duplicate_entries : forall here,
      NoDup (tables here);

    entries_match_next_node_result : forall here current_flow hop_target,
      dec_next here current_flow = Some hop_target
        <-> In (current_flow, hop_target) (tables here)
  }.

  Definition routing_tables_generator := dec_next_node -> list Node -> routing_tables.

  Definition routing_tables_generator_valid (generator : routing_tables_generator) := forall dec_next all_nodes,
    Listing all_nodes
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

  Lemma map_filter_nodup_preservation : forall A B (mapper: A -> option B) l,
    (forall (x y : A),
        match mapper x, mapper y with
        | Some x', Some y' => x' = y'
        | _, _ => False
        end -> x = y
      )
      -> NoDup l
      -> NoDup (map_filter mapper l).
  Proof.
    intros.
    dependent induction l; [apply NoDup_nil | idtac].
    inversion_clear H0.
    simpl.
    destruct_with_eqn (mapper a); try (apply IHl; assumption).
    apply NoDup_cons; try (apply IHl; assumption).
    unfold not; intros.
    clear IHl.
    dependent induction l; try tauto.
    inversion_clear H2.
    simpl in H0, H1.
    apply IHl with (b := b); try tauto.
    destruct_with_eqn (mapper a0); simpl in H0; try assumption.
    destruct H0; try assumption; subst.
    enough (a0 = a) by firstorder.
    apply H.
    rewrite Heqo, Heqo0.
    reflexivity.
  Qed.

  Lemma map_filter_in_filtering : forall A B mapper l (result : B),
    (forall (x y : B), {x = y} + {x <> y})
      -> In result (map_filter mapper l)
      -> {element : A | mapper element = Some result}.
  Proof.
    intros.
    dependent induction l; try (simpl in H; tauto).
    simpl in H.
    destruct_with_eqn (mapper a).
    - assert ({b = result} + {b <> result}) by apply X.
      destruct H0.
      + subst.
        apply exist with (x := a).
        assumption.
      + simpl in H.
        apply IHl; try assumption.
        destruct H; tauto.
    - apply IHl; assumption.
  Qed.

  Fixpoint max_by {A} (mapper : A -> nat) (l : list A) default :=
    match l with
    | [] => default
    | car :: cdr =>
      if (mapper car) <? mapper (max_by mapper cdr default)
      then max_by mapper cdr default
      else car
    end.

  Lemma max_by_maximum {A} : forall (mapper : A -> nat) default l element,
    In element l
      -> mapper element <= mapper (max_by mapper l default).
  Proof.
    intros; dependent induction l; inversion_clear H; subst; simpl; repeat progress match goal with
    | [ |- context[if ?cond then _ else _] ] => destruct_with_eqn (cond)
    | [ H : _ <? _ = true |- _ ] => rewrite Nat.ltb_lt in H
    | [ H : ?a <? ?b = false |- _ ] => assert (~a < b) by (rewrite <- Nat.ltb_lt; congruence); clear H
    | [ IH : forall e : ?type, In e ?l -> _, element : ?type, H : In ?element ?l |- _ ] => specialize (IH element); specialize (IH H)
    end; try omega.
  Qed.

  Lemma in_split {A} : forall (element : A) l,
    In element l
      -> exists front back, l = (front ++ element :: back).
  Proof.
    intros.
    dependent induction l generalizing element; inversion_clear H.
    - subst.
      exists [], l.
      reflexivity.
    - apply IHl in H0.
      destruct H0.
      destruct H.
      subst.
      exists (a :: x), x0.
      reflexivity.
  Qed.

  Lemma pidgeonhole_principle : forall {A} (big_list small_list : list A),
    (forall element, In element small_list -> In element big_list)
      -> NoDup small_list
      -> length small_list <= length big_list.
  Proof.
    intros.
    dependent induction small_list generalizing big_list; simpl; try omega.
    inversion_clear H0.
    assert (In a big_list) by (apply H; simpl; tauto).
    apply in_split in H0.
    destruct H0.
    destruct H0.
    subst.
    assert (length (x ++ a :: x0) = S (length (x ++ x0))) by (clear; dependent induction x; simpl; eauto).
    rewrite H0.
    enough (length small_list <= length (x ++ x0)) by omega.
    apply IHsmall_list; try assumption.
    intros.
    specialize (H element).
    assert (In element (a :: small_list)) by (simpl; tauto).
    apply H in H4.
    assert (element <> a) by (unfold not; intros; subst; tauto).
    clear - H4 H5.
    dependent induction x; simpl in *; destruct H4; eauto; congruence.
  Qed.

  Hypothesis Switch_eq_dec : forall x y : Switch, {x = y} + {x <> y}.
  Hypothesis Host_eq_dec : forall x y : Host, {x = y} + {x <> y}.

  Ltac combined_eq_dec combined_type :=
    intros; repeat match goal with
    | [ x : combined_type |- _ ] => destruct x
    | [ |- {?x = ?x} + {_} ] => constructor 1; reflexivity
    | [ H : ?x <> ?y |- {_} + {?constr ?x <> ?constr ?y} ] => constructor 2; congruence
    | [ H : ?x <> ?y |- {_} + {?constr _ ?x <> ?constr _ ?y} ] => constructor 2; congruence
    | [ H : ?x <> ?y |- {_} + {?constr ?x _ <> ?constr ?y _} ] => constructor 2; congruence
    | [ H : forall a b : ?type, {a = b} + {a <> b}, x : ?type, y : ?type |- {?constr ?x = ?constr ?y} + {?constr ?x <> ?constr ?y} ] => destruct (H x y); subst
    | [ H : forall a b : ?type, {a = b} + {a <> b}, w : ?type, x : ?type, y : ?type, z : ?type |- {?constr ?w ?x = ?constr ?y ?z} + {?constr ?w ?x <> ?constr ?y ?z} ] => destruct (H w y), (H x z); subst
    | [ H1 : forall a b : ?type1, {a = b} + {a <> b}, H2 : forall a b : ?type2, {a = b} + {a <> b}, w : ?type1, x : ?type2, y : ?type1, z : ?type2 |- {?constr ?w ?x = ?constr ?y ?z} + {?constr ?w ?x <> ?constr ?y ?z} ] => destruct (H1 w y), (H2 x z); subst
    end; constructor 2; discriminate.

  Definition Node_eq_dec : forall x y : Node, {x = y} + {x <> y}.
  Proof.
    combined_eq_dec Node.
  Defined.

  Definition Host_pair_eq_dec : forall x y : (Host * Host), {x = y} + {x <> y}.
  Proof.
    combined_eq_dec (prod Host Host).
  Defined.

  Definition flow_eq_dec : forall x y : flow, {x = y} + {x <> y}.
  Proof.
    assert (Host_eq_dec := Host_eq_dec).
    combined_eq_dec flow.
  Defined.

  Definition flow_Node_pair_eq_dec : forall x y : (flow * Node), {x = y} + {x <> y}.
  Proof.
    assert (Node_eq_dec := Node_eq_dec).
    assert (flow_eq_dec := flow_eq_dec).
    combined_eq_dec (prod flow Node).
  Defined.

  Definition is_host node :=
    match node with
    | HostNode _ => true
    | SwitchNode _ => false
    end.

  Definition is_switch node :=
    match node with
    | HostNode _ => false
    | SwitchNode _ => true
    end.

  Definition filter_hosts :=
    map_filter (fun node =>
      match node with
      | HostNode host => Some host
      | SwitchNode _ => None
      end
    ).

  Definition filter_switches :=
    map_filter (fun node =>
      match node with
      | HostNode _ => None
      | SwitchNode switch => Some switch
      end
    ).

  Lemma filter_listing_nodes : forall all_nodes,
    Listing all_nodes
      -> Listing (filter_switches all_nodes) /\ Listing (filter_hosts all_nodes).
  Proof.
    intros; constructor; constructor; unfold Listing; match goal with
    | [ all_nodes : list Node, H : Listing ?all_nodes |- Full _ ] =>
      unfold Full; intros; match goal with
      | [ |- In ?a (filter_hosts all_nodes) ] => apply map_filter_in_preservation with (element := HostNode a)
      | [ |- In ?a (filter_switches all_nodes) ] => apply map_filter_in_preservation with (element := SwitchNode a)
      end; try apply H; try apply Node_eq_dec; reflexivity
    | [ all_nodes : list Node, H : Listing ?all_nodes |- NoDup _ ] =>
      apply proj1 in H; apply map_filter_nodup_preservation; try assumption;
      intros; repeat match goal with
      | [ x : Node |- _ ] => destruct x
      end; subst; tauto
    end.
  Qed.

  Definition exhaustive_routing_tables_generator (dec_next : dec_next_node) (all_nodes : list Node) (here : Switch) :=
    let all_hosts := filter_hosts all_nodes
    in map_filter (fun pair =>
      match dec_next here {| Src := pair.(fst); Dest := pair.(snd) |} with
      | Some hop_target => Some ({| Src := pair.(fst); Dest := pair.(snd) |}, hop_target)
      | None => None
      end
    ) (nodup Host_pair_eq_dec (list_prod all_hosts all_hosts)).

  Theorem exhaustive_routing_tables_generator_valid : routing_tables_generator_valid exhaustive_routing_tables_generator.
  Proof.
    unfold exhaustive_routing_tables_generator.
    constructor; intros.
    - remember (nodup Host_pair_eq_dec (list_prod (filter_hosts all_nodes) (filter_hosts all_nodes))) as pairs.
      assert (NoDup pairs) by (subst; apply NoDup_nodup).
      clear H Heqpairs.
      dependent induction pairs; try apply NoDup_nil.
      simpl.
      inversion_clear H0; subst.
      destruct a; simpl.
      destruct (dec_next here {| Src := h; Dest := h0 |}); try (apply IHpairs; assumption).
      constructor; try (apply IHpairs; assumption).
      clear IHpairs.
      dependent induction pairs; try (simpl; tauto).
      inversion_clear H1; subst.
      simpl.
      destruct (dec_next here {| Src := a.(fst); Dest := a.(snd) |}).
      + simpl.
        unfold not.
        intros.
        destruct a.
        destruct H1.
        * injection H1.
          intros.
          subst.
          apply H0.
          simpl in H.
          tauto.
        * apply IHpairs in H1; try assumption.
          simpl in H.
          tauto.
      + simpl in H.
        apply IHpairs; tauto.
    - constructor; intros.
      + apply map_filter_in_preservation with (element := (current_flow.(Src), current_flow.(Dest))).
        * apply Host_pair_eq_dec.
        * destruct current_flow.
          simpl.
          rewrite H0.
          reflexivity.
        * assert (Listing (filter_hosts all_nodes)) by (apply filter_listing_nodes in H; tauto).
          apply nodup_In, in_prod; apply H1.
      + apply map_filter_in_filtering in H0; try apply flow_Node_pair_eq_dec.
        destruct H0.
        assert (x = (current_flow.(Src), current_flow.(Dest))).
        * destruct (dec_next here {| Src := x.(fst); Dest := x.(snd) |}); try discriminate.
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
          congruence.
  Qed.

  Section OpenFlow.
    Definition ipv4_address : Type := word 8 * word 8 * word 8 * word 8.

    Definition ipv4_eqb (ip1 ip2 : ipv4_address) : bool :=
      match ip1, ip2 with
      | (a1, b1, c1, d1), (a2, b2, c2, d2) => weqb a1 a2 && weqb b1 b2 && weqb c1 c2 && weqb d1 d2
      end.

    Lemma ipv4_eqb_iff : forall ip1 ip2, ipv4_eqb ip1 ip2 = true <-> ip1 = ip2.
    Proof.
      intros; constructor.
      - intros; unfold ipv4_eqb in H; repeat match goal with
        | [ H : context[let (_, _) := ?i in _] |- _ ] => destruct i
        | [ H : (_ && _)%bool = true |- _ ] => unfold andb in H
        | [ H : (if ?e then ?f else false) = true |- _ ] => assert (e = true) by (destruct e; [reflexivity | discriminate]); assert (f = true) by (destruct e; [assumption | discriminate]); clear H
        | [ H : weqb ?a ?b = true |- _ ] => apply weqb_true_iff in H
        end; subst; reflexivity.
      - intros; unfold ipv4_eqb; repeat match goal with
        | [ |- context[let (_, _) := ?i in _] ] => destruct i
        | [ |- (_ && _)%bool = true ] => unfold andb
        | [ |- weqb ?w ?w = true ] => apply weqb_true_iff; reflexivity
        | [ H : weqb ?w ?w = true |- context[if weqb ?w ?w then _ else _] ] => rewrite H
        | [ |- context[if weqb ?w ?w then _ else _] ] => assert (weqb w w = true)
        | [ H : (?a, ?b, ?c, ?d) = (?e, ?f, ?g, ?h) |- _ ] => injection H; clear H; intros; subst
        end.
    Qed.

    Lemma ipv4_eqb_refl : forall ip, ipv4_eqb ip ip = true.
    Proof.
      intros.
      apply ipv4_eqb_iff.
      reflexivity.
    Qed.

    Record ipv4_packet := {
      IpSrc : ipv4_address;
      IpDest : ipv4_address
      (* Other fields exist but are not used here *)
    }.


    (* OpenFlow switch spec: https://www.opennetworking.org/wp-content/uploads/2013/04/openflow-spec-v1.0.0.pdf *)

    Record header_fields_matcher := {
      (* TODO: support IP wildcard matchers *)
      IpSrcMatcher : option ipv4_address;
      IpDestMatcher : option ipv4_address
      (* Other header fields exist but are not used here *)
    }.

    Inductive openflow_pseudo_action :=
    | ForwardToSwitch : Port -> openflow_pseudo_action
    | ForwardToDest : Port -> openflow_pseudo_action
    | Drop
    .

    Record openflow_flow_entry := {
      header_fields : header_fields_matcher;
      action : openflow_pseudo_action
      (* Entries also contain "counters" which are not used here *)
    }.

    Definition matches_header_fields_matcher (packet : ipv4_packet) (matcher : header_fields_matcher) : bool :=
      match matcher.(IpSrcMatcher) with
      | Some src_address => ipv4_eqb src_address packet.(IpSrc)
      | None => true
      end &&
      match matcher.(IpDestMatcher) with
      | Some dest_address => ipv4_eqb dest_address packet.(IpDest)
      | None => true
      end.

    Fixpoint get_matching_action packet openflow_flow_entries :=
      match openflow_flow_entries with
      | [] => Drop
      | entry :: cdr =>
        if matches_header_fields_matcher packet entry.(header_fields)
        then entry.(action)
        else get_matching_action packet cdr
      end.

    Definition host_ip_map := Host -> ipv4_address.
    Definition switch_openflow_entry_map := Switch -> list openflow_flow_entry.

    Section OpenFlowNetwork.
      Variable host_ip : host_ip_map.
      Variable entries : switch_openflow_entry_map.
      Variable topology : network_topology.
      Variable packet : ipv4_packet.

      Inductive openflow_network_packet_state :=
      | NotSentYet
      | EnRoute : Switch -> openflow_network_packet_state
      | ReceivedAtHost : Host -> openflow_network_packet_state
      | Arrived
      | Dropped
      .

      Inductive openflow_network_step : openflow_network_packet_state -> openflow_network_packet_state -> Prop :=
      | EmitPacketFromSrc : forall port src_host first_switch,
        src_host.(host_ip) = packet.(IpSrc)
          -> topology (HostNode src_host) (SwitchNode first_switch) = Some port
          -> openflow_network_step NotSentYet (EnRoute first_switch)
      | ForwardPacketToSwitch : forall port current_switch new_switch,
        get_matching_action packet current_switch.(entries) = ForwardToSwitch port
          -> topology (SwitchNode current_switch) (SwitchNode new_switch) = Some port
          -> openflow_network_step (EnRoute current_switch) (EnRoute new_switch)
      | ForwardPacketToDest : forall port current_switch dest_host,
        get_matching_action packet current_switch.(entries) = ForwardToDest port
          -> topology (SwitchNode current_switch) (HostNode dest_host) = Some port
          -> openflow_network_step (EnRoute current_switch) (ReceivedAtHost dest_host)
      | DropPacketAtSwitch : forall current_switch,
        get_matching_action packet current_switch.(entries) = Drop
          -> openflow_network_step (EnRoute current_switch) Dropped
      | AcceptPacket : forall dest_host,
        dest_host.(host_ip) = packet.(IpDest)
          -> openflow_network_step (ReceivedAtHost dest_host) Arrived
      .

      Fixpoint always_reaches_state_after_bounded_steps desired_state num_steps current_state : Prop :=
        desired_state = current_state \/
        match num_steps with
        | 0 => False
        | S num_steps' =>
          (exists new_state, openflow_network_step current_state new_state) /\
          forall new_state,
            openflow_network_step current_state new_state
              -> always_reaches_state_after_bounded_steps desired_state num_steps' new_state
        end.
    End OpenFlowNetwork.

    Definition generate_openflow_entries
      (tables : routing_tables)
      (host_ip : host_ip_map)
      (topology : network_topology)
      (switch : Switch)
    :=
      map (fun pair => {|
        header_fields := {|
          IpSrcMatcher := Some pair.(fst).(Src).(host_ip);
          IpDestMatcher := Some pair.(fst).(Dest).(host_ip)
        |};
        action := match topology (SwitchNode switch) pair.(snd) with
        | Some port =>
          if is_switch pair.(snd)
          then ForwardToSwitch port
          else ForwardToDest port

        (* Impossible if `tables` is valid for the topology *)
        | None => Drop
        end
      |}) (tables switch).

    Fixpoint all_ports_exist (topology : network_topology) switch entries :=
      match entries with
      | [] => True
      | entry :: cdr =>
        match entry.(action) with
        | ForwardToSwitch port
        | ForwardToDest port => exists hop_target, topology (SwitchNode switch) hop_target = Some port
        | Drop => True
        end /\ all_ports_exist topology switch cdr
      end.

    Record valid_openflow_entries (topology : network_topology) (policy : static_network_policy) (host_ip : host_ip_map) (entries : switch_openflow_entry_map) : Prop := {
      packets_arrive_iff_allowed : forall packet src_node dest_node,
        src_node.(host_ip) = packet.(IpSrc)
          -> dest_node.(host_ip) = packet.(IpDest)
          -> exists num_steps,

            (* Note: If the source/dest node have the same IP (or are the same node), this will always be true if num_steps >= 1 *)
            always_reaches_state_after_bounded_steps
              host_ip
              entries
              topology
              packet
              (if policy {| Src := src_node; Dest := dest_node |} then Arrived else Dropped)
              num_steps
              NotSentYet;
      existent_ports : forall switch, all_ports_exist topology switch switch.(entries)
    }.

    Record flow_transition_system {state} := {
      Initial : state;
      (* TODO: incorporate wall clock time *)
      Step : state -> flow -> state
    }.

    Arguments flow_transition_system : clear implicits.

    Definition join_transition_systems {A} {B} (sys1 : flow_transition_system A) (sys2 : flow_transition_system B) :=
      {|
        Initial := (sys1.(Initial), sys2.(Initial));
        Step := fun current_state next_flow => (Step sys1 current_state.(fst) next_flow, Step sys2 current_state.(snd) next_flow)
      |}.

    Inductive trc {state : Set} (step : state -> flow -> state) : state -> state -> Prop :=
    | TrcRefl : forall (start : state), trc step start start
    | TrcFront : forall start mid dest sent_flow,
      step start sent_flow = mid
        -> trc step mid dest
        -> trc step start dest
    .

    Arguments trc {state} step.

    Definition invariant {state : Set} (sys : flow_transition_system state) (condition : state -> Prop) := forall new_state,
      trc sys.(Step) sys.(Initial) new_state
        -> condition new_state.

    Lemma invariant_weakening {state : Set} : forall sys (weak_condition strong_condition : state -> Prop),
      invariant sys strong_condition
        -> (forall s, strong_condition s -> weak_condition s)
        -> invariant sys weak_condition.
    Proof.
      unfold invariant; eauto.
    Qed.

    Record dynamic_network_policy {policy_state : Set} := {
      policy_system : flow_transition_system policy_state;

      policy_state_decider : policy_state -> static_network_policy
    }.

    Definition filter_transition_system {state} (predicate : state -> flow -> bool) (sys : flow_transition_system state) :=
      {|
        Initial := sys.(Initial);
        Step := fun current_state next_flow =>
          if predicate current_state next_flow
          then sys.(Step) current_state next_flow
          else current_state
      |}.

    Lemma filter_transition_system_trc {state : Set} : forall predicate (sys : flow_transition_system state) new_state,
      let filtered_sys := filter_transition_system predicate sys in
      trc filtered_sys.(Step) filtered_sys.(Initial) new_state
        -> trc sys.(Step) sys.(Initial) new_state.
    Proof.
      intros.
      unfold filtered_sys, filter_transition_system in H.
      simpl in H.
      clear filtered_sys.
      remember sys.(Initial) as start_state; clear Heqstart_state.
      dependent induction H; try apply TrcRefl.
      destruct (predicate start sent_flow).
      - eapply TrcFront; eassumption.
      - subst; assumption.
    Qed.

    Section NetworkSystem.
      Context {policy_state : Set}.
      Variable topology : network_topology.
      Variable policy : @dynamic_network_policy policy_state.
      Variable node_ip : host_ip_map.

      Record network_controller {controller_state} := {
        controller_system : flow_transition_system controller_state;

        controller_state_decider : controller_state -> switch_openflow_entry_map
      }.

      Definition dynamic_policy_valid paths :=
        let filtered_policy_sys := filter_transition_system policy.(policy_state_decider) policy.(policy_system) in
        invariant filtered_policy_sys (fun current_state =>
          all_pairs_paths_valid topology (policy.(policy_state_decider) current_state) paths
        ).

      Definition controller_implements_policy {controller_state : Set} (controller : @network_controller controller_state) :=
        let joined_sys := filter_transition_system (fun current_state next_flow =>

          (* state only changes for flows that are allowed by the current policy *)
          policy.(policy_state_decider) current_state.(fst) next_flow
        ) (join_transition_systems policy.(policy_system) controller.(controller_system)) in
        invariant joined_sys (fun policy_and_controller_state =>
          let (policy_state, controller_state) := policy_and_controller_state in
          valid_openflow_entries topology (policy.(policy_state_decider) policy_state) node_ip (controller.(controller_state_decider) controller_state)
        ).
    End NetworkSystem.

    Ltac get_matching_action_unequal_induction host_ip Heqb IHl Src0 Src1 Dest0 Dest1 :=
      let H' := fresh "H'" in
      assert (H' : Src0 <> Src1 \/ Dest0 <> Dest1) by (destruct (Host_eq_dec Src0 Src1), (Host_eq_dec Dest0 Dest1); subst; tauto);
      destruct H';
      unfold matches_header_fields_matcher;
      simpl;
      match goal with
      | [ H : Src0 <> Src1 |- _ ] => destruct_with_eqn (ipv4_eqb Src1.(host_ip) Src0.(host_ip))
      | [ H : Dest0 <> Dest1 |- _ ] => destruct_with_eqn (ipv4_eqb Dest1.(host_ip) Dest0.(host_ip))
      end;
      match goal with
      | [ H : Injective host_ip |- _ ] => try (apply ipv4_eqb_iff, H in Heqb; congruence)
      end;
      match goal with
      | [ |- context[_ && false] ] => rewrite andb_false_r
      | _ => simpl
      end;
      apply IHl;
      intros;
      constructor;
      intros;
      match goal with
      | [ H : forall h, ?next = Some h <-> In (?f, h) _ |- _ ] =>
        match goal with
        | [ |- next = Some _ ] => apply H; constructor 2; assumption
        | [ H2 : next = Some ?hop |- In (f, ?hop) _ ] => apply H in H2; inversion_clear H2; congruence
        end
      end.

    Lemma get_matching_action_forwards_to_correct_port : forall topology (dec_next : dec_next_node) current_flow (here : Switch) hop_target port host_ip all_nodes,
      dec_next here current_flow = Some hop_target
        -> topology (SwitchNode here) hop_target = Some port
        -> Injective host_ip
        -> Listing all_nodes
        -> routing_tables_valid (exhaustive_routing_tables_generator dec_next all_nodes) dec_next
        -> get_matching_action
          {| IpSrc := current_flow.(Src).(host_ip); IpDest := current_flow.(Dest).(host_ip) |}
          (generate_openflow_entries (exhaustive_routing_tables_generator dec_next all_nodes) host_ip topology here)
          = if is_switch hop_target then ForwardToSwitch port else ForwardToDest port.
    Proof.
      intros.
      assert (forall hop, dec_next here current_flow = Some hop <-> In (current_flow, hop) (exhaustive_routing_tables_generator dec_next all_nodes here)) by (intros; apply entries_match_next_node_result; assumption).
      clear H3.
      unfold generate_openflow_entries.
      induction (exhaustive_routing_tables_generator dec_next all_nodes here); [ apply H4 in H; inversion H | idtac ].
      simpl.
      destruct a.
      assert ({current_flow = f} + {current_flow <> f}) by (apply flow_eq_dec).
      destruct H3.
      - destruct current_flow, f; injection e; intros; subst; simpl.
        unfold matches_header_fields_matcher.
        simpl.
        repeat rewrite ipv4_eqb_refl.
        simpl.
        enough (hop_target = n) by (rewrite <- H3, H0; reflexivity).
        enough (Some hop_target = Some n) by (injection H3; tauto).
        rewrite <- H.
        apply H4.
        constructor.
        reflexivity.
      - destruct current_flow, f.
        get_matching_action_unequal_induction host_ip Heqb IHl Src0 Src1 Dest0 Dest1.
    Qed.

    Lemma get_matching_action_drops : forall topology dec_next current_flow here host_ip all_nodes,
      dec_next here current_flow = None
        -> Injective host_ip
        -> Listing all_nodes
        -> routing_tables_valid (exhaustive_routing_tables_generator dec_next all_nodes) dec_next
        -> get_matching_action
          {| IpSrc := current_flow.(Src).(host_ip); IpDest := current_flow.(Dest).(host_ip) |}
          (generate_openflow_entries (exhaustive_routing_tables_generator dec_next all_nodes) host_ip topology here)
          = Drop.
    Proof.
      intros.
      assert (forall hop, dec_next here current_flow = Some hop <-> In (current_flow, hop) (exhaustive_routing_tables_generator dec_next all_nodes here)) by (intros; apply entries_match_next_node_result; assumption).
      clear H2.
      unfold generate_openflow_entries.
      simpl.
      unfold matches_header_fields_matcher.
      induction (exhaustive_routing_tables_generator dec_next all_nodes here); try reflexivity.
      simpl.
      unfold matches_header_fields_matcher.
      destruct a.
      simpl.
      assert (H' : {current_flow = f} + {current_flow <> f}) by (apply flow_eq_dec); destruct H'.
      - subst.
        assert (dec_next here f = Some n) by (apply H3; simpl; tauto).
        rewrite H2 in H.
        discriminate.
      - destruct current_flow, f.
        get_matching_action_unequal_induction host_ip Heqb IHl Src0 Src1 Dest0 Dest1.
    Qed.

    Lemma dec_next_creates_valid_unique_state_transitions : forall topology policy dec_next host_ip (packet : ipv4_packet) here current_flow all_nodes entries,
      dec_next_node_valid topology policy dec_next
        -> valid_topology topology
        -> Listing all_nodes
        -> Injective host_ip
        -> entries = generate_openflow_entries (exhaustive_routing_tables_generator dec_next all_nodes) host_ip topology
        -> packet = {| IpSrc := current_flow.(Src).(host_ip); IpDest := current_flow.(Dest).(host_ip) |}
        -> (
          (exists new_state, openflow_network_step host_ip entries topology packet (EnRoute here) new_state) /\
          forall new_state,
            openflow_network_step host_ip entries topology packet (EnRoute here) new_state
              -> new_state =
                  match dec_next here current_flow with
                  | Some (SwitchNode hop_target) => EnRoute hop_target
                  | Some (HostNode hop_target) => ReceivedAtHost hop_target
                  | None => Dropped
                  end
        ).
    Proof.
      intros.
      assert (routing_tables_valid (exhaustive_routing_tables_generator dec_next all_nodes) dec_next) by (apply exhaustive_routing_tables_generator_valid; assumption).
      constructor; destruct_with_eqn (dec_next here current_flow).
      - destruct n.
        + exists (EnRoute s).
          apply all_hops_in_topology with (topology := topology) (policy := policy) (here := here) (hop_target := SwitchNode s) (current_flow := current_flow) in H; try assumption.
          destruct_with_eqn (topology (SwitchNode here) (SwitchNode s)); try tauto.
          apply ForwardPacketToSwitch with (port := p); try assumption.
          subst.
          apply get_matching_action_forwards_to_correct_port with (hop_target := SwitchNode s); assumption.
        + exists (ReceivedAtHost h).
          apply all_hops_in_topology with (topology := topology) (policy := policy) (here := here) (hop_target := HostNode h) (current_flow := current_flow) in H; try assumption.
          destruct_with_eqn (topology (SwitchNode here) (HostNode h)); try tauto.
          apply ForwardPacketToDest with (port := p) (dest_host := h); try assumption.
          subst.
          apply get_matching_action_forwards_to_correct_port with (hop_target := HostNode h); assumption.
      - exists Dropped.
        subst.
        constructor; simpl; try (apply get_matching_action_drops; assumption).
      - intros.

        apply all_hops_in_topology with (topology := topology) (policy := policy) (here := here) (hop_target := n) (current_flow := current_flow) in H; try assumption.
        destruct_with_eqn (topology (SwitchNode here) n); try tauto.
        assert (
          get_matching_action
            {| IpSrc := current_flow.(Src).(host_ip); IpDest := current_flow.(Dest).(host_ip) |}
            (generate_openflow_entries (exhaustive_routing_tables_generator dec_next all_nodes) host_ip topology here)
          = if is_switch n then ForwardToSwitch p else ForwardToDest p
        ) by (apply get_matching_action_forwards_to_correct_port with (hop_target := n); assumption).
        inversion_clear H6; subst; rewrite H8 in H7; destruct (is_switch n); try discriminate; injection H7; intros; subst.

        + enough (n = SwitchNode new_switch) by (subst; reflexivity).
          apply no_duplicate_ports with (node := SwitchNode here) (outgoing1 := n) (outgoing2 := SwitchNode new_switch) in H0.
          rewrite Heqo0, H9 in H0.
          apply H0.
          reflexivity.
        + enough (n = HostNode dest_host) by (subst; reflexivity).
          apply no_duplicate_ports with (node := SwitchNode here) (outgoing1 := n) (outgoing2 := HostNode dest_host) in H0.
          rewrite Heqo0, H9 in H0.
          apply H0.
          reflexivity.
      - intros.
        assert (
          get_matching_action
            {| IpSrc := current_flow.(Src).(host_ip); IpDest := current_flow.(Dest).(host_ip) |}
            (generate_openflow_entries (exhaustive_routing_tables_generator dec_next all_nodes) host_ip topology here)
          = Drop
        ) by (apply get_matching_action_drops; assumption).
        inversion_clear H6; subst; try reflexivity; rewrite H7 in H8; discriminate.
    Qed.

    Lemma reaches_arrived_state_from_destination_in_one_step : forall host_ip topology tables src_host dest_host,
      always_reaches_state_after_bounded_steps
        host_ip
        (generate_openflow_entries tables host_ip topology)
        topology
        {| IpSrc := src_host.(host_ip); IpDest := dest_host.(host_ip) |}
        Arrived
        1
        (ReceivedAtHost dest_host).
    Proof.
      intros.
      simpl.
      apply or_intror.
      constructor.
      - exists Arrived.
        constructor.
        reflexivity.
      - intros.
        apply or_introl.
        inversion_clear H; reflexivity.
    Qed.

    Lemma always_reaches_state_after_bounded_steps_weakening : forall host_ip entries topology packet desired_state big_num_steps small_num_steps current_state,
      always_reaches_state_after_bounded_steps host_ip entries topology packet desired_state small_num_steps current_state
        -> small_num_steps <= big_num_steps
        -> always_reaches_state_after_bounded_steps host_ip entries topology packet desired_state big_num_steps current_state.
    Proof.
      intros.
      dependent induction small_num_steps generalizing big_num_steps.
      - simpl in H.
        destruct H; try tauto.
        destruct big_num_steps; simpl; tauto.
      - destruct big_num_steps; try omega.
        simpl.
        destruct H; [ apply or_introl | apply or_intror ]; try assumption.
        destruct H.
        constructor; try assumption.
        intros.
        apply IHsmall_num_steps.
        + apply H1; assumption.
        + omega.
    Qed.

    Lemma always_reaches_state_after_bounded_steps_combination : forall host_ip entries topology packet start_state mid_state end_state bound1 bound2,
      always_reaches_state_after_bounded_steps host_ip entries topology packet mid_state bound1 start_state
        -> always_reaches_state_after_bounded_steps host_ip entries topology packet end_state bound2 mid_state
        -> always_reaches_state_after_bounded_steps host_ip entries topology packet end_state (bound1 + bound2) start_state.
    Proof.
      intros.
      dependent induction bound1 generalizing start_state; try (destruct H; subst; tauto).
      destruct H.
      - subst.
        apply always_reaches_state_after_bounded_steps_weakening with (small_num_steps := bound2); intuition.
      - simpl.
        apply or_intror.
        destruct H.
        eauto.
    Qed.

    Lemma no_cycles_implies_eventually_dropped : forall topology dec_next (policy : static_network_policy) current_flow all_nodes host_ip first_switch first_port,
      valid_topology topology
        -> Injective host_ip
        -> dec_next_node_valid topology policy dec_next
        -> policy current_flow = false
        -> Listing all_nodes
        -> topology (HostNode current_flow.(Src)) (SwitchNode first_switch) = Some first_port
        -> always_reaches_state_after_bounded_steps
            host_ip
            (
              generate_openflow_entries
                (exhaustive_routing_tables_generator dec_next all_nodes)
                host_ip
                topology
            )
            topology
            {| IpSrc := current_flow.(Src).(host_ip); IpDest := current_flow.(Dest).(host_ip) |}
            Dropped
            (length (filter_switches all_nodes))
            (EnRoute first_switch).
    Proof.
      intros.
      assert (forall path here end_switch, is_partial_next_node_path (fun here current_flow hop_target => dec_next here current_flow = Some hop_target) path here end_switch current_flow -> NoDup (here :: path)) by (intros; eapply all_paths_acyclic in H1; eassumption).
      remember (@nil Switch) as path_so_far.
      remember first_switch as current_switch.
      rewrite Heqcurrent_switch in H4.
      remember (length (filter_switches all_nodes)) as num_unvisited_switches.
      assert (is_partial_next_node_path (fun here current_flow hop_target => dec_next here current_flow = Some hop_target) path_so_far first_switch current_switch current_flow) by (subst; reflexivity).
      assert (num_unvisited_switches + length path_so_far = length (filter_switches all_nodes)) by (subst; simpl; omega).
      clear Heqcurrent_switch Heqpath_so_far Heqnum_unvisited_switches.
      dependent induction num_unvisited_switches generalizing current_switch path_so_far.
      - apply H5 in H6.
        enough (H' : length (first_switch :: path_so_far) <= length (filter_switches all_nodes)) by (simpl in *; intuition).
        apply pidgeonhole_principle; try assumption.
        intros.
        apply filter_listing_nodes in H3.
        destruct H3.
        destruct H3.
        apply H10.
      - simpl.
        apply or_intror.
        assert (_ /\ _) by (apply dec_next_creates_valid_unique_state_transitions with (policy := policy) (all_nodes := all_nodes); try eassumption; eauto).
        destruct H8.
        constructor; try eassumption.
        clear H8.
        intros.
        apply H9 in H8.
        clear H9.
        subst.
        destruct_with_eqn (dec_next current_switch current_flow); try solve [ apply always_reaches_state_after_bounded_steps_weakening with (small_num_steps := 0); simpl; intuition ].
        destruct n.
        + apply IHnum_unvisited_switches with (path_so_far := path_so_far ++ [s]).
          * apply is_partial_next_node_path_app with (mid_switch := current_switch); simpl; tauto.
          * rewrite app_length; simpl; omega.
        + assert (H' := H1).
          apply forwards_to_correct_host with (here := current_switch) (current_flow := current_flow) (end_host := h) in H1; try assumption.
          subst.
          apply path_exists_only_for_valid_flows with (current_flow := current_flow) (first_switch := first_switch) (port := first_port) in H'; try assumption.
          enough (policy current_flow = true) by congruence.
          apply H'.
          exists path_so_far.
          clear - H6 Heqo.
          dependent induction path_so_far generalizing first_switch; simpl in *; subst; try assumption.
          constructor; try tauto.
          apply IHpath_so_far; tauto.
    Qed.

    Lemma disallowed_packet_eventually_dropped : forall topology policy dec_next all_nodes host_ip src dest,
      valid_topology topology
        -> Listing all_nodes
        -> Injective host_ip
        -> dec_next_node_valid topology policy dec_next
        -> policy {| Src := src; Dest := dest |} = false
        -> exists num_steps,
          always_reaches_state_after_bounded_steps
            host_ip
            (
              generate_openflow_entries
                (exhaustive_routing_tables_generator dec_next all_nodes)
                host_ip
                topology
            )
            topology
            {| IpSrc := src.(host_ip); IpDest := dest.(host_ip) |}
            Dropped
            num_steps
            NotSentYet.
    Proof.
      intros.
      destruct_with_eqn (find (fun switch => if topology (HostNode src) (SwitchNode switch) then true else false) (filter_switches all_nodes)).
      - exists (S (length (filter_switches all_nodes))).
        simpl.
        apply or_intror.
        constructor.
        + exists (EnRoute s).
          apply find_some in Heqo.
          destruct Heqo.
          destruct_with_eqn (topology (HostNode src) (SwitchNode s)); try discriminate.
          apply EmitPacketFromSrc with (port := p) (src_host := src); try assumption.
          reflexivity.
        + intros.
          inversion_clear H4; try tauto.
          remember {| Src := src; Dest := dest |} as current_flow.
          assert (H' : src = current_flow.(Src)) by (rewrite Heqcurrent_flow; reflexivity); rewrite H' in *; clear H'.
          assert (H' : dest = current_flow.(Dest)) by (rewrite Heqcurrent_flow; reflexivity); rewrite H' in *; clear H'.
          clear Heqcurrent_flow src dest.
          simpl in H5.
          apply H1 in H5.
          subst.
          eapply no_cycles_implies_eventually_dropped; eassumption.
      - apply no_isolated_hosts with (host := src) in H.
        destruct H.
        destruct_with_eqn (topology (HostNode src) (SwitchNode x)); try tauto.
        apply find_none with (x := x) in Heqo; try (rewrite Heqo0 in Heqo; discriminate).
        apply filter_listing_nodes in H0.
        destruct H0.
        destruct H0.
        apply H5.
    Qed.

    Theorem openflow_rules_generator_validity : forall topology policy paths all_nodes host_ip,
      valid_topology topology
        -> all_pairs_paths_valid topology policy paths
        -> Listing all_nodes
        -> Injective host_ip
        -> valid_openflow_entries
          topology
          policy
          host_ip
          (
            generate_openflow_entries
            (
              exhaustive_routing_tables_generator
              (all_pairs_paths_dec_next_node_generator paths topology policy)
              all_nodes
            )
            host_ip
            topology
          ).
    Proof.
      intros.
      set (dec_next := all_pairs_paths_dec_next_node_generator paths topology policy).
      set (tables := exhaustive_routing_tables_generator dec_next all_nodes).
      set (openflow_entries := generate_openflow_entries tables host_ip topology).
      assert (dec_next_node_valid topology policy dec_next) by (apply all_pairs_paths_dec_generator_valid; assumption).
      assert (routing_tables_valid tables dec_next) by (apply exhaustive_routing_tables_generator_valid; assumption).
      constructor; intros.
      - assert (H' := H).
        apply no_isolated_hosts with (host := src_node) in H.
        destruct H.
        destruct_with_eqn (topology (HostNode src_node) (SwitchNode x)); try tauto.
        unfold dec_next_node_valid in H3.
        assert (dec_next_node_valid topology policy dec_next) by (apply all_pairs_paths_dec_generator_valid; assumption).
        assert (H'' := H7).
        apply path_exists_only_for_valid_flows with (current_flow := {| Src := src_node; Dest := dest_node |}) (first_switch := x) (port := p) in H7; try (simpl; assumption).
        destruct_with_eqn (policy {| Src := src_node; Dest := dest_node |}).
        + assert (exists path, _) by (apply H7; reflexivity).
          clear H7.
          destruct H8.
          exists (1 + (length (filter_switches all_nodes) + 1) + 1).
          simpl.
          apply or_intror.
          constructor.
          * exists (EnRoute x).
            apply EmitPacketFromSrc with (port := p) (src_host := src_node); assumption.
          * intros.
            apply always_reaches_state_after_bounded_steps_combination with (mid_state := ReceivedAtHost dest_node); try (destruct packet; simpl in H5, H6; subst; apply reaches_arrived_state_from_destination_in_one_step).
            inversion_clear H8.
            --rewrite <- H5 in H9.
              apply H2 in H9.
              subst.
              clear x Heqo H7.
              assert (H''' := H'').
              apply path_exists_only_for_valid_flows with (current_flow := {| Src := src_node; Dest := dest_node |}) (first_switch := first_switch) (port := port) in H''; try assumption.
              rewrite Heqb in H''.
              assert (exists _, _) by (apply H''; reflexivity); clear H''.
              destruct H7.
              clear H H10.
              destruct packet; simpl in H5, H6; subst.
              apply always_reaches_state_after_bounded_steps_weakening with (small_num_steps := length x + 1).
              ++dependent induction x generalizing first_switch.
                **simpl in H7.
                  apply always_reaches_state_after_bounded_steps_weakening with (small_num_steps := 1); try omega.
                  simpl.
                  apply or_intror.
                  assert (_ /\ _) by (apply dec_next_creates_valid_unique_state_transitions with (policy := policy) (all_nodes := all_nodes) (current_flow := {| Src := src_node; Dest := dest_node |}) (here := first_switch); try eassumption; eauto).
                  simpl in H.
                  constructor; try tauto.
                  destruct H.
                  intros.
                  specialize (H5 new_state0).
                  rewrite H7 in H5.
                  apply or_introl, eq_sym, H5.
                  assumption.
                **destruct H7.
                  simpl.
                  apply or_intror.
                  assert (_ /\ _) by (apply dec_next_creates_valid_unique_state_transitions with (policy := policy) (all_nodes := all_nodes) (current_flow := {| Src := src_node; Dest := dest_node |}) (here := first_switch); try eassumption; eauto).
                  simpl in H6.
                  constructor; try tauto.
                  destruct H6.
                  intros.
                  specialize (H7 new_state0).
                  rewrite H in H7.
                  assert (new_state0 = EnRoute a) by (apply H7; assumption).
                  subst.
                  apply IHx.
                  assumption.
              ++enough (length x <= length (filter_switches all_nodes)) by omega.
                destruct x; try (simpl; omega).
                apply all_paths_acyclic with (path := s :: x) (here := first_switch) (end_switch := last (s :: x) first_switch) (current_flow := {| Src := src_node; Dest := dest_node |}) in H'''; try assumption.
                **inversion_clear H'''.
                  apply pidgeonhole_principle; try assumption.
                  intros.
                  apply filter_listing_nodes; assumption.
                **apply next_node_path_has_partial.
                  assumption.
        + destruct packet.
          simpl in H5, H6.
          subst.
          apply disallowed_packet_eventually_dropped with (policy := policy); try assumption.
      - unfold openflow_entries, generate_openflow_entries.
        set (switch_tables := tables switch).
        dependent induction switch_tables; simpl; try tauto.
        constructor; try assumption.
        destruct_with_eqn (topology (SwitchNode switch) a.(snd)); try tauto.
        destruct (is_switch a.(snd)); eexists; eassumption.
    Qed.

    Definition openflow_rules_generator
      (topology : {t : network_topology | valid_topology t})
      (policy : static_network_policy)
      (paths : {pairs_paths : all_pairs_paths | all_pairs_paths_valid topology.(proj1_sig) policy pairs_paths})
      (all_nodes : {enumeration : list Node | Listing enumeration})
      (host_ip : {ips : host_ip_map | Injective ips})
    : {entries : switch_openflow_entry_map | valid_openflow_entries topology.(proj1_sig) policy host_ip.(proj1_sig) entries}.
    Proof.
      econstructor.
      apply openflow_rules_generator_validity with (paths := paths.(proj1_sig)) (all_nodes := all_nodes.(proj1_sig)); exact _.(proj2_sig).
    Defined.

    Theorem dynamic_controller_generator_validity : forall (policy_state : Set) topology (policy : @dynamic_network_policy policy_state) paths all_nodes host_ip,
      valid_topology topology
        -> dynamic_policy_valid topology policy paths
        -> Listing all_nodes
        -> Injective host_ip
        -> controller_implements_policy topology policy host_ip {|
          controller_system := policy.(policy_system);
          controller_state_decider := fun state =>
          (
            generate_openflow_entries
            (
              exhaustive_routing_tables_generator
              (all_pairs_paths_dec_next_node_generator paths topology (policy.(policy_state_decider) state))
              all_nodes
            )
            host_ip
            topology
          )
        |}.
    Proof.
      unfold controller_implements_policy, dynamic_policy_valid, invariant.
      intros.
      destruct new_state.
      simpl in H3.
      assert (p = p0).
      - destruct policy.(policy_system).
        clear - H3.
        dependent induction H3; try reflexivity.
        simpl in H3, IHtrc.
        destruct (policy_state_decider policy Initial0 sent_flow); eapply IHtrc; reflexivity.
      - subst.
        apply openflow_rules_generator_validity; try assumption.
        apply H0.
        unfold filter_transition_system.
        simpl.
        destruct policy.(policy_system).
        clear - H3.
        simpl.
        simpl in H3.
        dependent induction H3; try apply TrcRefl.
        destruct_with_eqn (policy_state_decider policy Initial0 sent_flow).
        + eapply TrcFront with (sent_flow0 := sent_flow); try reflexivity.
          apply IHtrc; simpl; try rewrite Heqb; reflexivity.
        + apply IHtrc; simpl; try rewrite Heqb; reflexivity.
    Qed.

    Definition dynamic_controller_generator
      {policy_state : Set}
      (topology : {t : network_topology | valid_topology t})
      (policy : @dynamic_network_policy policy_state)
      (paths: {pairs_paths : all_pairs_paths | dynamic_policy_valid topology.(proj1_sig) policy pairs_paths})
      (all_nodes : {enumeration : list Node | Listing enumeration})
      (host_ip : {ips : host_ip_map | Injective ips})
    : {controller : @network_controller policy_state | controller_implements_policy topology.(proj1_sig) policy host_ip.(proj1_sig) controller}.
    Proof.
      econstructor.
      apply dynamic_controller_generator_validity with (paths := paths.(proj1_sig)) (all_nodes := all_nodes.(proj1_sig)); exact _.(proj2_sig).
    Defined.
  End OpenFlow.
End Node.

Ltac prove_valid_topology topology :=
  let Switch := match goal with
  | [ |- {t : @network_topology ?Switch _ | valid_topology t} ] => Switch
  | _ => fail 1 "Unexpected goal in valid topology proof"
  end in
  let Host := match goal with
  | [ |- {t : @network_topology _ ?Host | valid_topology t} ] => Host
  end in
  apply exist with (x := topology);
  constructor;
  intros;
  repeat match goal with
  | [ x : @Node Switch Host |- _ ] => destruct x
  | [ x : Switch |- _ ] => destruct x
  | [ x : Host |- _ ] => destruct x
  end;
  simpl;
  try reflexivity;
  match goal with
  | [ |- exists _, _ ] =>
    let adjacent_switch := fresh "adjacent_switch" in
      evar (adjacent_switch : Switch);
      exists adjacent_switch;
      destruct_with_eqn adjacent_switch; repeat match goal with
      | [ H : adjacent_switch = ?val |- True ] => instantiate (adjacent_switch := val); apply I
      | _ => idtac
      end; discriminate
  | _ => firstorder discriminate
  end.

Ltac prove_injective_ips host_ip :=
  let Host := match goal with
  | [ |- {ips : @host_ip_map ?Host | Injective ips} ] => Host
  | _ => fail 1 "Unexpected goal in injective IPs proof"
  end in
  apply exist with (x := host_ip);
  unfold Injective;
  intros;
  repeat match goal with
  | [ x : Host |- _ ] => destruct x
  end;
  try reflexivity;
  try discriminate.

Ltac enumerate_nodes :=
  let Switch := match goal with
  | [ |- {l : list (@Node ?Switch ?Host) | Listing l} ] => Switch
  | _ => fail 1 "Unexpected goal in finite set enumeration"
  end in
  let Host := match goal with
  | [ |- {l : list (@Node ?Switch ?Host) | Listing l} ] => Host
  end in
  econstructor;
  unfold Listing, Full;
  constructor;
  [
    idtac |
    intros;
    match goal with
    | [ node : @Node Switch Host |- _ ] => destruct node
    end;
    match goal with
    | [ switch : Switch |- _ ] => destruct switch
    | [ host : Host |- _ ] => destruct host
    end;
    unshelve (
      let cdr := fresh "cdr" in
        evar (cdr : list (@Node Switch Host));
        let cdr' := (eval unfold cdr in cdr) in
          clear cdr;
          match goal with
          | [ |- In ?n _ ] => instantiate (1 := n :: cdr')
          end;
          simpl;
          tauto
    );
    exact []
  ];
  repeat constructor;
  firstorder discriminate.

Fixpoint map_with_index' {A} {B} (f : A -> nat -> B) (l : list A) (start_index : nat) :=
  match l with
  | [] => []
  | car :: cdr => (f car start_index) :: map_with_index' f cdr (S start_index)
  end.

Definition map_with_index {A} {B} (f : A -> nat -> B) (l : list A) := map_with_index' f l 0.

Definition set_value_at {A} (lst : list (list A)) (i j : nat) (val : A) :=
  map_with_index (fun row row_index =>
    if row_index =? i
    then map_with_index (fun entry col_index => if col_index =? j then val else entry) row
    else row
  ) lst.

Definition get_value_at {A} (lst : list (list A)) (i j : nat) :=
  match nth_error lst i with
  | Some row =>
    match nth_error row j with
    | Some entry => Some entry
    | None => None
    end
  | None => None
  end.

Definition distance_can_be_shortened (dists : list (list (option nat))) (i j k : nat) :=
  match get_value_at dists i j, get_value_at dists i k, get_value_at dists k j with
  | Some None, Some (Some i_k), Some (Some k_j) => Some (i_k + k_j)
  | Some (Some i_j), Some (Some i_k), Some (Some k_j) => if i_k + k_j <? i_j then Some (i_k + k_j) else None
  | _, _, _ => None
  end.

Fixpoint find_index {Node} (Node_eq_dec : forall (n1 n2 : Node), {n1 = n2} + {n1 <> n2}) nodes node :=
  match nodes with
  | [] => None
  | car :: cdr =>
    if Node_eq_dec car node
    then Some 0
    else match find_index Node_eq_dec cdr node with
    | Some cdr_index => Some (S cdr_index)
    | None => None
    end
  end.

Fixpoint next_matrix_to_paths {Switch} {Host} (Node_eq_dec : forall (n1 n2 : @Node Switch Host), {n1 = n2} + {n1 <> n2}) all_nodes max_length (next_matrix : list (list (option (@Node Switch Host)))) switchA hostB :=
  match max_length with
  | 0 => None
  | S max_length' =>
    let indexA := find_index Node_eq_dec all_nodes (SwitchNode switchA) in
    let indexB := find_index Node_eq_dec all_nodes (HostNode hostB) in
    match indexA, indexB with
    | Some iA, Some iB =>
      match nth_error next_matrix iA with
      | Some nodeA_row =>
        match nth_error nodeA_row iB with
        | Some (Some (SwitchNode hop)) =>
          match next_matrix_to_paths Node_eq_dec all_nodes max_length' next_matrix hop hostB with
          | Some cdr_path => Some (hop :: cdr_path)
          | None => None
          end
        | Some (Some (HostNode host)) =>
          if Node_eq_dec (HostNode host) (HostNode hostB)
          then Some []
          else None
        | _ => None
        end
      | None => None
      end
    | _, _ => None
    end
  end.

(* Implements the Floyd-Warshall algorithm *)
Ltac generate_all_pairs_paths Node Node_eq_dec Switch_eq_dec Host_eq_dec topology all_nodes costs :=
  let nodes := (eval unfold all_nodes in all_nodes.(proj1_sig)) in
  let dists := fresh "dists" in
  let nexts := fresh "nexts" in
  set (dists := map (fun n1 =>
    map (fun n2 =>
      if Node_eq_dec n1 n2
      then Some 0
      else match topology n1 n2 with
      | Some port => Some (costs n1 port)
      | None => None
      end
    ) nodes
  ) nodes);
  set (nexts := map (fun n1 =>
    map (fun n2 =>
      if Node_eq_dec n1 n2
      then Some n1
      else match topology n1 n2 with
      | Some _ => Some n2
      | None => None
      end
    ) nodes
  ) nodes);
  let num_nodes := eval compute in (length nodes) in
  let k := fresh "k" in
  set (k := 0);
  repeat (
    match (eval compute in k) with
    | num_nodes => fail 1
    | _ => idtac
    end;

    let i := fresh "i" in
    set (i := 0);
    repeat (
      match (eval compute in i) with
      | num_nodes => fail 1
      | _ => idtac
      end;

      let j := fresh "j" in
      set (j := 0);
      repeat (
        match (eval compute in j) with
        | num_nodes => fail 1
        | _ => idtac
        end;

        match eval compute in (distance_can_be_shortened dists i j k) with
        | Some ?short_distance =>
          let dists' := eval compute in (set_value_at dists i j (Some short_distance)) in (
            clear dists;
            set (dists := dists')
          );
          let nexts' := eval compute in (
            set_value_at nexts i j (
              match get_value_at nexts i k with
              | Some v => v
              | None => None
              end
            )
          ) in (
            clear nexts;
            set (nexts := nexts')
          )
        | None => idtac
        end;

        let j' := eval compute in j in
          clear j;
          set (j := S j')
      );
      clear j;

      let i' := eval compute in i in
        clear i;
        set (i := S i')
    );
    clear i;

    let k' := eval compute in k in
      clear k;
      set (k := S k')
  );
  clear k;
  let all_switches := (constr:(filter_switches nodes)) in
  let all_hosts := (constr:(filter_hosts nodes)) in
  let paths_grid := eval compute in (map (fun switchA =>
    map (fun hostB =>
      next_matrix_to_paths Node_eq_dec nodes num_nodes nexts switchA hostB
    ) all_hosts
  ) all_switches) in
  exact (fun switch host =>
    match find_index Switch_eq_dec all_switches switch, find_index Host_eq_dec all_hosts host with
    | Some iA, Some iB =>
      match nth_error paths_grid iA with
      | Some switch_row =>
        match nth_error switch_row iB with
        | Some path => path
        | None => None
        end
      | None => None
      end
    | _, _ => None
    end
  ).

Ltac prove_dynamic_policy_valid Switch Host topology policy costs Switch_eq_dec Host_eq_dec all_nodes paths policy_invariant :=
  let invariant_implies_path_exists := fresh "invariant_implies_path_exists" in
  let invariant_initial := fresh "invariant_initial" in
  let invariant_step := fresh "invariant_step" in
  assert (invariant_implies_path_exists : forall st current_flow first_switch,
    policy_invariant st
      -> policy_state_decider policy st current_flow = true
      -> (if topology (HostNode current_flow.(Src)) (SwitchNode first_switch) then True else False)
      -> paths first_switch current_flow.(Dest) = None
      -> False
  );
  [
    idtac |
    assert (invariant_initial : policy_invariant policy.(policy_system).(Initial));
    [
      clear |
      assert (invariant_step : forall st current_flow,
        policy_invariant st
          -> policy.(policy_state_decider) st current_flow = true
          -> policy_invariant (policy.(policy_system).(Step) st current_flow)
      ); [clear | idtac]
    ]
  ];
  [ idtac | idtac | idtac |
    apply exist with (x := paths);
    apply invariant_weakening with (strong_condition := policy_invariant);
    match goal with
    | [ |- invariant _ policy_invariant ] =>
      unfold invariant;
      intros;
      unfold filter_transition_system in *;
      let start := fresh "start" in
      let Heqstart := fresh "Heqstart" in
      remember policy.(policy_system).(Initial) as start eqn:Heqstart;
      clear Heqstart;
      match goal with
      | [ H : trc _ _ _ |- _ ] =>
        simpl in H;
        dependent induction H;
        [ apply invariant_initial | idtac ];
        subst;
        match goal with
        | [ H : ?inv (if ?cond then _ else _) -> ?inv ?dest |- ?inv ?dest ] =>
          apply H;
          destruct_with_eqn (cond); try assumption;
          apply invariant_step; assumption
        end
      end
    | [ |- forall state, policy_invariant state -> all_pairs_paths_valid _ _ _ ] =>
      intros;
      constructor;
      intros;
      match goal with
      | [ |- match paths ?src ?dest with | Some _ => _ | None => True end ] =>
        destruct src, dest;
        unfold paths;
        simpl;
        tauto
      | [ |- match paths ?first_switch ?current_flow.(Dest) with | Some _ => True | None => False end ] =>
        destruct_with_eqn (paths first_switch current_flow.(Dest));
        [ tauto | idtac ];
        destruct current_flow;
        eapply invariant_implies_path_exists;
        try eassumption;
        match goal with
        | [ H : ?cond = Some _ |- if ?cond then True else False ] => rewrite H; tauto
        end
      | [ |- exists x, generates_decreasing_costs topology paths x ] =>
        exists costs;
        constructor;
        unfold only_positive_costs;
        intros;
        repeat match goal with
        | [ n : @Node Switch Host |- _ ] => destruct n
        | [ s : Switch |- _ ] => destruct s
        | [ h : Host |- _ ] => destruct h
        end; unfold costs, topology, paths;
        simpl;
        solve [ intuition ]
      end
    | _ => idtac
    end
  ].

Section NetworkExample.
  Local Inductive ExampleSwitch :=
  | sA
  | sB
  | sC
  | sD
  | sE
  | sF
  .

  Local Inductive ExampleHost :=
  | hA
  | hB
  | hC
  | hD
  | hE
  | hF
  .

  Definition all_nodes : {l : list (@Node ExampleSwitch ExampleHost) | Listing l} := ltac:(enumerate_nodes).

  Definition ExampleSwitch_eq_dec : forall x y : ExampleSwitch, {x = y} + {x <> y} := ltac:(decide equality).
  Definition ExampleHost_eq_dec : forall x y : ExampleHost, {x = y} + {x <> y} := ltac:(decide equality).
  Definition ExampleNode_eq_dec : forall x y : @Node ExampleSwitch ExampleHost, {x = y} + {x <> y} := @Node_eq_dec ExampleSwitch ExampleHost ExampleSwitch_eq_dec ExampleHost_eq_dec.
  Definition portNo := natToWord 16.

  (*
    example_topology:

       hB --- sB ----> sE      hE
             / | \   /          |
    hA --- sA  |  sD ---- sF ---|
            \  | /   \      ↖______- hF
              sC - hC \__- hD
  *)
  Local Definition example_topology n1 n2 :=
    match n1, n2 with
    (* Arbitrarily, the ports are numbered in increasing
       order at each node. *)
    | HostNode hA, SwitchNode sA => Some (portNo 1)
    | SwitchNode sA, HostNode hA => Some (portNo 1)
    | SwitchNode sA, SwitchNode sB => Some (portNo 2)
    | SwitchNode sA, SwitchNode sC => Some (portNo 3)
    | HostNode hB, SwitchNode sB => Some (portNo 1)
    | SwitchNode sB, SwitchNode sA => Some (portNo 1)
    | SwitchNode sB, HostNode hB => Some (portNo 2)
    | SwitchNode sB, SwitchNode sC => Some (portNo 3)
    | SwitchNode sB, SwitchNode sD => Some (portNo 4)
    | SwitchNode sB, SwitchNode sE => Some (portNo 5)
    | HostNode hC, SwitchNode sC => Some (portNo 1)
    | SwitchNode sC, SwitchNode sA => Some (portNo 1)
    | SwitchNode sC, SwitchNode sB => Some (portNo 2)
    | SwitchNode sC, HostNode hC => Some (portNo 3)
    | SwitchNode sC, SwitchNode sD => Some (portNo 4)
    | HostNode hD, SwitchNode sD => Some (portNo 1)
    | SwitchNode sD, SwitchNode sB => Some (portNo 1)
    | SwitchNode sD, SwitchNode sC => Some (portNo 2)
    | SwitchNode sD, HostNode hD => Some (portNo 3)
    | SwitchNode sD, SwitchNode sE => Some (portNo 4)
    | SwitchNode sD, SwitchNode sF => Some (portNo 5)
    | HostNode hE, SwitchNode sF => Some (portNo 1)
    | SwitchNode sE, SwitchNode sD => Some (portNo 1)
    | HostNode hF, SwitchNode sF => Some (portNo 1)
    | SwitchNode sF, SwitchNode sD => Some (portNo 1)
    | SwitchNode sF, HostNode hE => Some (portNo 2)
    | _, _ => None
    end.

  (* Giving all edges a cost of 1 would not satisfy the decreasing-costs
  constraint, because when routing F to E, node B would choose
  a path of [C; A; B; E] which is not shorter than the original expected
  path from F of [D; C; B; E]. However, if the (C, B) edge
  has a large cost, then the total cost of [C; A; B; E] is less
  than the cost of [D; C; B; E]. *)
  Definition example_costs (n1 : @Node ExampleSwitch ExampleHost) port :=
    match n1 with
    | SwitchNode sC => if weqb port (natToWord 16 2) then 5 else 1
    | _ => 1
    end.

  Local Definition example_all_pairs_paths : @all_pairs_paths ExampleSwitch ExampleHost := ltac:(generate_all_pairs_paths (@Node ExampleSwitch ExampleHost) ExampleNode_eq_dec ExampleSwitch_eq_dec ExampleHost_eq_dec example_topology all_nodes example_costs).

  Definition ExampleHost_eqb x y := if ExampleHost_eq_dec x y then true else false.

  Fixpoint in_pair_list pair_list current_flow :=
    match pair_list with
    | [] => false
    | (src, dest) :: cdr => (ExampleHost_eqb src current_flow.(Src) && ExampleHost_eqb dest current_flow.(Dest)) || in_pair_list cdr current_flow
    end.

  (*
    Initial state: A can send to anywhere that it can reach
    After each successful packet from x to y, policy updates so y can also send to x, provided that y can reach x
  *)
  Definition example_dynamic_policy : @dynamic_network_policy ExampleHost (list (ExampleHost * ExampleHost)) := {|
    policy_system := {|
      Initial := [(hA, hB); (hA, hC); (hA, hD); (hA, hE)];
      Step := fun current_state last_flow =>
        if ExampleHost_eq_dec hF last_flow.(Src)
        then current_state
        else (last_flow.(Dest), last_flow.(Src)) :: current_state
    |};
    policy_state_decider := in_pair_list
  |}.

  Definition verified_example_paths : {paths : @all_pairs_paths ExampleSwitch ExampleHost | dynamic_policy_valid example_topology example_dynamic_policy paths}.
  Proof.
    prove_dynamic_policy_valid ExampleSwitch ExampleHost example_topology example_dynamic_policy example_costs ExampleSwitch_eq_dec ExampleHost_eq_dec all_nodes example_all_pairs_paths (fix contains_valid_entries (state : list (ExampleHost * ExampleHost)) := match state with
    | [] => True
    | (src, dest) :: cdr => dest <> hF /\ contains_valid_entries cdr
    end); intros.
    - intros; unfold example_dynamic_policy in *; simpl in *; destruct current_flow; dependent induction st; intros; try discriminate H0; simpl in *; intros.
      repeat match goal with
      | [ H : let (_, _) := ?a in _ |- _ ] => destruct a
      | [ H : _ || _ = true |- _ ] => rewrite orb_true_iff in H
      | [ H : _ && _ = true |- _ ] => rewrite andb_true_iff in H
      | [ H : _ /\ _ |- _ ] => destruct H
      | [ H : _ \/ _ |- _ ] => destruct H
      | [ H : ExampleHost_eqb ?a ?b = true |- _ ] => assert (a = b) by (destruct a, b; simpl in H; try reflexivity; discriminate H); clear H; subst
      end; apply IHst with (Src0 := Src0) (Dest0 := Dest0) (first_switch := first_switch); try assumption; repeat match goal with
      | [ H : example_all_pairs_paths ?s ?h = _ |- _ ] => destruct s, h; unfold example_all_pairs_paths in H; simpl in H; try discriminate H
      end; destruct Src0; try tauto.
    - firstorder discriminate.
    - intros; repeat match goal with
    | [ f : flow |- _ ] => destruct f
    | [ x : @Node ExampleSwitch ExampleHost |- _ ] => destruct x; simpl
    | [ x : ExampleSwitch |- _ ] => destruct x; simpl
    | [ x : ExampleHost |- _ ] => destruct x; simpl
    | [ |- _ /\ _ ] => constructor
    end; congruence.
  Defined.

  Definition example_host_ip_nat node :=
    match node with
    | hA => (10, 0, 0, 1)
    | hB => (10, 0, 0, 2)
    | hC => (10, 0, 0, 3)
    | hD => (10, 0, 0, 4)
    | hE => (10, 0, 0, 5)
    | hF => (10, 0, 0, 6)
    end.

  Definition host_ip node :=
    match example_host_ip_nat node with
    | (n1, n2, n3, n4) => (natToWord 8 n1, natToWord 8 n2, natToWord 8 n3, natToWord 8 n4)
    end.

  Definition generated_dynamic_controller := @dynamic_controller_generator
    ExampleSwitch
    ExampleHost
    ExampleSwitch_eq_dec
    ExampleHost_eq_dec
    (list (ExampleHost * ExampleHost))
    ltac:(prove_valid_topology example_topology)
    example_dynamic_policy
    verified_example_paths
    all_nodes
    ltac:(prove_injective_ips host_ip).
End NetworkExample.

Require Extraction.
Extraction Language OCaml.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive list => "list" [ "[]" "( :: )" ].
Extract Inductive prod => "( * )" [ "(, )" ].
Extraction "src/generated_controller.ml" generated_dynamic_controller.
