(* ========================================================================= *)
(*  DebianVote.v                                                             *)
(*                                                                           *)
(*  A formalisation of the vote counting procedure of the Debian             *)
(*  Constitution, Appendix A.5 ("Vote Counting"):                            *)
(*                                                                           *)
(*   1. Each voter's ballot ranks the options; options may be ranked         *)
(*      equally; unranked options rank equal to each other and below all     *)
(*      ranked options.                                                      *)
(*   2. Quorum: with quorum R, a non-default option A is dropped unless at   *)
(*      least R voters rank A above the default option D: V(A,D) >= R.       *)
(*   3. Majority: a non-default option A with majority ratio N is dropped    *)
(*      unless V(A,D) >= N * V(D,A) and V(A,D) > V(D,A).                     *)
(*   4. A defeats B if V(A,B) > V(B,A)  (among undropped options).           *)
(*   5. A transitively defeats C if A defeats C, or A defeats some B that    *)
(*      transitively defeats C.                                              *)
(*   6. The Schwartz set: options A such that for every option B, either A   *)
(*      transitively defeats B or B does not transitively defeat A.          *)
(*   7. If there are defeats between options in the Schwartz set, drop the   *)
(*      weakest such defeats and return to step 5. (A,X) is weaker than      *)
(*      (B,Y) if V(A,X) < V(B,Y), or V(A,X) = V(B,Y) and V(X,A) > V(Y,B).    *)
(*   8. Otherwise the options in the Schwartz set are the winners.           *)
(*                                                                           *)
(*  The specification `cssd_spec` is a direct transcription of steps 5-8    *)
(*  as an inductive relation; `cssd` is a boolean implementation; the main   *)
(*  theorems are that the implementation satisfies the specification, that  *)
(*  the specification is functional, that there is always at least one       *)
(*  winner, that the default option is never dropped, and that a Condorcet   *)
(*  winner among the undropped options is the unique winner.                 *)
(* ========================================================================= *)

From Stdlib Require Import List Arith Lia Bool PeanoNat.
Import ListNotations.

Section Debian.

  (* ----------------------------------------------------------------------- *)
  (*  Options                                                                *)
  (* ----------------------------------------------------------------------- *)

  Variable cand : Type.
  Variable cand_all : list cand.
  Hypothesis cand_fin : forall c, In c cand_all.
  Hypothesis cand_nodup : NoDup cand_all.
  Hypothesis dec_cand : forall x y : cand, {x = y} + {x <> y}.
  Variable default : cand.

  (* the pairwise matrix of the vote: Vm x y voters rank x above y *)
  Variable Vm : cand -> cand -> nat.

  Definition ceq (x y : cand) : bool := if dec_cand x y then true else false.

  Lemma ceq_true x y : ceq x y = true <-> x = y.
  Proof. unfold ceq. destruct (dec_cand x y); split; intros; congruence. Qed.

  Lemma ceq_refl x : ceq x x = true.
  Proof. apply ceq_true. reflexivity. Qed.

  Definition inb (x : cand) (l : list cand) : bool := existsb (ceq x) l.

  Lemma inb_true x l : inb x l = true <-> In x l.
  Proof.
    unfold inb. rewrite existsb_exists. split.
    - intros [y [Hy He]]. apply ceq_true in He. subst. auto.
    - intros H. exists x. split; auto. apply ceq_refl.
  Qed.

  (* ----------------------------------------------------------------------- *)
  (*  Ballots and the pairwise matrix V (A.5.1, A.5.3.1)                    *)
  (* ----------------------------------------------------------------------- *)

  (* A ballot gives each option a rank; 0 means "not ranked"; 1 is the
     highest preference. Equal ranks are allowed. A.5.1: "Each voter's ballot
     ranks the options being voted on. Not all options need be ranked." *)
  Definition ballot := cand -> nat.

  (* x is ranked above y on ballot b. A.5.1: "Ranked options are considered
     preferred to all unranked options. Voters may rank options equally.
     Unranked options are considered to be ranked equally with one another." *)
  Definition above (b : ballot) (x y : cand) : bool :=
    match b x, b y with
    | 0, _ => false                   (* unranked is never above anything *)
    | S _, 0 => true                  (* ranked is above unranked *)
    | S rx, S ry => rx <? ry          (* smaller rank number = higher preference *)
    end.

  (* V(x,y): the number of voters who rank x above y (one ballot per voter).
     A.5.3.1: "Given two options A and B, V(A,B) is the number of voters who
     prefer option A over option B." *)
  Definition V (bs : list ballot) (x y : cand) : nat :=
    length (filter (fun b => above b x y) bs).

  Lemma above_irrefl b x : above b x x = false.
  Proof. unfold above. destruct (b x); auto. apply Nat.ltb_irrefl. Qed.

  (* at most one of x above y, y above x holds on a ballot *)
  Lemma above_antisym b x y : above b x y = true -> above b y x = false.
  Proof.
    unfold above. destruct (b x) as [| rx], (b y) as [| ry]; try discriminate; auto.
    intros H. apply Nat.ltb_lt in H. apply Nat.ltb_ge. lia.
  Qed.

  (* ----------------------------------------------------------------------- *)
  (*  Defeats (A.5.4)                                                        *)
  (* ----------------------------------------------------------------------- *)

  Definition defeat := (cand * cand)%type.

  Definition deq (p q : defeat) : bool := ceq (fst p) (fst q) && ceq (snd p) (snd q).

  Lemma deq_true p q : deq p q = true <-> p = q.
  Proof.
    unfold deq. destruct p as [a b], q as [c d]. simpl.
    rewrite andb_true_iff, !ceq_true. split.
    - intros [-> ->]. reflexivity.
    - intros H. inversion H. auto.
  Qed.

  (* ----------------------------------------------------------------------- *)
  (*  Transitive defeat (A.5.5), relative to a current list of defeats       *)
  (* ----------------------------------------------------------------------- *)

  (* A.5.5.1, as stated: "An option A transitively defeats an option C if A
     defeats C or if there is some other option B where A defeats B AND B
     transitively defeats C." B need not be required to differ from A and C:
     no option defeats itself, and if B = C then A defeats C directly. *)
  Inductive TDef (defs : list defeat) : cand -> cand -> Prop :=
  | tdef_direct a c : In (a, c) defs -> TDef defs a c
  | tdef_via a b c : In (a, b) defs -> TDef defs b c -> TDef defs a c.

  Lemma TDef_trans defs a b c : TDef defs a b -> TDef defs b c -> TDef defs a c.
  Proof.
    intros H1 H2. induction H1.
    - apply tdef_via with c0; auto.
    - apply tdef_via with b; auto.
  Qed.

  (* the right-recursive form, convenient for closure arguments *)
  Lemma TDef_snoc defs a b c : TDef defs a b -> In (b, c) defs -> TDef defs a c.
  Proof. intros H Hc. apply TDef_trans with b; auto. constructor; auto. Qed.

  (* Computation: forward reachability by iterated expansion. One expansion
     step adds every option defeated by an option already reached. *)
  Definition successors (defs : list defeat) (a : cand) : list cand :=
    map snd (filter (fun p => ceq (fst p) a) defs).

  Definition expand (defs : list defeat) (S : list cand) : list cand :=
    S ++ filter (fun c => negb (inb c S))
                (flat_map (successors defs) S).

  Fixpoint iterate (n : nat) (f : list cand -> list cand) (S : list cand) : list cand :=
    match n with
    | O => S
    | S n' => iterate n' f (f S)
    end.

  (* everything reachable from a in at most (length cand_all) steps *)
  Definition reach (defs : list defeat) (a : cand) : list cand :=
    iterate (length cand_all) (expand defs) (successors defs a).

  Definition tdef (defs : list defeat) (a c : cand) : bool := inb c (reach defs a).

  (* -- soundness: everything computed is a transitive defeat -------------- *)

  Lemma successors_in defs a c : In c (successors defs a) <-> In (a, c) defs.
  Proof.
    unfold successors. rewrite in_map_iff. split.
    - intros [[a' c'] [E Hin]]. simpl in E. subst. apply filter_In in Hin.
      destruct Hin as [Hin He]. simpl in He. apply ceq_true in He. subst. auto.
    - intros H. exists (a, c). split; auto. apply filter_In. split; auto. simpl. apply ceq_refl.
  Qed.

  Lemma expand_sound defs a S :
    (forall c, In c S -> TDef defs a c) ->
    forall c, In c (expand defs S) -> TDef defs a c.
  Proof.
    intros HS c Hc. unfold expand in Hc. apply in_app_or in Hc. destruct Hc as [Hc | Hc]; auto.
    apply filter_In in Hc. destruct Hc as [Hc _]. apply in_flat_map in Hc.
    destruct Hc as [b [Hb Hbc]]. apply successors_in in Hbc.
    apply TDef_snoc with b; auto.
  Qed.

  Lemma iterate_sound defs a n S :
    (forall c, In c S -> TDef defs a c) ->
    forall c, In c (iterate n (expand defs) S) -> TDef defs a c.
  Proof.
    revert S. induction n as [| n IH]; intros S HS c Hc; simpl in Hc; auto.
    apply (IH (expand defs S)); auto. apply expand_sound; auto.
  Qed.

  Lemma tdef_sound defs a c : tdef defs a c = true -> TDef defs a c.
  Proof.
    unfold tdef, reach. intros H. apply inb_true in H.
    apply (iterate_sound defs a (length cand_all) (successors defs a)); auto.
    intros x Hx. apply successors_in in Hx. constructor; auto.
  Qed.

  (* -- completeness: iteration reaches a closed set ----------------------- *)

  Lemma expand_grows defs S c : In c S -> In c (expand defs S).
  Proof. intros H. unfold expand. apply in_or_app. auto. Qed.

  Lemma iterate_grows defs n S c : In c S -> In c (iterate n (expand defs) S).
  Proof.
    revert S. induction n as [| n IH]; intros S H; simpl; auto.
    apply IH. apply expand_grows. auto.
  Qed.

  (* a set is closed if it contains the successors of its members *)
  Definition closed (defs : list defeat) (S : list cand) : Prop :=
    forall b c, In b S -> In (b, c) defs -> In c S.

  Lemma expand_closed_or_grows defs S :
    closed defs S \/ exists c, In c (expand defs S) /\ ~ In c S.
  Proof.
    destruct (filter (fun c => negb (inb c S)) (flat_map (successors defs) S)) as [| c l] eqn:Hf.
    - left. intros b c Hb Hbc.
      destruct (inb c S) eqn:Hc; [apply inb_true; auto | ].
      assert (In c (filter (fun c => negb (inb c S)) (flat_map (successors defs) S))).
      { apply filter_In. split; [ | rewrite Hc; auto].
        apply in_flat_map. exists b. split; auto. apply successors_in. auto. }
      rewrite Hf in H. contradiction.
    - right. exists c. split.
      + unfold expand. apply in_or_app. right. rewrite Hf. left. auto.
      + assert (In c (filter (fun c => negb (inb c S)) (flat_map (successors defs) S)))
          by (rewrite Hf; left; auto).
        apply filter_In in H. destruct H as [_ H]. apply negb_true_iff in H.
        intros Hc. apply inb_true in Hc. congruence.
  Qed.

  (* We measure a set by the number of members of cand_all it contains. *)
  Definition size (S : list cand) : nat := length (filter (fun c => inb c S) cand_all).

  Lemma filter_len_mono (S T : list cand) (L : list cand) :
    (forall c, In c S -> In c T) ->
    length (filter (fun c => inb c S) L) <= length (filter (fun c => inb c T) L).
  Proof.
    intros H. induction L as [| x xs IH]; simpl; auto.
    destruct (inb x S) eqn:HS.
    - apply inb_true in HS. apply H in HS. apply inb_true in HS. rewrite HS. simpl. lia.
    - destruct (inb x T); simpl; lia.
  Qed.

  Lemma filter_len_strict (S T : list cand) (L : list cand) c :
    (forall x, In x S -> In x T) -> In c L -> In c T -> ~ In c S ->
    length (filter (fun c => inb c S) L) < length (filter (fun c => inb c T) L).
  Proof.
    intros H HcL HcT HcS. induction L as [| x xs IH]; simpl in *; [contradiction | ].
    destruct HcL as [-> | HcL].
    - destruct (inb c S) eqn:HS; [apply inb_true in HS; contradiction | ].
      apply inb_true in HcT. rewrite HcT. simpl.
      pose proof (filter_len_mono S T xs H). lia.
    - specialize (IH HcL).
      destruct (inb x S) eqn:HS.
      + apply inb_true in HS. apply H in HS. apply inb_true in HS. rewrite HS. simpl. lia.
      + destruct (inb x T); simpl; lia.
  Qed.

  Lemma size_le (S T : list cand) : (forall c, In c S -> In c T) -> size S <= size T.
  Proof. intros H. apply filter_len_mono. auto. Qed.

  Lemma size_lt (S T : list cand) c :
    (forall x, In x S -> In x T) -> In c T -> ~ In c S -> size S < size T.
  Proof. intros H Hc Hnc. apply (filter_len_strict S T cand_all c); auto. Qed.

  Lemma filter_len_le (f : cand -> bool) (L : list cand) : length (filter f L) <= length L.
  Proof. induction L as [| x xs IH]; simpl; auto. destruct (f x); simpl; lia. Qed.

  Lemma size_bound S : size S <= length cand_all.
  Proof. unfold size. apply filter_len_le. Qed.

  Lemma size_pos S x : In x S -> 1 <= size S.
  Proof.
    intros Hx. unfold size.
    assert (In x (filter (fun c => inb c S) cand_all)).
    { apply filter_In. split; [apply cand_fin | apply inb_true; auto]. }
    destruct (filter (fun c => inb c S) cand_all); [contradiction | simpl; lia].
  Qed.

  (* a closed set is left unchanged by expansion, syntactically *)
  Lemma expand_closed_id defs S : closed defs S -> expand defs S = S.
  Proof.
    intros Hc. unfold expand.
    assert (filter (fun c => negb (inb c S)) (flat_map (successors defs) S) = []).
    { destruct (filter (fun c => negb (inb c S)) (flat_map (successors defs) S)) as [| c l] eqn:Hf;
        [reflexivity | exfalso].
      assert (In c (filter (fun c => negb (inb c S)) (flat_map (successors defs) S)))
        by (rewrite Hf; left; auto).
      apply filter_In in H. destruct H as [H Hn]. apply negb_true_iff in Hn.
      apply in_flat_map in H. destruct H as [b [Hb Hbc]]. apply successors_in in Hbc.
      pose proof (Hc b c Hb Hbc) as Hin. apply inb_true in Hin. congruence. }
    rewrite H. apply app_nil_r.
  Qed.

  Lemma iterate_closed_id defs S n : closed defs S -> iterate n (expand defs) S = S.
  Proof.
    intros Hc. induction n as [| n IH]; simpl; auto.
    rewrite expand_closed_id; auto.
  Qed.

  (* either the iterate is closed, or every step grew the set *)
  Lemma iterate_closed_or_big defs n S :
    closed defs (iterate n (expand defs) S) \/ size (iterate n (expand defs) S) >= size S + n.
  Proof.
    revert S. induction n as [| n IH]; intros S; simpl.
    - right. lia.
    - destruct (expand_closed_or_grows defs S) as [Hc | [c [Hc Hnc]]].
      + left. rewrite expand_closed_id; auto. rewrite iterate_closed_id; auto.
      + destruct (IH (expand defs S)) as [H | H]; [left; auto | right].
        pose proof (size_lt S (expand defs S) c (expand_grows defs S) Hc Hnc). lia.
  Qed.

  Lemma iterate_nil defs n : iterate n (expand defs) [] = [].
  Proof. induction n; simpl; auto. Qed.

  (* after length cand_all expansions the set is closed *)
  Lemma iterate_closed defs S : closed defs (iterate (length cand_all) (expand defs) S).
  Proof.
    destruct S as [| s S'].
    - rewrite iterate_nil. intros b c Hb. inversion Hb.
    - destruct (iterate_closed_or_big defs (length cand_all) (s :: S')) as [H | H]; auto.
      exfalso.
      pose proof (size_bound (iterate (length cand_all) (expand defs) (s :: S'))).
      pose proof (size_pos (s :: S') s ltac:(left; auto)).
      lia.
  Qed.

  (* -- completeness of tdef --------------------------------------------- *)

  Lemma closed_TDef defs S a :
    closed defs S -> (forall c, In (a, c) defs -> In c S) ->
    forall c, TDef defs a c -> In c S.
  Proof.
    intros Hc Hbase c H.
    (* induction on the right-recursive view: strengthen to any start x in S *)
    assert (Hgen : forall x c, TDef defs x c -> (forall y, In (x, y) defs -> In y S) -> In c S).
    { intros x c0 Hx. induction Hx as [x c0 Hd | x b c0 Hd Ht IH]; intros Hb.
      - apply Hb. auto.
      - apply IH. intros y Hy. apply (Hc b y); auto. }
    apply (Hgen a c H Hbase).
  Qed.

  Lemma tdef_complete defs a c : TDef defs a c -> tdef defs a c = true.
  Proof.
    intros H. unfold tdef, reach. apply inb_true.
    apply (closed_TDef defs (iterate (length cand_all) (expand defs) (successors defs a)) a).
    - apply iterate_closed.
    - intros x Hx. apply iterate_grows. apply successors_in. auto.
    - auto.
  Qed.

  Lemma tdef_iff defs a c : tdef defs a c = true <-> TDef defs a c.
  Proof. split; [apply tdef_sound | apply tdef_complete]. Qed.

  (* ----------------------------------------------------------------------- *)
  (*  The Schwartz set (A.5.6)                                               *)
  (* ----------------------------------------------------------------------- *)

  (* the Schwartz set of the current defeats, among the remaining options.
     A.5.6.1: "An option A is in the Schwartz set if for all options B, either
     A transitively defeats B, or B does not transitively defeat A." Options
     dropped in steps 2 and 3 are "dropped from consideration", so neither A
     nor B ranges over them (no defeat involves a dropped option, so read
     literally the text would put every dropped option in the Schwartz set). *)
  Definition schwartz (rem : list cand) (defs : list defeat) : list cand :=
    filter (fun a => forallb (fun b => tdef defs a b || negb (tdef defs b a)) rem) rem.

  Lemma schwartz_in rem defs a :
    In a (schwartz rem defs) <->
    In a rem /\ forall b, In b rem -> TDef defs a b \/ ~ TDef defs b a.
  Proof.
    unfold schwartz. rewrite filter_In, forallb_forall. split.
    - intros [Ha H]. split; auto. intros b Hb. specialize (H b Hb).
      apply orb_true_iff in H. destruct H as [H | H].
      + left. apply tdef_iff. auto.
      + right. intros Ht. apply tdef_iff in Ht. apply negb_true_iff in H. congruence.
    - intros [Ha H]. split; auto. intros b Hb. specialize (H b Hb). apply orb_true_iff.
      destruct H as [H | H].
      + left. apply tdef_iff. auto.
      + right. apply negb_true_iff. destruct (tdef defs b a) eqn:E; auto.
        apply tdef_iff in E. contradiction.
  Qed.

  (* The Schwartz set of a nonempty set of options is nonempty. Proof: pick a
     with the largest number of options it transitively defeats (counting a
     itself); if some b transitively defeated a without a defeating b, then b
     would transitively defeat strictly more. *)
  Definition dominated (defs : list defeat) (a : cand) : list cand :=
    a :: filter (fun c => tdef defs a c) cand_all.

  Lemma dominated_in defs a c : In c (dominated defs a) <-> c = a \/ TDef defs a c.
  Proof.
    unfold dominated. simpl. rewrite filter_In. split.
    - intros [-> | [_ H]]; [left; auto | right; apply tdef_iff; auto].
    - intros [-> | H]; [left; auto | right; split; [apply cand_fin | apply tdef_iff; auto]].
  Qed.

  (* an element of a nonempty list maximising a measure *)
  Fixpoint argmax (f : cand -> nat) (x : cand) (l : list cand) : cand :=
    match l with
    | [] => x
    | y :: ys => if f x <? f y then argmax f y ys else argmax f x ys
    end.

  Lemma argmax_in f x l : In (argmax f x l) (x :: l).
  Proof.
    revert x. induction l as [| y ys IH]; intros x; simpl; auto.
    destruct (f x <? f y).
    - destruct (IH y) as [H | H]; [right; left; auto | right; right; auto].
    - destruct (IH x) as [H | H]; [left; auto | right; right; auto].
  Qed.

  Lemma argmax_ge f x l : forall z, In z (x :: l) -> f z <= f (argmax f x l).
  Proof.
    revert x. induction l as [| y ys IH]; intros x z Hz; simpl in *.
    - destruct Hz as [-> | []]. auto.
    - destruct (f x <? f y) eqn:E.
      + apply Nat.ltb_lt in E. destruct Hz as [-> | [-> | Hz]].
        * pose proof (IH y y ltac:(left; auto)). lia.
        * apply IH. left. auto.
        * apply IH. right. auto.
      + apply Nat.ltb_ge in E. destruct Hz as [-> | [-> | Hz]].
        * apply IH. left. auto.
        * pose proof (IH x x ltac:(left; auto)). lia.
        * apply IH. right. auto.
  Qed.

  Lemma schwartz_nonempty rem defs : rem <> [] -> schwartz rem defs <> [].
  Proof.
    intros Hne. destruct rem as [| r rs]; [congruence | ].
    set (f := fun a => size (dominated defs a)).
    set (a := argmax f r rs).
    assert (Ha : In a (r :: rs)) by apply argmax_in.
    assert (Hmax : forall z, In z (r :: rs) -> f z <= f a) by apply argmax_ge.
    assert (Hin : In a (schwartz (r :: rs) defs)).
    { apply schwartz_in. split; auto. intros b Hb.
      destruct (tdef defs a b) eqn:Hab; [left; apply tdef_iff; auto | right].
      intros Hba.
      (* b transitively defeats a and a does not transitively defeat b:
         dominated b strictly contains dominated a *)
      assert (Hsub : forall c, In c (dominated defs a) -> In c (dominated defs b)).
      { intros c Hc. apply dominated_in in Hc. apply dominated_in.
        destruct Hc as [-> | Hc]; right; [auto | apply TDef_trans with a; auto]. }
      assert (Hb_in : In b (dominated defs b)) by (apply dominated_in; left; auto).
      assert (Hb_nin : ~ In b (dominated defs a)).
      { intros H. apply dominated_in in H. destruct H as [-> | H].
        - apply tdef_iff in Hba. rewrite Hba in Hab. discriminate.
        - apply tdef_iff in H. rewrite H in Hab. discriminate. }
      pose proof (size_lt _ _ b Hsub Hb_in Hb_nin) as Hlt.
      specialize (Hmax b Hb). unfold f in Hmax. lia. }
    intros Heq. rewrite Heq in Hin. inversion Hin.
  Qed.

  (* ----------------------------------------------------------------------- *)
  (*  Weakest defeats and sequential dropping (A.5.7, A.5.8)                 *)
  (* ----------------------------------------------------------------------- *)

  (* (A,X) is weaker than (B,Y). A.5.7.1: "A defeat (A,X) is weaker than a
     defeat (B,Y) if V(A,X) is less than V(B,Y). Also, (A,X) is weaker than
     (B,Y) if V(A,X) is equal to V(B,Y) and V(X,A) is greater than V(Y,B)." *)
  Definition weaker (p q : defeat) : bool :=
    let '(a, x) := p in let '(b, y) := q in
    (Vm a x <? Vm b y) || ((Vm a x =? Vm b y) && (Vm y b <? Vm x a)).

  (* the defeats between options of the Schwartz set; A.5.7: "If there are
     defeats between options in the Schwartz set, ..." *)
  Definition inner (rem : list cand) (defs : list defeat) : list defeat :=
    let S := schwartz rem defs in
    filter (fun p => inb (fst p) S && inb (snd p) S) defs.

  (* the weakest among a list of defeats: those with nothing weaker.
     A.5.7.2: "A weakest defeat is a defeat that has no other defeat weaker
     than it. There may be more than one such defeat." *)
  Definition weakest (l : list defeat) : list defeat :=
    filter (fun p => forallb (fun q => negb (weaker q p)) l) l.

  Definition remove_all (l : list defeat) (defs : list defeat) : list defeat :=
    filter (fun p => negb (existsb (deq p) l)) defs.

  (* one round of A.5.7: "we drop the weakest such defeats from the list of
     pairwise defeats". "Such" refers to the defeats within the Schwartz set,
     so "weakest" is taken among those (inner), and all of them are dropped *)
  Definition drop_weakest (rem : list cand) (defs : list defeat) : list defeat :=
    remove_all (weakest (inner rem defs)) defs.

  (* The specification of steps 5-8, as a relation between the current list
     of defeats and the resulting winners. *)
  Inductive cssd_spec (rem : list cand) : list defeat -> list cand -> Prop :=
  (* A.5.8: no defeats within the Schwartz set; its options are the winners *)
  | cssd_done defs :
      inner rem defs = [] ->
      cssd_spec rem defs (schwartz rem defs)
  (* A.5.7: drop the weakest inner defeats "and return to step 5" *)
  | cssd_step defs W :
      inner rem defs <> [] ->
      cssd_spec rem (drop_weakest rem defs) W ->
      cssd_spec rem defs W.

  (* the implementation, with fuel *)
  Fixpoint cssd (fuel : nat) (rem : list cand) (defs : list defeat) : list cand :=
    match fuel with
    | O => schwartz rem defs
    | S f =>
      match inner rem defs with
      | [] => schwartz rem defs
      | _ => cssd f rem (drop_weakest rem defs)
      end
    end.

  (* -- the weakest defeats of a nonempty list are nonempty ---------------- *)

  (* weaker is a strict order: irreflexive and transitive *)
  Lemma weaker_irrefl p : weaker p p = false.
  Proof.
    destruct p as [a x]. simpl. rewrite Nat.ltb_irrefl. simpl. rewrite Nat.ltb_irrefl.
    apply andb_false_r.
  Qed.

  Lemma weaker_trans p q r : weaker p q = true -> weaker q r = true -> weaker p r = true.
  Proof.
    destruct p as [a x], q as [b y], r as [c z]. simpl.
    rewrite !orb_true_iff, !andb_true_iff, !Nat.ltb_lt, !Nat.eqb_eq.
    intros [H1 | [H1 H2]] [H3 | [H3 H4]]; try (left; lia); right; lia.
  Qed.

  (* A finite nonempty list has an element with nothing weaker in the list
     (weaker is a strict partial order: irreflexive and transitive). *)
  Fixpoint pick_min (x : defeat) (l : list defeat) : defeat :=
    match l with
    | [] => x
    | y :: ys => let m := pick_min y ys in if weaker x m then x else m
    end.

  Lemma pick_min_spec x l :
    In (pick_min x l) (x :: l) /\ forall q, In q (x :: l) -> weaker q (pick_min x l) = false.
  Proof.
    revert x. induction l as [| y ys IH]; intros x; simpl.
    - split; [left; auto | ]. intros q [-> | []]. apply weaker_irrefl.
    - destruct (IH y) as [Hin Hmin].
      destruct (weaker x (pick_min y ys)) eqn:E.
      + split; [left; auto | ]. intros q [-> | Hq]; [apply weaker_irrefl | ].
        destruct (weaker q x) eqn:F; auto.
        pose proof (weaker_trans _ _ _ F E) as G. rewrite (Hmin q Hq) in G. discriminate.
      + split; [right; auto | ]. intros q [-> | Hq]; auto.
  Qed.

  Lemma weakest_nonempty l : l <> [] -> weakest l <> [].
  Proof.
    intros Hne. destruct l as [| x l']; [congruence | ].
    destruct (pick_min_spec x l') as [Hin Hmin].
    assert (In (pick_min x l') (weakest (x :: l'))).
    { unfold weakest. apply filter_In. split; auto. apply forallb_forall.
      intros q Hq. apply negb_true_iff. apply Hmin. auto. }
    intros Heq. rewrite Heq in H. inversion H.
  Qed.

  Lemma weakest_sub l p : In p (weakest l) -> In p l.
  Proof. unfold weakest. intros H. apply filter_In in H. destruct H. auto. Qed.

  Lemma inner_sub rem defs p : In p (inner rem defs) -> In p defs.
  Proof. unfold inner. intros H. apply filter_In in H. destruct H. auto. Qed.

  Lemma remove_all_sub l defs p : In p (remove_all l defs) -> In p defs.
  Proof. unfold remove_all. intros H. apply filter_In in H. destruct H. auto. Qed.

  Lemma remove_all_removes l defs p : In p l -> ~ In p (remove_all l defs).
  Proof.
    intros Hp H. unfold remove_all in H. apply filter_In in H. destruct H as [_ H].
    apply negb_true_iff in H.
    assert (existsb (deq p) l = true).
    { apply existsb_exists. exists p. split; auto. apply deq_true. auto. }
    congruence.
  Qed.

  Lemma filter_len_le' (f : defeat -> bool) (l : list defeat) : length (filter f l) <= length l.
  Proof. induction l as [| x xs IH]; simpl; auto. destruct (f x); simpl; lia. Qed.

  Lemma filter_strict (f : defeat -> bool) (l : list defeat) p :
    In p l -> f p = false -> length (filter f l) < length l.
  Proof.
    induction l as [| x xs IH]; intros Hp Hf; simpl in *; [contradiction | ].
    destruct Hp as [-> | Hp].
    - rewrite Hf. pose proof (filter_len_le' f xs). lia.
    - specialize (IH Hp Hf). destruct (f x); simpl; lia.
  Qed.

  (* dropping strictly shortens the list of defeats *)
  Lemma drop_weakest_shorter rem defs :
    inner rem defs <> [] -> length (drop_weakest rem defs) < length defs.
  Proof.
    intros Hne. unfold drop_weakest, remove_all.
    pose proof (weakest_nonempty _ Hne) as Hw.
    destruct (weakest (inner rem defs)) as [| p w] eqn:Hwk; [congruence | ].
    assert (Hp : In p defs).
    { apply inner_sub with rem. apply weakest_sub with (l := inner rem defs). rewrite Hwk. left. auto. }
    apply (filter_strict _ defs p Hp).
    apply negb_false_iff. apply existsb_exists. exists p. split; [left; auto | apply deq_true; auto].
  Qed.

  (* -- the implementation satisfies the specification ---------------------- *)

  Theorem cssd_correct rem : forall fuel defs,
    length defs <= fuel -> cssd_spec rem defs (cssd fuel rem defs).
  Proof.
    induction fuel as [| f IH]; intros defs Hlen; simpl.
    - (* defs = [] so inner = [] *)
      destruct defs; [ | simpl in Hlen; lia].
      apply cssd_done. reflexivity.
    - destruct (inner rem defs) as [| p l] eqn:Hin.
      + apply cssd_done. auto.
      + apply cssd_step; [rewrite Hin; discriminate | ].
        apply IH. pose proof (drop_weakest_shorter rem defs ltac:(rewrite Hin; discriminate)). lia.
  Qed.

  (* the specification is a function *)
  Theorem cssd_spec_functional rem defs W1 W2 :
    cssd_spec rem defs W1 -> cssd_spec rem defs W2 -> W1 = W2.
  Proof.
    intros H1. revert W2. induction H1 as [defs Hi | defs W1 Hi H1 IH]; intros W2 H2.
    - inversion H2; subst; auto. contradiction.
    - inversion H2; subst; [contradiction | ]. apply IH. auto.
  Qed.

  (* the winners are a Schwartz set (of the final list of defeats), and there
     is at least one winner *)
  Theorem cssd_winners_schwartz rem defs W :
    cssd_spec rem defs W -> exists defs', W = schwartz rem defs' /\ inner rem defs' = [].
  Proof.
    intros H. induction H as [defs Hi | defs W Hi H IH]; [exists defs; auto | auto].
  Qed.

  Theorem cssd_nonempty rem defs W : rem <> [] -> cssd_spec rem defs W -> W <> [].
  Proof.
    intros Hne H. destruct (cssd_winners_schwartz rem defs W H) as [defs' [-> _]].
    apply schwartz_nonempty. auto.
  Qed.

  (* -- a Condorcet winner among the remaining options wins outright ------- *)

  (* any transitive defeat of a ends with a direct defeat of a *)
  Lemma TDef_last defs b a : TDef defs b a -> exists x, In (x, a) defs.
  Proof.
    intros H. induction H as [b a Hd | b c a Hd Ht IH]; [exists b; auto | auto].
  Qed.

  Theorem condorcet_winner rem defs a :
    NoDup rem -> In a rem ->
    (forall b, In b rem -> b <> a -> In (a, b) defs) ->
    (forall x, ~ In (x, a) defs) ->
    cssd_spec rem defs [a].
  Proof.
    intros Hnd Ha Hbeats Hnone.
    assert (Hsch : schwartz rem defs = [a]).
    { (* a is in the Schwartz set and nothing else is *)
      assert (Hmem : forall b, In b (schwartz rem defs) <-> b = a).
      { intros b. rewrite schwartz_in. split.
        - intros [Hb Hall]. destruct (dec_cand b a) as [| Hne]; auto. exfalso.
          specialize (Hall a Ha). destruct Hall as [Hba | Hnab].
          + destruct (TDef_last _ _ _ Hba) as [x Hx]. apply (Hnone x). auto.
          + apply Hnab. constructor. apply Hbeats; auto.
        - intros ->. split; auto. intros b Hb. right. intros Hba.
          destruct (TDef_last _ _ _ Hba) as [x Hx]. apply (Hnone x). auto. }
      (* schwartz is a filter of rem, which has no duplicates, so it is [a] *)
      unfold schwartz in *. 
      assert (Hnd' : NoDup (filter (fun a0 => forallb (fun b => tdef defs a0 b || negb (tdef defs b a0)) rem) rem))
        by (apply NoDup_filter; auto).
      destruct (filter (fun a0 => forallb (fun b => tdef defs a0 b || negb (tdef defs b a0)) rem) rem)
        as [| x [| y l]] eqn:Hf.
      - exfalso. assert (In a []) by (apply Hmem; auto). inversion H.
      - f_equal. apply Hmem. left. auto.
      - exfalso. assert (x = a) by (apply Hmem; left; auto).
        assert (y = a) by (apply Hmem; right; left; auto). subst.
        inversion Hnd'. apply H1. left. auto. }
    assert (Hinner : inner rem defs = []).
    { unfold inner. rewrite Hsch.
      destruct (filter (fun p => inb (fst p) [a] && inb (snd p) [a]) defs) as [| p l] eqn:Hf; auto.
      exfalso.
      assert (In p (filter (fun p => inb (fst p) [a] && inb (snd p) [a]) defs)) by (rewrite Hf; left; auto).
      apply filter_In in H. destruct H as [Hp H]. apply andb_true_iff in H. destruct H as [H1 H2].
      apply inb_true in H1. apply inb_true in H2. destruct p as [x y]. simpl in *.
      destruct H1 as [H1 | []]. destruct H2 as [H2 | []]. apply (Hnone x). rewrite H2. exact Hp. }
    rewrite <- Hsch. apply cssd_done. auto.
  Qed.

  (* ----------------------------------------------------------------------- *)
  (*  Steps 5-8 on sets (A.5.5 - A.5.8)                                       *)
  (* ----------------------------------------------------------------------- *)

  (* The text speaks of sets of options and of defeats. Here the options under
     consideration are a predicate R, the current defeats a predicate D and
     the winners a predicate W: there are no lists, no enumeration of the
     options, no fuel and no order. This is the specification a reader checks
     against the Constitution; cssd_spec above is the bridge to the program. *)

  (* A.5.5.1: "An option A transitively defeats an option C if A defeats C or
     if there is some other option B where A defeats B AND B transitively
     defeats C." (see TDef) *)
  Inductive TD (D : defeat -> Prop) : cand -> cand -> Prop :=
  | td_direct a c : D (a, c) -> TD D a c
  | td_via a b c : D (a, b) -> TD D b c -> TD D a c.

  (* A.5.6.1: "An option A is in the Schwartz set if for all options B, either
     A transitively defeats B, or B does not transitively defeat A." A and B
     range over the options still under consideration (see schwartz) *)
  Definition Schwartz (R : cand -> Prop) (D : defeat -> Prop) (a : cand) : Prop :=
    R a /\ forall b, R b -> TD D a b \/ ~ TD D b a.

  (* A.5.7: "defeats between options in the Schwartz set" *)
  Definition Inner (R : cand -> Prop) (D : defeat -> Prop) (p : defeat) : Prop :=
    D p /\ Schwartz R D (fst p) /\ Schwartz R D (snd p).

  (* A.5.7.2: "A weakest defeat is a defeat that has no other defeat weaker
     than it", among the defeats of A.5.7 ("the weakest such defeats");
     weaker is A.5.7.1 *)
  Definition Weakest (R : cand -> Prop) (D : defeat -> Prop) (p : defeat) : Prop :=
    Inner R D p /\ forall q, Inner R D q -> weaker q p = false.

  Inductive SSD (R : cand -> Prop) : (defeat -> Prop) -> (cand -> Prop) -> Prop :=
  (* A.5.8: "If there are no defeats within the Schwartz set, then the winner
     is chosen from the options in the Schwartz set." W is that set; the
     casting vote among several winners is outside the count *)
  | ssd_done D W :
      (forall p, ~ Inner R D p) ->
      (forall a, W a <-> Schwartz R D a) ->
      SSD R D W
  (* A.5.7: "If there are defeats between options in the Schwartz set, we
     drop the weakest such defeats from the list of pairwise defeats, and
     return to step 5." D' is D without its weakest inner defeats *)
  | ssd_step D D' W :
      (exists p, Inner R D p) ->
      (forall p, D' p <-> D p /\ ~ Weakest R D p) ->
      SSD R D' W ->
      SSD R D W.

  Lemma TD_ext (D D' : defeat -> Prop) a b :
    (forall p, D p <-> D' p) -> TD D a b -> TD D' a b.
  Proof.
    intros HD H. induction H as [a c H | a b c H _ IH].
    - apply td_direct, HD, H.
    - apply td_via with b; [apply HD, H | exact IH].
  Qed.

  Lemma Schwartz_ext (R R' : cand -> Prop) (D D' : defeat -> Prop) a :
    (forall x, R x <-> R' x) -> (forall p, D p <-> D' p) ->
    Schwartz R D a -> Schwartz R' D' a.
  Proof.
    intros HR HD [Ha H]. split; [apply HR, Ha | ].
    intros b Hb. destruct (H b (proj2 (HR b) Hb)) as [H1 | H1].
    - left. apply TD_ext with D; auto.
    - right. intros H2. apply H1. apply TD_ext with D'; [intros p; split; apply HD | exact H2].
  Qed.

  Lemma Inner_ext (R R' : cand -> Prop) (D D' : defeat -> Prop) p :
    (forall x, R x <-> R' x) -> (forall p, D p <-> D' p) -> Inner R D p -> Inner R' D' p.
  Proof.
    intros HR HD [H1 [H2 H3]]. split; [apply HD, H1 | split; apply Schwartz_ext with R D; auto].
  Qed.

  Lemma Weakest_ext (R R' : cand -> Prop) (D D' : defeat -> Prop) p :
    (forall x, R x <-> R' x) -> (forall p, D p <-> D' p) -> Weakest R D p -> Weakest R' D' p.
  Proof.
    intros HR HD [H1 H2]. split; [apply Inner_ext with R D; auto | ].
    intros q Hq. apply H2. apply Inner_ext with R' D'; [intros x; split; apply HR | intros r; split; apply HD | exact Hq].
  Qed.

  (* the specification determines the winners, up to equivalence of the sets *)
  Theorem SSD_functional (R R' : cand -> Prop) D W :
    (forall x, R x <-> R' x) -> SSD R D W ->
    forall D' W', (forall p, D p <-> D' p) -> SSD R' D' W' -> forall a, W a <-> W' a.
  Proof.
    intros HR H. induction H as [D W Hn HW | D D1 W [p Hp] HD1 H IH];
      intros D' W' HD H'; destruct H' as [D'0 W'0 Hn' HW' | D'0 D'1 W'0 [p' Hp'] HD'1 H'].
    - intros a. rewrite HW, HW'. split; apply Schwartz_ext; auto; intros; symmetry; auto.
    - exfalso. apply (Hn p'). apply Inner_ext with R' D'0; [intros; symmetry; auto | intros; symmetry; auto | exact Hp'].
    - exfalso. apply (Hn' p). apply Inner_ext with R D; auto.
    - apply IH with D'1; auto. intros q. rewrite HD1, HD'1. split; intros [H1 H2]; split.
      + apply HD, H1.
      + intros H3. apply H2. apply Weakest_ext with R' D'0; [intros; symmetry; auto | intros; symmetry; auto | exact H3].
      + apply HD, H1.
      + intros H3. apply H2. apply Weakest_ext with R D; auto.
  Qed.

  Lemma SSD_ext (R R' : cand -> Prop) D W :
    (forall x, R x <-> R' x) -> SSD R D W ->
    forall D' W', (forall p, D p <-> D' p) -> (forall a, W a <-> W' a) -> SSD R' D' W'.
  Proof.
    intros HR H. induction H as [D W Hn HW | D D1 W [p Hp] HD1 H IH]; intros D' W' HD HW'.
    - apply ssd_done.
      + intros p Hp. apply (Hn p). apply Inner_ext with R' D'; [intros; symmetry; auto | intros; symmetry; auto | exact Hp].
      + intros a. rewrite <- HW', HW. split; apply Schwartz_ext; auto; intros; symmetry; auto.
    - apply ssd_step with D1.
      + exists p. apply Inner_ext with R D; auto.
      + intros q. rewrite HD1. split; intros [H1 H2]; split.
        * apply HD, H1.
        * intros H3. apply H2. apply Weakest_ext with R' D'; [intros; symmetry; auto | intros; symmetry; auto | exact H3].
        * apply HD, H1.
        * intros H3. apply H2. apply Weakest_ext with R D; auto.
      + apply IH; [intros; reflexivity | exact HW'].
  Qed.

  (* -- the list-based relation cssd_spec is an instance ------------------- *)

  Lemma TDef_TD defs a b : TDef defs a b <-> TD (fun p => In p defs) a b.
  Proof.
    split; intros H; induction H; [apply td_direct | eapply td_via | apply tdef_direct | eapply tdef_via]; eauto.
  Qed.

  Lemma schwartz_Schwartz rem defs a :
    In a (schwartz rem defs) <-> Schwartz (fun x => In x rem) (fun p => In p defs) a.
  Proof.
    rewrite schwartz_in. unfold Schwartz. split; intros [Ha H]; split; auto; intros b Hb;
      destruct (H b Hb) as [H1 | H1]; [left | right | left | right]; rewrite ?TDef_TD in *; auto;
      intros H2; apply H1; rewrite ?TDef_TD in *; auto.
  Qed.

  Lemma inner_Inner rem defs p :
    In p (inner rem defs) <-> Inner (fun x => In x rem) (fun p => In p defs) p.
  Proof using cand_all cand_fin dec_cand Vm.
    unfold inner, Inner. rewrite filter_In, andb_true_iff, !inb_true, !schwartz_Schwartz. reflexivity.
  Qed.

  Lemma weakest_in l p : In p (weakest l) <-> In p l /\ forall q, In q l -> weaker q p = false.
  Proof.
    unfold weakest. rewrite filter_In, forallb_forall. split; intros [H1 H2]; split; auto;
      intros q Hq; specialize (H2 q Hq); [apply negb_true_iff | apply negb_true_iff in H2]; auto.
  Qed.

  Lemma weakest_Weakest rem defs p :
    In p (weakest (inner rem defs)) <-> Weakest (fun x => In x rem) (fun p => In p defs) p.
  Proof.
    rewrite weakest_in, inner_Inner. unfold Weakest. split; intros [H1 H2]; split; auto;
      intros q Hq; apply H2, inner_Inner, Hq.
  Qed.

  Lemma remove_all_in l defs p : In p (remove_all l defs) <-> In p defs /\ ~ In p l.
  Proof.
    unfold remove_all. rewrite filter_In, negb_true_iff. split; intros [H1 H2]; split; auto.
    - intros H. assert (existsb (deq p) l = true) by (apply existsb_exists; exists p; split; auto; apply deq_true; auto).
      congruence.
    - destruct (existsb (deq p) l) eqn:E; auto. exfalso. apply existsb_exists in E.
      destruct E as [q [Hq E]]. apply deq_true in E. subst. auto.
  Qed.

  Lemma drop_weakest_in rem defs p :
    In p (drop_weakest rem defs) <->
    In p defs /\ ~ Weakest (fun x => In x rem) (fun p => In p defs) p.
  Proof. unfold drop_weakest. rewrite remove_all_in, weakest_Weakest. tauto. Qed.

  Lemma inner_nil rem defs :
    inner rem defs = [] <-> forall p, ~ Inner (fun x => In x rem) (fun p => In p defs) p.
  Proof using cand_all cand_fin dec_cand Vm.
    split.
    - intros H p Hp. apply inner_Inner in Hp. rewrite H in Hp. inversion Hp.
    - intros H. destruct (inner rem defs) as [| p l] eqn:E; [reflexivity | ]. exfalso. apply (H p).
      apply inner_Inner. rewrite E. left. reflexivity.
  Qed.

  Theorem cssd_SSD rem defs W :
    cssd_spec rem defs W -> SSD (fun x => In x rem) (fun p => In p defs) (fun w => In w W).
  Proof.
    intros H. induction H as [defs Hi | defs W Hi H IH].
    - apply ssd_done; [apply inner_nil, Hi | intros a; apply schwartz_Schwartz].
    - apply ssd_step with (fun p => In p (drop_weakest rem defs)); auto.
      + destruct (inner rem defs) as [| p l] eqn:E; [congruence | ].
        exists p. apply inner_Inner. rewrite E. left. auto.
      + intros p. apply drop_weakest_in.
  Qed.

  (* hence cssd_spec only depends on which options and defeats are present *)
  Corollary cssd_spec_same rem rem' defs defs' W W' :
    (forall x, In x rem <-> In x rem') -> (forall p, In p defs <-> In p defs') ->
    cssd_spec rem defs W -> cssd_spec rem' defs' W' -> forall a, In a W <-> In a W'.
  Proof.
    intros HR HD H H'. apply (SSD_functional _ _ _ _ HR (cssd_SSD _ _ _ H) _ _ HD (cssd_SSD _ _ _ H')).
  Qed.

  (* ----------------------------------------------------------------------- *)
  (*  The winners lie in the initial Schwartz set                            *)
  (* ----------------------------------------------------------------------- *)

  (* the defeats are among the options under consideration *)
  Definition defs_within (rem : list cand) (defs : list defeat) : Prop :=
    forall a b, In (a, b) defs -> In a rem /\ In b rem.

  Lemma TDef_mono defs defs' a b :
    (forall p, In p defs' -> In p defs) -> TDef defs' a b -> TDef defs a b.
  Proof.
    intros Hs H. induction H; [apply tdef_direct | eapply tdef_via]; eauto.
  Qed.

  (* no defeat enters the Schwartz set from outside *)
  Lemma schwartz_closed rem defs u v :
    defs_within rem defs -> In v (schwartz rem defs) -> In (u, v) defs -> In u (schwartz rem defs).
  Proof.
    intros Hw Hv Huv. apply schwartz_in in Hv. destruct Hv as [Hvr Hv].
    apply schwartz_in. split; [apply (Hw u v Huv) | ]. intros b Hb.
    destruct (tdef defs u b) eqn:E; [left; apply tdef_iff; auto | right].
    intros Hbu. destruct (Hv b Hb) as [Hvb | Hnbv].
    - assert (TDef defs u b) by (apply tdef_via with v; auto). apply tdef_iff in H. congruence.
    - apply Hnbv. apply TDef_snoc with u; auto.
  Qed.

  Lemma TDef_into_schwartz rem defs x s :
    defs_within rem defs -> TDef defs x s -> In s (schwartz rem defs) -> In x (schwartz rem defs).
  Proof.
    intros Hw H. induction H as [x s H | x b s H _ IH]; intros Hs.
    - apply schwartz_closed with s; auto.
    - apply schwartz_closed with b; auto.
  Qed.

  (* every option outside the Schwartz set is transitively defeated from it *)
  Lemma outside_schwartz rem defs x :
    In x rem -> ~ In x (schwartz rem defs) ->
    exists s, In s (schwartz rem defs) /\ TDef defs s x.
  Proof.
    intros Hx Hnx.
    (* some b defeats x transitively without being defeated back *)
    assert (Hb : exists b, In b rem /\ TDef defs b x).
    { destruct (forallb (fun b => tdef defs x b || negb (tdef defs b x)) rem) eqn:E.
      - exfalso. apply Hnx. unfold schwartz. apply filter_In. auto.
      - assert (Hex : exists b, In b rem /\ (tdef defs x b || negb (tdef defs b x)) = false).
        { clear Hx Hnx. induction rem as [| y ys IH]; [discriminate | ]. simpl in E.
          destruct (tdef defs x y || negb (tdef defs y x)) eqn:Ey; simpl in E.
          - destruct (IH E) as [b [Hb Hb']]. exists b. split; [right |]; auto.
          - exists y. split; [left |]; auto. }
        destruct Hex as [b [Hb Hb']]. exists b. split; auto.
        apply orb_false_iff in Hb'. destruct Hb' as [_ Hb']. apply negb_false_iff in Hb'.
        apply tdef_iff. auto. }
    destruct Hb as [b0 [Hb0 Hb0x]].
    (* take, among the options transitively defeating x, one that transitively
       defeats the most options; it is in the Schwartz set *)
    set (C := filter (fun b => tdef defs b x) rem).
    assert (HC : In b0 C) by (apply filter_In; split; auto; apply tdef_iff; auto).
    destruct C as [| c cs] eqn:EC; [inversion HC | ].
    set (f := fun a => size (dominated defs a)).
    set (a := argmax f c cs).
    assert (Ha : In a (c :: cs)) by apply argmax_in.
    assert (Hmax : forall z, In z (c :: cs) -> f z <= f a) by apply argmax_ge.
    rewrite <- EC in Ha, Hmax. unfold C in Ha, Hmax. apply filter_In in Ha. destruct Ha as [Har Hax].
    apply tdef_iff in Hax. exists a. split; auto.
    apply schwartz_in. split; auto. intros b Hb.
    destruct (tdef defs a b) eqn:Hab; [left; apply tdef_iff; auto | right].
    intros Hba.
    assert (Hsub : forall c, In c (dominated defs a) -> In c (dominated defs b)).
    { intros c0 Hc. apply dominated_in in Hc. apply dominated_in.
      destruct Hc as [-> | Hc]; right; [auto | apply TDef_trans with a; auto]. }
    assert (Hb_in : In b (dominated defs b)) by (apply dominated_in; left; auto).
    assert (Hb_nin : ~ In b (dominated defs a)).
    { intros H. apply dominated_in in H. destruct H as [-> | H].
      - apply tdef_iff in Hba. rewrite Hba in Hab. discriminate.
      - apply tdef_iff in H. rewrite H in Hab. discriminate. }
    pose proof (size_lt _ _ b Hsub Hb_in Hb_nin) as Hlt.
    assert (HbC : In b (filter (fun b => tdef defs b x) rem)).
    { apply filter_In. split; auto. apply tdef_iff. apply TDef_trans with a; auto. }
    specialize (Hmax b HbC). unfold f in Hmax. lia.
  Qed.

  Lemma drop_weakest_sub rem defs p : In p (drop_weakest rem defs) -> In p defs.
  Proof. apply remove_all_sub. Qed.

  (* a defeat that does not lie inside the Schwartz set survives a round *)
  Lemma drop_weakest_keeps rem defs a b :
    In (a, b) defs -> ~ In b (schwartz rem defs) -> In (a, b) (drop_weakest rem defs).
  Proof.
    intros H Hb. unfold drop_weakest. apply remove_all_in. split; auto.
    intros Hw. apply weakest_sub in Hw. unfold inner in Hw. apply filter_In in Hw.
    destruct Hw as [_ Hw]. apply andb_true_iff in Hw. destruct Hw as [_ Hw].
    apply inb_true in Hw. contradiction.
  Qed.

  Lemma TDef_outside rem defs b x :
    defs_within rem defs -> ~ In b (schwartz rem defs) -> TDef defs b x ->
    TDef (drop_weakest rem defs) b x.
  Proof.
    intros Hw Hb H. induction H as [b x H | b y x H Hyx IH].
    - apply tdef_direct. apply drop_weakest_keeps; auto.
      intros Hx. apply Hb. apply schwartz_closed with x; auto.
    - assert (Hy : ~ In y (schwartz rem defs)) by (intros Hy; apply Hb; apply schwartz_closed with y; auto).
      apply tdef_via with y; [apply drop_weakest_keeps | apply IH]; auto.
  Qed.

  Lemma TDef_exit rem defs s x :
    defs_within rem defs -> In s (schwartz rem defs) -> ~ In x (schwartz rem defs) ->
    TDef defs s x -> exists s', In s' (schwartz rem defs) /\ TDef (drop_weakest rem defs) s' x.
  Proof.
    intros Hw Hs Hx H. induction H as [s x H | s y x H Hyx IH].
    - exists s. split; auto. apply tdef_direct, drop_weakest_keeps; auto.
    - destruct (inb y (schwartz rem defs)) eqn:Ey.
      + apply inb_true in Ey. apply IH; auto.
      + assert (Hy : ~ In y (schwartz rem defs)) by (intros Hy; apply inb_true in Hy; congruence).
        exists s. split; auto. apply tdef_via with y; [apply drop_weakest_keeps | apply TDef_outside]; auto.
  Qed.

  (* a round of step 7 never enlarges the Schwartz set *)
  Lemma schwartz_drop_sub rem defs x :
    defs_within rem defs ->
    In x (schwartz rem (drop_weakest rem defs)) -> In x (schwartz rem defs).
  Proof.
    intros Hw Hx. destruct (inb x (schwartz rem defs)) eqn:E; [apply inb_true; auto | exfalso].
    assert (Hnx : ~ In x (schwartz rem defs)) by (intros H; apply inb_true in H; congruence).
    apply schwartz_in in Hx. destruct Hx as [Hxr Hx].
    destruct (outside_schwartz rem defs x Hxr Hnx) as [s [Hs Hsx]].
    destruct (TDef_exit rem defs s x Hw Hs Hnx Hsx) as [s' [Hs' Hs'x]].
    assert (Hs'r : In s' rem) by (apply schwartz_in in Hs'; tauto).
    destruct (Hx s' Hs'r) as [Hxs' | Hn]; [ | contradiction].
    apply Hnx. apply TDef_into_schwartz with s'; auto.
    apply TDef_mono with (drop_weakest rem defs); auto. apply drop_weakest_sub.
  Qed.

  Theorem cssd_winners_in_schwartz rem defs W :
    defs_within rem defs -> cssd_spec rem defs W ->
    forall w, In w W -> In w (schwartz rem defs).
  Proof.
    intros Hw H. induction H as [defs Hi | defs W Hi H IH]; intros w Hin; auto.
    apply schwartz_drop_sub; auto. apply IH; auto.
    intros a b Hab. apply Hw. apply drop_weakest_sub with rem. auto.
  Qed.

  (* any transitive defeat starts with a direct defeat *)
  Lemma TDef_first defs a c : TDef defs a c -> exists y, In (a, y) defs.
  Proof. intros H. destruct H as [a c H | a b c H _]; eauto. Qed.

  (* ----------------------------------------------------------------------- *)
  (*  Rules of a particular vote: quorum and majority ratios (A.5.2, A.5.3)  *)
  (*  (placed last so that no earlier lemma depends on them)                 *)
  (* ----------------------------------------------------------------------- *)


  (* The quorum R is a non-negative real: Debian computes Q = sqrt(n)/2 from
     the number n of developers and uses R = 3Q, which is irrational unless n
     is a perfect square. Since V(A,D) >= R iff V(A,D)^2 >= R^2, we store R^2
     exactly, as the fraction quorum_num / quorum_den (9n/4 for Debian).

     The majority ratio of an option is S for a supermajority of S:1, and 1
     otherwise. The majority rule itself changed with version 1.6 of the
     Constitution (13 December 2015): before, A passed if V(A,D) > N V(D,A);
     since, if V(A,D) >= N V(D,A) and V(A,D) > V(D,A). strict_majority selects
     the earlier rule. *)
  Record rules := {
    quorum_num : nat;           (* R^2 = quorum_num / quorum_den *)
    quorum_den : nat;
    ratio : cand -> nat;
    strict_majority : bool      (* the rule of versions 1.0 to 1.5 *)
  }.

  Variable rl : rules.

  (* A.5.2, on the square of the quorum (see Quorum) *)
  Definition passes_quorum (x : cand) : bool :=
    ceq x default || (quorum_num rl <=? quorum_den rl * (Vm x default * Vm x default)).

  (* A.5.3, in the version given by strict_majority (see Majority) *)
  Definition passes_majority (x : cand) : bool :=
    ceq x default ||
    (if strict_majority rl then ratio rl x * Vm default x <? Vm x default
     else (ratio rl x * Vm default x <=? Vm x default) && (Vm default x <? Vm x default)).

  (* the options that survive steps 2 and 3 (A.5.2, A.5.3) *)
  Definition remaining : list cand :=
    filter (fun x => passes_quorum x && passes_majority x) cand_all.

  (* Steps 2 and 3 as propositions, transcribing the text *)

  (* A.5.2: "If the ballot has a quorum requirement R any options other than
     the default option which do not receive at least R votes ranking that
     option above the default option are dropped from consideration."
     V(x,D) >= R iff V(x,D)^2 >= R^2 = quorum_num / quorum_den; a ballot
     without a quorum requirement has quorum_num = 0 *)
  Definition Quorum (x : cand) : Prop :=
    x = default \/ quorum_num rl <= quorum_den rl * (Vm x default * Vm x default).

  (* A.5.3: "Any (non-default) option which does not defeat the default option
     by its required majority ratio is dropped from consideration."
     A.5.3.2 (since version 1.6): "An option A defeats the default option D by
     a majority ratio N, if V(A,D) is greater or equal to N * V(D,A) and V(A,D)
     is strictly greater than V(D,A)." Versions 1.0 to 1.5 (strict_majority):
     "if V(A,D) is strictly greater than N * V(D,A)".
     A.5.3.3: "If a supermajority of S:1 is required for A, its majority ratio
     is S; otherwise, its majority ratio is 1." (ratio rl x) *)
  Definition Majority (x : cand) : Prop :=
    x = default \/
    (if strict_majority rl then ratio rl x * Vm default x < Vm x default
     else ratio rl x * Vm default x <= Vm x default /\ Vm default x < Vm x default).

  Lemma remaining_in x : In x remaining <-> Quorum x /\ Majority x.
  Proof.
    unfold remaining, Quorum, Majority, passes_quorum, passes_majority.
    rewrite filter_In, andb_true_iff, !orb_true_iff, ceq_true.
    destruct (strict_majority rl); rewrite ?andb_true_iff, ?Nat.leb_le, ?Nat.ltb_lt;
      split; [intros [_ H]; exact H | intros H; split; [apply cand_fin | exact H]
             | intros [_ H]; exact H | intros H; split; [apply cand_fin | exact H]].
  Qed.

  Lemma passes_quorum_iff x : passes_quorum x = true <-> Quorum x.
  Proof. unfold passes_quorum, Quorum. rewrite orb_true_iff, ceq_true, Nat.leb_le. reflexivity. Qed.

  Lemma passes_majority_iff x : passes_majority x = true <-> Majority x.
  Proof.
    unfold passes_majority, Majority. rewrite orb_true_iff, ceq_true.
    destruct (strict_majority rl); rewrite ?andb_true_iff, ?Nat.leb_le, ?Nat.ltb_lt; reflexivity.
  Qed.

  Lemma default_remaining : In default remaining.
  Proof.
    unfold remaining. apply filter_In. split; [apply cand_fin | ].
    unfold passes_quorum, passes_majority. rewrite ceq_refl. reflexivity.
  Qed.

  (* the initial list of pairwise defeats among the remaining options.
     A.5.4: "From the list of undropped options, we generate a list of
     pairwise defeats." A.5.4.1: "An option A defeats an option B, if V(A,B)
     is strictly greater than V(B,A)." *)
  Definition initial_defeats : list defeat :=
    flat_map (fun a => map (fun b => (a, b))
                           (filter (fun b => Vm b a <? Vm a b) remaining))
             remaining.

  Lemma initial_defeats_in a b :
    In (a, b) initial_defeats <->
    In a remaining /\ In b remaining /\ Vm b a < Vm a b.
  Proof.
    unfold initial_defeats. rewrite in_flat_map. split.
    - intros [a' [Ha Hin]]. apply in_map_iff in Hin. destruct Hin as [b' [E Hb]].
      inversion E; subst. apply filter_In in Hb. destruct Hb as [Hb Hlt].
      apply Nat.ltb_lt in Hlt. auto.
    - intros [Ha [Hb Hlt]]. exists a. split; auto. apply in_map_iff. exists b.
      split; auto. apply filter_In. split; auto. apply Nat.ltb_lt. auto.
  Qed.

End Debian.

(* ========================================================================= *)
(*  The whole procedure (A.5.1 - A.5.8), from ballots to winners            *)
(* ========================================================================= *)


(* ========================================================================= *)
(*  The whole procedure (A.5.1 - A.5.8), from ballots to winners            *)
(* ========================================================================= *)

Section Procedure.

  Variable cand : Type.
  Variable cand_all : list cand.
  Hypothesis cand_fin : forall c, In c cand_all.
  Hypothesis cand_nodup : NoDup cand_all.
  Hypothesis dec_cand : forall x y : cand, {x = y} + {x <> y}.
  Variable default : cand.
  Variable rl : rules cand.

  (* the report of a count: everything Debian publishes about an outcome *)
  Record report := {
    rep_remaining : list cand;          (* options surviving quorum and majority *)
    rep_defeats   : list (defeat cand); (* initial pairwise defeats among them *)
    rep_winners   : list cand           (* the Schwartz set after dropping *)
  }.

  Definition count (Vm : cand -> cand -> nat) : report :=
    let rem := remaining cand cand_all dec_cand default Vm rl in
    let defs := initial_defeats cand cand_all dec_cand default Vm rl in
    {| rep_remaining := rem;
       rep_defeats := defs;
       rep_winners := cssd cand cand_all dec_cand Vm (length defs) rem defs |}.

  (* counting a list of ballots: tabulate V once, then count *)
  Definition count_ballots (bs : list (ballot cand)) : report := count (V cand bs).

  (* the winners of a count satisfy the specification of A.5.5-A.5.8 *)
  Theorem count_spec Vm :
    cssd_spec cand cand_all dec_cand Vm
              (rep_remaining (count Vm)) (rep_defeats (count Vm)) (rep_winners (count Vm)).
  Proof. unfold count. simpl. apply cssd_correct. auto. Qed.

  (* and are uniquely determined by it *)
  Theorem count_unique Vm W :
    cssd_spec cand cand_all dec_cand Vm
              (rep_remaining (count Vm)) (rep_defeats (count Vm)) W ->
    W = rep_winners (count Vm).
  Proof.
    intros H. apply (cssd_spec_functional cand cand_all dec_cand Vm _ _ _ _ H (count_spec Vm)).
  Qed.

  (* the default option always survives quorum and majority *)
  Theorem count_default Vm : In default (rep_remaining (count Vm)).
  Proof. unfold count. simpl. apply default_remaining; auto. Qed.

  (* there is always at least one winner *)
  Theorem count_nonempty Vm : rep_winners (count Vm) <> [].
  Proof.
    apply (cssd_nonempty cand cand_all cand_fin dec_cand Vm
             (rep_remaining (count Vm)) (rep_defeats (count Vm)) (rep_winners (count Vm))).
    - intros H. pose proof (count_default Vm) as H0. rewrite H in H0. inversion H0.
    - apply count_spec.
  Qed.

  (* every winner is a remaining option *)
  Theorem count_winners_remaining Vm w :
    In w (rep_winners (count Vm)) -> In w (rep_remaining (count Vm)).
  Proof.
    intros H.
    destruct (cssd_winners_schwartz cand cand_all dec_cand Vm
                (rep_remaining (count Vm)) (rep_defeats (count Vm)) (rep_winners (count Vm))
                (count_spec Vm))
      as [defs' [Heq _]].
    rewrite Heq in H. apply schwartz_in in H; auto. destruct H. auto.
  Qed.

  (* a Condorcet winner among the remaining options is the unique winner *)
  Theorem count_condorcet Vm a :
    In a (rep_remaining (count Vm)) ->
    (forall b, In b (rep_remaining (count Vm)) -> b <> a -> Vm b a < Vm a b) ->
    rep_winners (count Vm) = [a].
  Proof.
    intros Ha Hbeats. symmetry.
    apply count_unique.
    apply (condorcet_winner cand cand_all cand_fin dec_cand Vm).
    - unfold count. simpl. unfold remaining. apply NoDup_filter. auto.
    - auto.
    - intros b Hb Hne. apply initial_defeats_in. repeat split; auto.
    - intros x Hx. apply initial_defeats_in in Hx. destruct Hx as [Hx [_ Hlt]].
      destruct (dec_cand x a) as [-> | Hne]; [lia | ].
      specialize (Hbeats x Hx Hne). lia.
  Qed.

  (* ----------------------------------------------------------------------- *)
  (*  The whole of Appendix A.5 as a specification on sets                  *)
  (* ----------------------------------------------------------------------- *)

  (* the options that survive steps 2 and 3 (A.5.2, A.5.3) *)
  Definition Remaining Vm (x : cand) : Prop :=
    Quorum cand default Vm rl x /\ Majority cand default Vm rl x.

  (* the defeats of step 4. A.5.4: "From the list of undropped options, we
     generate a list of pairwise defeats." A.5.4.1: "An option A defeats an
     option B, if V(A,B) is strictly greater than V(B,A)." *)
  Definition Defeats0 Vm (p : defeat cand) : Prop :=
    Remaining Vm (fst p) /\ Remaining Vm (snd p) /\ Vm (snd p) (fst p) < Vm (fst p) (snd p).

  (* W is the set of winners of a vote with pairwise matrix Vm, as defined by
     Appendix A.5: no list, enumeration of the options, or fuel appears *)
  Definition debian_outcome Vm (W : cand -> Prop) : Prop :=
    SSD cand Vm (Remaining Vm) (Defeats0 Vm) W.

  (* the counter computes an outcome ... *)
  Theorem count_correct Vm : debian_outcome Vm (fun w => In w (rep_winners (count Vm))).
  Proof.
    unfold debian_outcome.
    pose proof (cssd_SSD cand cand_all cand_fin dec_cand Vm _ _ _ (count_spec Vm)) as H.
    unfold count in H |- *. simpl in H |- *.
    apply (SSD_ext cand Vm _ _ _ _ (fun x => remaining_in cand cand_all cand_fin dec_cand default Vm rl x) H).
    - intros [a b]. cbn beta. etransitivity; [apply initial_defeats_in | ].
      unfold Defeats0, Remaining. simpl. rewrite !remaining_in; auto. reflexivity.
    - intros a. reflexivity.
  Qed.

  (* ... and there is only one *)
  Theorem debian_outcome_unique Vm W W' :
    debian_outcome Vm W -> debian_outcome Vm W' -> forall a, W a <-> W' a.
  Proof.
    intros H H'. apply (SSD_functional cand Vm _ _ _ _ (fun x => iff_refl _) H _ _ (fun p => iff_refl _) H').
  Qed.

  Corollary count_complete Vm W :
    debian_outcome Vm W -> forall a, W a <-> In a (rep_winners (count Vm)).
  Proof. intros H. apply (debian_outcome_unique Vm); [exact H | apply count_correct]. Qed.

  (* ----------------------------------------------------------------------- *)
  (*  Further properties                                                     *)
  (* ----------------------------------------------------------------------- *)

  (* sequential dropping only ever elects options of the initial Schwartz set *)
  Theorem count_winners_in_schwartz Vm w :
    In w (rep_winners (count Vm)) ->
    In w (schwartz cand cand_all dec_cand (rep_remaining (count Vm)) (rep_defeats (count Vm))).
  Proof.
    intros H. apply (cssd_winners_in_schwartz cand cand_all cand_fin dec_cand Vm _ _ (rep_winners (count Vm)));
      [ | apply count_spec | exact H].
    intros a b Hab. unfold count in Hab |- *. simpl in Hab |- *. apply initial_defeats_in in Hab. tauto.
  Qed.

  (* a Condorcet loser among the remaining options never wins, unless it is
     the only remaining option *)
  Theorem count_condorcet_loser Vm l :
    In l (rep_remaining (count Vm)) ->
    (exists b, In b (rep_remaining (count Vm)) /\ b <> l) ->
    (forall b, In b (rep_remaining (count Vm)) -> b <> l -> Vm l b < Vm b l) ->
    ~ In l (rep_winners (count Vm)).
  Proof.
    intros Hl [b [Hb Hbl]] Hlose Hw.
    apply count_winners_in_schwartz in Hw. apply schwartz_in in Hw; auto. destruct Hw as [_ Hw].
    destruct (Hw b Hb) as [Hlb | Hnbl].
    - destruct (TDef_first cand _ _ _ Hlb) as [y Hy].
      unfold count in Hy, Hl, Hlose, Hb. simpl in Hy, Hl, Hlose, Hb.
      apply initial_defeats_in in Hy. destruct Hy as [_ [Hy Hlt]].
      destruct (dec_cand y l) as [-> | Hyl]; [lia | ]. specialize (Hlose y Hy Hyl). lia.
    - apply Hnbl. apply tdef_direct. unfold count in Hb, Hl, Hlose |- *. simpl in Hb, Hl, Hlose |- *.
      apply initial_defeats_in. repeat split; auto.
  Qed.

End Procedure.

(* the winners do not depend on the order in which the options are listed *)
Theorem count_order_independent (cand : Type) (l1 l2 : list cand)
  (fin1 : forall c, In c l1) (fin2 : forall c, In c l2)
  (dec_cand : forall x y : cand, {x = y} + {x <> y}) default rl Vm a :
  In a (rep_winners cand (count cand l1 dec_cand default rl Vm)) <->
  In a (rep_winners cand (count cand l2 dec_cand default rl Vm)).
Proof.
  pose proof (count_correct cand l1 fin1 dec_cand default rl Vm) as H1.
  pose proof (count_correct cand l2 fin2 dec_cand default rl Vm) as H2.
  exact (debian_outcome_unique cand default rl Vm _ _ H1 H2 a).
Qed.

(* ========================================================================= *)
(*  Certificates                                                            *)
(* ========================================================================= *)

(* A certificate lets anyone confirm a published outcome with a small checker
   that never computes a transitive closure. For every round of step 7 it
   names the Schwartz set S and gives, as witnesses,
     - for each remaining option x outside S, a path of defeats from S to x;
     - for each member y of S, a root r and paths of defeats r..y and y..r.
   The checker verifies these paths, that no defeat enters S from outside, and
   that every defeat inside S joins two members with the same root. It then
   performs the round itself (dropping the weakest defeats inside S) and moves
   to the next round. An accepted certificate determines the outcome of A.5:
   check_certificate_sound. Certificates are produced by an untrusted program. *)

Section Certificate.

  Variable cand : Type.
  Variable cand_all : list cand.
  Hypothesis cand_fin : forall c, In c cand_all.
  Hypothesis dec_cand : forall x y : cand, {x = y} + {x <> y}.
  Variable default : cand.
  Variable rl : rules cand.
  Variable Vm : cand -> cand -> nat.

  Definition dinb (p : defeat cand) (l : list (defeat cand)) : bool := existsb (deq cand dec_cand p) l.

  Lemma dinb_true p l : dinb p l = true <-> In p l.
  Proof.
    unfold dinb. rewrite existsb_exists. split.
    - intros [q [Hq E]]. apply deq_true in E. subst. auto.
    - intros H. exists p. split; auto. apply deq_true. auto.
  Qed.

  Fixpoint lookup {B : Type} (x : cand) (l : list (cand * B)) : option B :=
    match l with
    | [] => None
    | (y, b) :: l' => if ceq cand dec_cand x y then Some b else lookup x l'
    end.

  (* a path x0 x1 ... xk of options in which each defeats the next *)
  Fixpoint path_ok (defs : list (defeat cand)) (l : list cand) : bool :=
    match l with
    | x :: (y :: _) as rest => dinb (x, y) defs && path_ok defs rest
    | _ => true
    end.

  (* a path from a to b *)
  Definition path_from_to (defs : list (defeat cand)) (l : list cand) (a b : cand) : bool :=
    match l with
    | [] => false
    | x :: _ => ceq cand dec_cand x a && ceq cand dec_cand (last l x) b && path_ok defs l
    end.

  Lemma last_cons_default {A : Type} (l : list A) (x d : A) : l <> [] -> last l x = last l d.
  Proof.
    induction l as [| y [| z l'] IH]; intros H; [congruence | reflexivity | ].
    simpl. simpl in IH. apply IH. discriminate.
  Qed.

  Lemma path_ok_reach defs x l :
    path_ok defs (x :: l) = true -> l = [] \/ TDef cand defs x (last l x).
  Proof.
    revert x. induction l as [| y l' IH]; intros x H; [left; auto | right].
    simpl in H. apply andb_true_iff in H. destruct H as [Hxy H].
    apply dinb_true in Hxy. destruct l' as [| z l''].
    - simpl. apply tdef_direct. auto.
    - destruct (IH y H) as [Hn | Hy]; [discriminate | ].
      apply tdef_via with y; auto.
      change (last (y :: z :: l'') x) with (last (z :: l'') x).
      rewrite (last_cons_default (z :: l'') x y); auto. discriminate.
  Qed.

  (* a path from a to b shows that a = b or a transitively defeats b *)
  Lemma path_from_to_reach defs l a b :
    path_from_to defs l a b = true -> a = b \/ TDef cand defs a b.
  Proof.
    unfold path_from_to. destruct l as [| x l]; [discriminate | ].
    rewrite !andb_true_iff, !(ceq_true cand dec_cand). intros [[-> Hb] Hp].
    destruct (path_ok_reach defs a l Hp) as [-> | H].
    - left. simpl in Hb. auto.
    - right. replace b with (last l a); auto. rewrite <- Hb.
      destruct l; reflexivity.
  Qed.

  Record scert := {
    sc_set : list cand;                                     (* S *)
    sc_out : list (cand * list cand);                       (* x outside S: path from S to x *)
    sc_in  : list (cand * (cand * (list cand * list cand))) (* y in S: root r, paths r..y, y..r *)
  }.

  Definition root (c : scert) (y : cand) : option cand :=
    option_map fst (lookup y (sc_in c)).

  Definition same_root (c : scert) (u v : cand) : bool :=
    match root c u, root c v with
    | Some r1, Some r2 => ceq cand dec_cand r1 r2
    | _, _ => false
    end.

  Definition check_scert (rem : list cand) (defs : list (defeat cand)) (c : scert) : bool :=
    let S := sc_set c in
    forallb (fun s => inb cand dec_cand s rem) S &&
    forallb (fun p => negb (inb cand dec_cand (snd p) S) || inb cand dec_cand (fst p) S) defs &&
    forallb (fun x => inb cand dec_cand x S ||
               match lookup x (sc_out c) with
               | Some (s :: l) => inb cand dec_cand s S && path_from_to defs (s :: l) s x
               | _ => false
               end) rem &&
    forallb (fun y => match lookup y (sc_in c) with
                      | Some (r, (p1, p2)) => path_from_to defs p1 r y && path_from_to defs p2 y r
                      | None => false
                      end) S &&
    forallb (fun p => negb (inb cand dec_cand (fst p) S && inb cand dec_cand (snd p) S) || same_root c (fst p) (snd p)) defs.

  Lemma lookup_some {B : Type} x (l : list (cand * B)) b : lookup x l = Some b -> In (x, b) l.
  Proof.
    induction l as [| [y b'] l IH]; simpl; [discriminate | ].
    destruct (ceq cand dec_cand x y) eqn:E; intros H; [inversion H; subst; apply (ceq_true cand dec_cand) in E; subst; left; auto | right; auto].
  Qed.

  Lemma TDef_into_set defs (S : list cand) x s :
    (forall p, In p defs -> In (snd p) S -> In (fst p) S) ->
    TDef cand defs x s -> In s S -> In x S.
  Proof.
    intros Hc H. induction H as [x s H | x b s H _ IH]; intros Hs.
    - apply (Hc (x, s) H Hs).
    - apply (Hc (x, b) H). apply IH. auto.
  Qed.

  Theorem check_scert_sound rem defs c :
    check_scert rem defs c = true ->
    forall a, In a (sc_set c) <-> In a (schwartz cand cand_all dec_cand rem defs).
  Proof.
    unfold check_scert. rewrite !andb_true_iff, !forallb_forall.
    intros [[[[Hrem Hclosed] Hout] Hin] Hroot] a.
    set (S := sc_set c) in *.
    assert (Hc : forall p, In p defs -> In (snd p) S -> In (fst p) S).
    { intros p Hp Hs. specialize (Hclosed p Hp). apply orb_true_iff in Hclosed.
      destruct Hclosed as [H | H]; [apply negb_true_iff in H; apply (inb_true cand dec_cand) in Hs; congruence | apply (inb_true cand dec_cand); auto]. }
    (* inside S, every transitive defeat cand joins members with the same root *)
    assert (Hsame : forall u v, TDef cand defs u v -> In v S -> In u S /\ same_root c u v = true \/ u = v).
    { intros u v H. induction H as [u v H | u w v H Hwv IH]; intros Hv.
      - left. assert (Hu : In u S) by (apply (Hc (u, v) H Hv)). split; auto.
        specialize (Hroot (u, v) H). simpl in Hroot. apply orb_true_iff in Hroot.
        destruct Hroot as [Hr | Hr]; auto. apply negb_true_iff in Hr.
        assert (inb cand dec_cand u S = true) by (apply (inb_true cand dec_cand); auto). assert (inb cand dec_cand v S = true) by (apply (inb_true cand dec_cand); auto).
        rewrite H0, H1 in Hr. discriminate.
      - destruct (IH Hv) as [[Hw Hwv'] | ->]; [left | left].
        + assert (Hu : In u S) by (apply (Hc (u, w) H Hw)). split; auto.
          specialize (Hroot (u, w) H). simpl in Hroot. apply orb_true_iff in Hroot.
          destruct Hroot as [Hr | Hr].
          * apply negb_true_iff in Hr. assert (inb cand dec_cand u S = true) by (apply (inb_true cand dec_cand); auto).
            assert (inb cand dec_cand w S = true) by (apply (inb_true cand dec_cand); auto). rewrite H0, H1 in Hr. discriminate.
          * unfold same_root in Hr, Hwv' |- *. destruct (root c u), (root c w), (root c v); try discriminate.
            apply (ceq_true cand dec_cand) in Hr. apply (ceq_true cand dec_cand) in Hwv'. subst. apply (ceq_refl cand dec_cand).
        + assert (Hu : In u S) by (apply (Hc (u, v) H Hv)). split; auto.
          specialize (Hroot (u, v) H). simpl in Hroot. apply orb_true_iff in Hroot.
          destruct Hroot as [Hr | Hr]; auto. apply negb_true_iff in Hr.
          assert (inb cand dec_cand u S = true) by (apply (inb_true cand dec_cand); auto). assert (inb cand dec_cand v S = true) by (apply (inb_true cand dec_cand); auto).
          rewrite H0, H1 in Hr. discriminate. }
    (* members of S reach and are reached from their root *)
    assert (Hr : forall y, In y S -> exists r, root c y = Some r /\
                 (r = y \/ TDef cand defs r y) /\ (y = r \/ TDef cand defs y r)).
    { intros y Hy. specialize (Hin y Hy). unfold root.
      destruct (lookup y (sc_in c)) as [[r [p1 p2]] |] eqn:E; [ | discriminate].
      apply andb_true_iff in Hin. destruct Hin as [H1 H2].
      exists r. split; [reflexivity | split; [apply path_from_to_reach with p1 | apply path_from_to_reach with p2]; auto]. }
    rewrite (schwartz_in cand cand_all cand_fin dec_cand). split.
    - intros Ha. split; [apply (inb_true cand dec_cand), Hrem, Ha | ]. intros b Hb.
      destruct (tdef cand cand_all dec_cand defs a b) eqn:Eab; [left; apply (tdef_iff cand cand_all cand_fin dec_cand); auto | right].
      intros Hba. destruct (Hsame b a Hba Ha) as [[HbS Hba'] | ->].
      + destruct (Hr a Ha) as [r [Ea [_ Har]]]. destruct (Hr b HbS) as [r' [Eb [Hrb _]]].
        unfold same_root in Hba'. rewrite Ea, Eb in Hba'. apply (ceq_true cand dec_cand) in Hba'. subst r'.
        assert (Hab : a = b \/ TDef cand defs a b).
        { destruct Har as [-> | Har]; destruct Hrb as [-> | Hrb]; auto; right; eauto using TDef_trans. }
        destruct Hab as [-> | Hab].
        * apply (tdef_iff cand cand_all cand_fin dec_cand) in Hba; auto. congruence.
        * apply (tdef_iff cand cand_all cand_fin dec_cand) in Hab; auto. congruence.
      + apply (tdef_iff cand cand_all cand_fin dec_cand) in Hba; auto. congruence.
    - intros [Har Ha]. destruct (inb cand dec_cand a S) eqn:E; [apply (inb_true cand dec_cand); auto | exfalso].
      specialize (Hout a Har). rewrite E in Hout. simpl in Hout.
      destruct (lookup a (sc_out c)) as [[| s l] |] eqn:El; try discriminate.
      apply andb_true_iff in Hout. destruct Hout as [Hs Hp]. apply (inb_true cand dec_cand) in Hs.
      destruct (path_from_to_reach defs (s :: l) s a Hp) as [-> | Hsa].
      + apply (inb_true cand dec_cand) in Hs. congruence.
      + assert (Hsr : In s rem) by (apply (inb_true cand dec_cand), Hrem, Hs).
        destruct (Ha s Hsr) as [Has | Hn]; [ | contradiction].
        assert (In a S) by (apply TDef_into_set with defs s; auto).
        apply (inb_true cand dec_cand) in H. congruence.
  Qed.

  (* the rounds of step 7, each with its Schwartz-set certificate *)
  Fixpoint check_rounds (rem : list cand) (defs : list (defeat cand)) (cs : list scert) : option (list cand) :=
    match cs with
    | [] => None
    | c :: cs' =>
      if check_scert rem defs c then
        let S := sc_set c in
        match filter (fun p => inb cand dec_cand (fst p) S && inb cand dec_cand (snd p) S) defs with
        | [] => Some S
        | inn => check_rounds rem (remove_all cand dec_cand (weakest cand Vm inn) defs) cs'
        end
      else None
    end.

  Lemma check_rounds_sound rem cs : forall defs W,
    check_rounds rem defs cs = Some W ->
    SSD cand Vm (fun x => In x rem) (fun p => In p defs) (fun a => In a W).
  Proof.
    induction cs as [| c cs IH]; intros defs W H; simpl in H; [discriminate | ].
    destruct (check_scert rem defs c) eqn:Ec; [ | discriminate].
    pose proof (check_scert_sound rem defs c Ec) as HS.
    (* the defeats inside S are the inner defeats *)
    assert (Hinn : forall p, In p (filter (fun p => inb cand dec_cand (fst p) (sc_set c) && inb cand dec_cand (snd p) (sc_set c)) defs) <->
                             In p (inner cand cand_all dec_cand rem defs)).
    { intros p. unfold inner. rewrite !filter_In, !andb_true_iff, !(inb_true cand dec_cand), !HS. reflexivity. }
    destruct (filter (fun p => inb cand dec_cand (fst p) (sc_set c) && inb cand dec_cand (snd p) (sc_set c)) defs) as [| q l] eqn:Ef.
    - inversion H; subst. apply ssd_done.
      + intros p Hp. apply (inner_Inner cand cand_all cand_fin dec_cand Vm) in Hp.
        apply Hinn in Hp. inversion Hp.
      + intros a. rewrite HS. apply schwartz_Schwartz; auto.
    - apply IH in H. apply ssd_step with (fun p => In p (remove_all cand dec_cand (weakest cand Vm (q :: l)) defs)); auto.
      + exists q. apply (inner_Inner cand cand_all cand_fin dec_cand Vm). apply Hinn. left. auto.
      + intros p. rewrite remove_all_in, <- (weakest_Weakest cand cand_all cand_fin dec_cand Vm), !weakest_in.
        split; intros [H1 H2]; split; auto; intros H3; apply H2; destruct H3 as [H3 H4]; split;
          [apply Hinn; auto | intros r Hr; apply H4, Hinn; auto | apply Hinn; auto | intros r Hr; apply H4, Hinn; auto].
  Qed.

  Definition check_certificate (cs : list scert) : option (list cand) :=
    check_rounds (remaining cand cand_all dec_cand default Vm rl)
                 (initial_defeats cand cand_all dec_cand default Vm rl) cs.

  (* an accepted certificate determines the outcome defined by Appendix A.5 *)
  Theorem check_certificate_sound cs W :
    check_certificate cs = Some W -> debian_outcome cand default rl Vm (fun a => In a W).
  Proof.
    intros H. apply check_rounds_sound in H. unfold debian_outcome.
    apply (SSD_ext cand Vm _ _ _ _ (fun x => remaining_in cand cand_all cand_fin dec_cand default Vm rl x) H).
    - intros [a b]. cbn beta. etransitivity; [apply initial_defeats_in | ].
      unfold Defeats0, Remaining. simpl. rewrite !remaining_in; auto. reflexivity.
    - intros a. reflexivity.
  Qed.

  (* and so agrees with the counter *)
  Corollary check_certificate_count cs W :
    check_certificate cs = Some W ->
    forall a, In a W <-> In a (rep_winners cand (count cand cand_all dec_cand default rl Vm)).
  Proof.
    intros H. apply (count_complete cand cand_all cand_fin dec_cand default rl Vm).
    apply check_certificate_sound with cs. auto.
  Qed.

End Certificate.

(* ========================================================================= *)
(*  Auditing a published result                                             *)
(* ========================================================================= *)

(* devotee's results file is a list of claims about one vote: the pairwise
   counts, which options reach the quorum and the majority, the defeats, the
   Schwartz set and the winners. Each claim is stated here with the
   definitions of the specification (holds), checked by a boolean function
   (audit), and the two are proved to agree in both directions
   (audit_correct): the checker accepts a claim exactly when it is true.
   Turning the lines of a results file into claims is done by an untrusted
   program; each verdict on a claim is verified. *)

Section Audit.

  Variable cand : Type.
  Variable cand_all : list cand.
  Hypothesis cand_fin : forall c, In c cand_all.
  Hypothesis dec_cand : forall x y : cand, {x = y} + {x <> y}.
  Variable default : cand.
  Variable rl : rules cand.
  Variable Vm : cand -> cand -> nat.

  Inductive claim :=
  | CMatrix (x y : cand) (v : nat)              (* V(x,y) = v *)
  | CQuorum (x : cand) (pass : bool)            (* x reaches / fails the quorum *)
  | CRatio (x : cand) (n : nat)                 (* the majority ratio of x is n *)
  | CMajority (x : cand) (pass : bool)          (* x passes / fails the majority *)
  | CDefeat (a b : cand)                        (* a defeats b among the remaining options *)
  | CDefeats (l : list (defeat cand))           (* l lists all the defeats *)
  | CSchwartz (l : list cand)                   (* l is the initial Schwartz set *)
  | CRoundSchwartz (k : nat) (l : list cand)    (* l is the Schwartz set in round k of step 7 *)
  | CWeakestIn (k : nat) (p : defeat cand)      (* p is one of the weakest defeats of round k *)
  | CWeakestAll (k : nat) (l : list (defeat cand))  (* l lists the weakest defeats of round k *)
  | CWinners (l : list cand).                   (* l is the set of winners *)

  (* the step of Appendix A.5 a claim is about *)
  Definition claim_step (c : claim) : nat :=
    match c with
    | CMatrix _ _ _ => 1 | CQuorum _ _ => 2 | CRatio _ _ => 3 | CMajority _ _ => 3
    | CDefeat _ _ => 4 | CDefeats _ => 4 | CSchwartz _ => 6 | CRoundSchwartz _ _ => 6
    | CWeakestIn _ _ => 7 | CWeakestAll _ _ => 7 | CWinners _ => 8
    end.

  (* the defeats left after k rounds of step 7 (once no defeat is left inside
     the Schwartz set, a round drops nothing) *)
  Fixpoint RoundDefs (k : nat) : defeat cand -> Prop :=
    match k with
    | O => Defeats0 cand default rl Vm
    | S k' => fun p => RoundDefs k' p /\
               ~ Weakest cand Vm (Remaining cand default rl Vm) (RoundDefs k') p
    end.

  (* what a claim says, in terms of the specification *)
  Definition holds (c : claim) : Prop :=
    match c with
    | CMatrix x y v => Vm x y = v
    | CQuorum x b => if b then Quorum cand default Vm rl x else ~ Quorum cand default Vm rl x
    | CRatio x n => ratio cand rl x = n
    | CMajority x b => if b then Majority cand default Vm rl x else ~ Majority cand default Vm rl x
    | CDefeat a b => Defeats0 cand default rl Vm (a, b)
    | CDefeats l => forall p, In p l <-> Defeats0 cand default rl Vm p
    | CSchwartz l => forall a, In a l <->
                       Schwartz cand (Remaining cand default rl Vm) (Defeats0 cand default rl Vm) a
    | CRoundSchwartz k l => forall a, In a l <->
                       Schwartz cand (Remaining cand default rl Vm) (RoundDefs k) a
    | CWeakestIn k p => Weakest cand Vm (Remaining cand default rl Vm) (RoundDefs k) p
    | CWeakestAll k l => forall p, In p l <->
                       Weakest cand Vm (Remaining cand default rl Vm) (RoundDefs k) p
    | CWinners l => forall W, debian_outcome cand default rl Vm W -> forall a, In a l <-> W a
    end.

  Definition rem0 := remaining cand cand_all dec_cand default Vm rl.
  Definition defs0 := initial_defeats cand cand_all dec_cand default Vm rl.

  (* the defeats after k rounds, as computed by the counter *)
  Fixpoint rdefs (k : nat) : list (defeat cand) :=
    match k with
    | O => defs0
    | S k' => drop_weakest cand cand_all dec_cand Vm rem0 (rdefs k')
    end.

  Definition schwartz_k k := schwartz cand cand_all dec_cand rem0 (rdefs k).
  Definition inner_k k := inner cand cand_all dec_cand rem0 (rdefs k).
  Definition weakest_k k := weakest cand Vm (inner_k k).
  Definition winners0 := rep_winners cand (count cand cand_all dec_cand default rl Vm).

  (* l and m have the same members *)
  Definition same_cands (l m : list cand) : bool :=
    forallb (fun a => inb cand dec_cand a m) l && forallb (fun a => inb cand dec_cand a l) m.
  Definition same_defeats (l m : list (defeat cand)) : bool :=
    forallb (fun p => dinb cand dec_cand p m) l && forallb (fun p => dinb cand dec_cand p l) m.

  Definition audit (c : claim) : bool :=
    match c with
    | CMatrix x y v => Vm x y =? v
    | CQuorum x b => Bool.eqb (passes_quorum cand dec_cand default Vm rl x) b
    | CRatio x n => ratio cand rl x =? n
    | CMajority x b => Bool.eqb (passes_majority cand dec_cand default Vm rl x) b
    | CDefeat a b => inb cand dec_cand a rem0 && inb cand dec_cand b rem0 && (Vm b a <? Vm a b)
    | CDefeats l => same_defeats l defs0
    | CSchwartz l => same_cands l (schwartz_k 0)
    | CRoundSchwartz k l => same_cands l (schwartz_k k)
    | CWeakestIn k p => dinb cand dec_cand p (weakest_k k)
    | CWeakestAll k l => same_defeats l (weakest_k k)
    | CWinners l => same_cands l winners0
    end.

  Lemma same_cands_iff l m : same_cands l m = true <-> forall a, In a l <-> In a m.
  Proof.
    unfold same_cands. rewrite andb_true_iff, !forallb_forall. split.
    - intros [H1 H2] a. split; intros H; [apply (inb_true cand dec_cand), H1 | apply (inb_true cand dec_cand), H2]; auto.
    - intros H. split; intros a Ha; apply (inb_true cand dec_cand), H; auto.
  Qed.

  Lemma same_defeats_iff l m : same_defeats l m = true <-> forall p, In p l <-> In p m.
  Proof.
    unfold same_defeats. rewrite andb_true_iff, !forallb_forall. split.
    - intros [H1 H2] p. split; intros H; [apply (dinb_true cand dec_cand), H1 | apply (dinb_true cand dec_cand), H2]; auto.
    - intros H. split; intros p Hp; apply (dinb_true cand dec_cand), H; auto.
  Qed.

  Lemma rem0_in x : In x rem0 <-> Remaining cand default rl Vm x.
  Proof. apply remaining_in; auto. Qed.

  Lemma defs0_in p : In p defs0 <-> Defeats0 cand default rl Vm p.
  Proof.
    destruct p as [a b]. unfold defs0. etransitivity; [apply initial_defeats_in | ].
    unfold Defeats0. simpl. rewrite <- !rem0_in. reflexivity.
  Qed.

  Lemma rdefs_in k p : In p (rdefs k) <-> RoundDefs k p.
  Proof.
    revert p. induction k as [| k IH]; intros p; simpl; [apply defs0_in | ].
    rewrite (drop_weakest_in cand cand_all cand_fin dec_cand Vm), IH.
    assert (HW : forall q, Weakest cand Vm (fun x => In x rem0) (fun q => In q (rdefs k)) q <->
                           Weakest cand Vm (Remaining cand default rl Vm) (RoundDefs k) q).
    { intros q. split; apply Weakest_ext; intros; rewrite ?rem0_in, ?IH; reflexivity. }
    split; intros [H1 H2]; split; auto; intros H3; apply H2;
      [apply (proj2 (HW p)) | apply (proj1 (HW p))]; exact H3.
  Qed.

  Lemma schwartz_k_in k a :
    In a (schwartz_k k) <-> Schwartz cand (Remaining cand default rl Vm) (RoundDefs k) a.
  Proof.
    unfold schwartz_k. rewrite (schwartz_Schwartz cand cand_all cand_fin dec_cand).
    split; apply Schwartz_ext; intros; rewrite ?rem0_in, ?rdefs_in; reflexivity.
  Qed.

  Lemma inner_k_in k p :
    In p (inner_k k) <-> Inner cand (Remaining cand default rl Vm) (RoundDefs k) p.
  Proof.
    unfold inner_k. rewrite (inner_Inner cand cand_all cand_fin dec_cand Vm).
    split; apply Inner_ext; intros; rewrite ?rem0_in, ?rdefs_in; reflexivity.
  Qed.

  Lemma weakest_k_in k p :
    In p (weakest_k k) <-> Weakest cand Vm (Remaining cand default rl Vm) (RoundDefs k) p.
  Proof.
    unfold weakest_k, inner_k. rewrite (weakest_Weakest cand cand_all cand_fin dec_cand Vm).
    split; apply Weakest_ext; intros; rewrite ?rem0_in, ?rdefs_in; reflexivity.
  Qed.

  Lemma winners0_in W a :
    debian_outcome cand default rl Vm W -> (In a winners0 <-> W a).
  Proof.
    intros HW. symmetry. apply (count_complete cand cand_all cand_fin dec_cand default rl Vm W HW).
  Qed.

  Lemma winners0_outcome : debian_outcome cand default rl Vm (fun a => In a winners0).
  Proof. apply (count_correct cand cand_all cand_fin dec_cand default rl Vm). Qed.

  (* the checker accepts a claim exactly when the claim is true *)
  Theorem audit_correct c : audit c = true <-> holds c.
  Proof.
    destruct c as [x y v | x b | x n | x b | a b | l | l | k l | k p | k l | l]; simpl.
    - apply Nat.eqb_eq.
    - destruct b; rewrite ?Bool.eqb_true_iff.
      + apply (passes_quorum_iff cand dec_cand).
      + rewrite <- (passes_quorum_iff cand dec_cand). split; [congruence | ].
        destruct (passes_quorum cand dec_cand default Vm rl x); tauto.
    - apply Nat.eqb_eq.
    - destruct b; rewrite ?Bool.eqb_true_iff.
      + apply (passes_majority_iff cand dec_cand).
      + rewrite <- (passes_majority_iff cand dec_cand). split; [congruence | ].
        destruct (passes_majority cand dec_cand default Vm rl x); tauto.
    - rewrite !andb_true_iff, !(inb_true cand dec_cand), Nat.ltb_lt, !rem0_in.
      unfold Defeats0. simpl. tauto.
    - rewrite same_defeats_iff. split; intros H p; rewrite H; [apply defs0_in | symmetry; apply defs0_in].
    - rewrite same_cands_iff. split; intros H a; rewrite H; [apply (schwartz_k_in 0) | symmetry; apply (schwartz_k_in 0)].
    - rewrite same_cands_iff. split; intros H a; rewrite H; [apply schwartz_k_in | symmetry; apply schwartz_k_in].
    - rewrite (dinb_true cand dec_cand). apply weakest_k_in.
    - rewrite same_defeats_iff. split; intros H q; rewrite H; [apply weakest_k_in | symmetry; apply weakest_k_in].
    - rewrite same_cands_iff. split.
      + intros H W HW a. rewrite H. apply winners0_in. auto.
      + intros H a. exact (H _ winners0_outcome a).
  Qed.

  (* -- explanations ------------------------------------------------------- *)

  (* Why a claim is false. Each piece of evidence states a fact about the
     vote (refutes) that contradicts the claim; explain finds such evidence
     for a false claim, and explain_sound proves that what it finds is right. *)
  Inductive evidence :=
  | EValue (v : nat)                   (* the true count, or the true majority ratio *)
  | ENumbers (for_ against : nat)      (* V(x,D) and V(D,x), which decide the other way *)
  | ENotRemaining (x : cand)           (* x does not survive steps 2 and 3 *)
  | ENotStronger (va vb : nat)         (* V(a,b) = va and V(b,a) = vb, with vb >= va *)
  | EMissing (x : cand)                (* x belongs to the set but is not listed *)
  | EExtra (x : cand)                  (* x is listed but does not belong to the set *)
  | EBeatenBy (x b : cand)             (* b transitively defeats x, and x does not
                                          transitively defeat b: x is not in the Schwartz set *)
  | EMissingDefeat (p : defeat cand)   (* p belongs to the set of defeats but is not listed *)
  | EExtraDefeat (p : defeat cand)     (* p is listed but does not belong *)
  | ENotInner (p : defeat cand)        (* p is not a defeat between two members of the Schwartz set *)
  | EWeaker (q : defeat cand).         (* q is a defeat inside the Schwartz set that is weaker *)

  Definition schwartz_refutes (D : defeat cand -> Prop) (l : list cand) (e : evidence) : Prop :=
    match e with
    | EMissing x => Schwartz cand (Remaining cand default rl Vm) D x /\ ~ In x l
    | ENotRemaining x => In x l /\ ~ Remaining cand default rl Vm x
    | EBeatenBy x b => In x l /\ Remaining cand default rl Vm b /\ TD cand D b x /\ ~ TD cand D x b
    | _ => False
    end.

  (* the fact that a piece of evidence states about a claim *)
  Definition refutes (c : claim) (e : evidence) : Prop :=
    match c, e with
    | CMatrix x y v, EValue w => Vm x y = w /\ w <> v
    | CQuorum x b, ENumbers f _ =>
        Vm x default = f /\ (if b then ~ Quorum cand default Vm rl x else Quorum cand default Vm rl x)
    | CRatio x n, EValue w => ratio cand rl x = w /\ w <> n
    | CMajority x b, ENumbers f g =>
        Vm x default = f /\ Vm default x = g /\
        (if b then ~ Majority cand default Vm rl x else Majority cand default Vm rl x)
    | CDefeat a b, ENotRemaining x => (x = a \/ x = b) /\ ~ Remaining cand default rl Vm x
    | CDefeat a b, ENotStronger va vb => Vm a b = va /\ Vm b a = vb /\ va <= vb
    | CDefeats l, EMissingDefeat p => Defeats0 cand default rl Vm p /\ ~ In p l
    | CDefeats l, EExtraDefeat p => In p l /\ ~ Defeats0 cand default rl Vm p
    | CSchwartz l, e => schwartz_refutes (Defeats0 cand default rl Vm) l e
    | CRoundSchwartz k l, e => schwartz_refutes (RoundDefs k) l e
    | CWeakestIn k p, ENotInner _ => ~ Inner cand (Remaining cand default rl Vm) (RoundDefs k) p
    | CWeakestIn k p, EWeaker q =>
        Inner cand (Remaining cand default rl Vm) (RoundDefs k) q /\ weaker cand Vm q p = true
    | CWeakestAll k l, EMissingDefeat p =>
        Weakest cand Vm (Remaining cand default rl Vm) (RoundDefs k) p /\ ~ In p l
    | CWeakestAll k l, EExtraDefeat p =>
        In p l /\ ~ Weakest cand Vm (Remaining cand default rl Vm) (RoundDefs k) p
    | CWinners l, EMissing x => (forall W, debian_outcome cand default rl Vm W -> W x) /\ ~ In x l
    | CWinners l, EExtra x => In x l /\ (forall W, debian_outcome cand default rl Vm W -> ~ W x)
    | _, _ => False
    end.

  Lemma schwartz_refutes_not D l e :
    schwartz_refutes D l e -> ~ (forall a, In a l <-> Schwartz cand (Remaining cand default rl Vm) D a).
  Proof.
    destruct e; simpl; intros H Hl; try contradiction.
    - destruct H as [H1 H2]. apply H2. apply Hl in H1. destruct H1 as [H1 _]. exact H1.
    - destruct H as [H1 H2]. apply H2, Hl, H1.
    - destruct H as [H1 [H2 [H3 H4]]]. apply Hl in H1. destruct H1 as [_ H1].
      destruct (H1 b H2) as [H5 | H5]; contradiction.
  Qed.

  (* evidence really contradicts the claim *)
  Theorem refutes_not_holds c e : refutes c e -> ~ holds c.
  Proof.
    destruct c as [x y v | x b | x n | x b | a b | l | l | k l | k p | k l | l]; simpl;
      try (apply schwartz_refutes_not); destruct e; simpl; try tauto.
    - intros [H1 H2] H. congruence.
    - destruct b; tauto.
    - intros [H1 H2] H. congruence.
    - destruct b; tauto.
    - intros [[-> | ->] H] [Ha [Hb _]]; contradiction.
    - intros [H1 [H2 H3]] [_ [_ H]]. simpl in H. lia.
    - intros [H1 H2] H. apply H2, H, H1.
    - intros [H1 H2] H. apply H2, H, H1.
    - intros H [H1 _]. contradiction.
    - intros [H1 H2] [_ H]. specialize (H _ H1). congruence.
    - intros [H1 H2] H. apply H2, H, H1.
    - intros [H1 H2] H. apply H2, H, H1.
    - intros [H1 H2] H. apply H2. apply (H _ winners0_outcome). apply H1, winners0_outcome.
    - intros [H1 H2] H. apply (H2 _ winners0_outcome). apply (H _ winners0_outcome). exact H1.
  Qed.

  (* the first member of l that is not in m *)
  Definition first_not_in (l m : list cand) : option cand :=
    find (fun a => negb (inb cand dec_cand a m)) l.
  Definition first_defeat_not_in (l m : list (defeat cand)) : option (defeat cand) :=
    find (fun p => negb (dinb cand dec_cand p m)) l.

  Definition explain_defeats (l truth : list (defeat cand)) : option evidence :=
    match first_defeat_not_in l truth with
    | Some p => Some (EExtraDefeat p)
    | None => match first_defeat_not_in truth l with
              | Some p => Some (EMissingDefeat p)
              | None => None
              end
    end.

  Definition explain_schwartz (k : nat) (l : list cand) : option evidence :=
    match first_not_in l (schwartz_k k) with
    | Some x =>
        if inb cand dec_cand x rem0 then
          match find (fun b => tdef cand cand_all dec_cand (rdefs k) b x &&
                               negb (tdef cand cand_all dec_cand (rdefs k) x b)) rem0 with
          | Some b => Some (EBeatenBy x b)
          | None => None
          end
        else Some (ENotRemaining x)
    | None => match first_not_in (schwartz_k k) l with
              | Some x => Some (EMissing x)
              | None => None
              end
    end.

  Definition explain (c : claim) : option evidence :=
    match c with
    | CMatrix x y v => if Vm x y =? v then None else Some (EValue (Vm x y))
    | CQuorum x b =>
        if Bool.eqb (passes_quorum cand dec_cand default Vm rl x) b then None
        else Some (ENumbers (Vm x default) (Vm default x))
    | CRatio x n => if ratio cand rl x =? n then None else Some (EValue (ratio cand rl x))
    | CMajority x b =>
        if Bool.eqb (passes_majority cand dec_cand default Vm rl x) b then None
        else Some (ENumbers (Vm x default) (Vm default x))
    | CDefeat a b =>
        if inb cand dec_cand a rem0 then
          if inb cand dec_cand b rem0 then
            if Vm b a <? Vm a b then None else Some (ENotStronger (Vm a b) (Vm b a))
          else Some (ENotRemaining b)
        else Some (ENotRemaining a)
    | CDefeats l => explain_defeats l defs0
    | CSchwartz l => explain_schwartz 0 l
    | CRoundSchwartz k l => explain_schwartz k l
    | CWeakestIn k p =>
        if dinb cand dec_cand p (inner_k k) then
          match find (fun q => weaker cand Vm q p) (inner_k k) with
          | Some q => Some (EWeaker q)
          | None => None
          end
        else Some (ENotInner p)
    | CWeakestAll k l => explain_defeats l (weakest_k k)
    | CWinners l =>
        match first_not_in l winners0 with
        | Some x => Some (EExtra x)
        | None => match first_not_in winners0 l with
                  | Some x => Some (EMissing x)
                  | None => None
                  end
        end
    end.

  Lemma first_not_in_some l m x :
    first_not_in l m = Some x -> In x l /\ ~ In x m.
  Proof.
    unfold first_not_in. intros H. apply find_some in H. destruct H as [H1 H2].
    split; auto. apply negb_true_iff in H2. intros H. apply (inb_true cand dec_cand) in H. congruence.
  Qed.

  Lemma first_defeat_not_in_some l m p :
    first_defeat_not_in l m = Some p -> In p l /\ ~ In p m.
  Proof.
    unfold first_defeat_not_in. intros H. apply find_some in H. destruct H as [H1 H2].
    split; auto. apply negb_true_iff in H2. intros H. apply (dinb_true cand dec_cand) in H. congruence.
  Qed.

  Lemma explain_defeats_sound l truth (P : defeat cand -> Prop) e :
    (forall p, In p truth <-> P p) -> explain_defeats l truth = Some e ->
    match e with
    | EExtraDefeat p => In p l /\ ~ P p
    | EMissingDefeat p => P p /\ ~ In p l
    | _ => False
    end.
  Proof.
    intros HP. unfold explain_defeats.
    destruct (first_defeat_not_in l truth) as [p |] eqn:E1.
    - intros H. inversion H; subst. apply first_defeat_not_in_some in E1.
      destruct E1 as [H1 H2]. split; auto. rewrite <- HP. auto.
    - destruct (first_defeat_not_in truth l) as [p |] eqn:E2; intros H; inversion H; subst.
      apply first_defeat_not_in_some in E2. destruct E2 as [H1 H2]. split; auto. apply HP. auto.
  Qed.

  Lemma explain_schwartz_sound k l e :
    explain_schwartz k l = Some e -> schwartz_refutes (RoundDefs k) l e.
  Proof.
    unfold explain_schwartz.
    destruct (first_not_in l (schwartz_k k)) as [x |] eqn:E1.
    - apply first_not_in_some in E1. destruct E1 as [Hx Hnx].
      destruct (inb cand dec_cand x rem0) eqn:Er.
      + destruct (find _ rem0) as [b |] eqn:Eb; intros H; inversion H; subst. simpl.
        apply find_some in Eb. destruct Eb as [Hb Hf]. apply andb_true_iff in Hf.
        destruct Hf as [Hbx Hxb]. apply negb_true_iff in Hxb.
        split; [auto | split; [apply rem0_in; auto | split]].
        * apply (TD_ext cand (fun p => In p (rdefs k))); [intros; apply rdefs_in | ].
          apply (TDef_TD cand), (tdef_iff cand cand_all cand_fin dec_cand). auto.
        * intros Hn. apply (TD_ext cand (RoundDefs k) (fun p => In p (rdefs k))) in Hn;
            [ | intros; symmetry; apply rdefs_in].
          apply (TDef_TD cand), (tdef_iff cand cand_all cand_fin dec_cand) in Hn. congruence.
      + intros H. inversion H; subst. simpl. split; auto. rewrite <- rem0_in.
        intros Hn. apply (inb_true cand dec_cand) in Hn. congruence.
    - destruct (first_not_in (schwartz_k k) l) as [x |] eqn:E2; intros H; inversion H; subst. simpl.
      apply first_not_in_some in E2. destruct E2 as [H1 H2]. split; auto. apply schwartz_k_in. auto.
  Qed.

  (* what explain finds really refutes the claim *)
  Theorem explain_sound c e : explain c = Some e -> refutes c e.
  Proof.
    destruct c as [x y v | x b | x n | x b | a b | l | l | k l | k p | k l | l]; simpl.
    - destruct (Vm x y =? v) eqn:E; intros H; inversion H; subst. simpl.
      split; auto. apply Nat.eqb_neq. auto.
    - destruct (Bool.eqb _ b) eqn:E; intros H; inversion H; subst. simpl. split; auto.
      destruct b, (passes_quorum cand dec_cand default Vm rl x) eqn:Q; simpl in E; try discriminate;
        rewrite <- (passes_quorum_iff cand dec_cand); congruence.
    - destruct (ratio cand rl x =? n) eqn:E; intros H; inversion H; subst. simpl.
      split; auto. apply Nat.eqb_neq. auto.
    - destruct (Bool.eqb _ b) eqn:E; intros H; inversion H; subst. simpl. split; [auto | split; auto].
      destruct b, (passes_majority cand dec_cand default Vm rl x) eqn:Q; simpl in E; try discriminate;
        rewrite <- (passes_majority_iff cand dec_cand); congruence.
    - destruct (inb cand dec_cand a rem0) eqn:Ea.
      + destruct (inb cand dec_cand b rem0) eqn:Eb.
        * destruct (Vm b a <? Vm a b) eqn:E; intros H; inversion H; subst. simpl.
          apply Nat.ltb_ge in E. auto.
        * intros H; inversion H; subst. simpl. split; [right; auto | ]. rewrite <- rem0_in.
          intros Hn. apply (inb_true cand dec_cand) in Hn. congruence.
      + intros H; inversion H; subst. simpl. split; [left; auto | ]. rewrite <- rem0_in.
        intros Hn. apply (inb_true cand dec_cand) in Hn. congruence.
    - intros H. pose proof (explain_defeats_sound l defs0 _ e defs0_in H) as He.
      destruct e; simpl; tauto.
    - intros H. exact (explain_schwartz_sound 0 l e H).
    - intros H. exact (explain_schwartz_sound k l e H).
    - destruct (dinb cand dec_cand p (inner_k k)) eqn:Ei.
      + destruct (find _ (inner_k k)) as [q |] eqn:Eq; intros H; inversion H; subst. simpl.
        apply find_some in Eq. destruct Eq as [Hq Hw]. split; auto. apply inner_k_in. auto.
      + intros H; inversion H; subst. simpl. rewrite <- inner_k_in.
        intros Hn. apply (dinb_true cand dec_cand) in Hn. congruence.
    - intros H. pose proof (explain_defeats_sound l (weakest_k k) _ e (weakest_k_in k) H) as He.
      destruct e; simpl; tauto.
    - destruct (first_not_in l winners0) as [x |] eqn:E1.
      + intros H; inversion H; subst. simpl. apply first_not_in_some in E1. destruct E1 as [H1 H2].
        split; auto. intros W HW Hx. apply H2. apply (winners0_in W x HW). auto.
      + destruct (first_not_in winners0 l) as [x |] eqn:E2; intros H; inversion H; subst. simpl.
        apply first_not_in_some in E2. destruct E2 as [H1 H2]. split; auto.
        intros W HW. apply (winners0_in W x HW). auto.
  Qed.

  (* a claim that explain refutes is false, and the audit rejects it *)
  Corollary explain_rejects c e : explain c = Some e -> audit c = false.
  Proof.
    intros H. destruct (audit c) eqn:E; auto. exfalso.
    apply (refutes_not_holds c e (explain_sound c e H)). apply audit_correct. auto.
  Qed.

End Audit.
