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
  (*  Ballots and the pairwise matrix V (A.5.1, A.5.4)                      *)
  (* ----------------------------------------------------------------------- *)

  (* A ballot gives each option a rank; 0 means "not ranked"; 1 is the
     highest preference. Equal ranks are allowed. *)
  Definition ballot := cand -> nat.

  (* x is ranked above y on ballot b *)
  Definition above (b : ballot) (x y : cand) : bool :=
    match b x, b y with
    | 0, _ => false                   (* unranked is never above anything *)
    | S _, 0 => true                  (* ranked is above unranked *)
    | S rx, S ry => rx <? ry          (* smaller rank number = higher preference *)
    end.

  (* V(x,y): the number of voters who rank x above y *)
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

  (* A.5.5, as stated: A transitively defeats C if A defeats C, or A defeats
     some B that transitively defeats C. *)
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

  (* the Schwartz set of the current defeats, among the remaining options *)
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

  (* (A,X) is weaker than (B,Y): A.5.7 *)
  Definition weaker (p q : defeat) : bool :=
    let '(a, x) := p in let '(b, y) := q in
    (Vm a x <? Vm b y) || ((Vm a x =? Vm b y) && (Vm y b <? Vm x a)).

  (* the defeats between options of the Schwartz set *)
  Definition inner (rem : list cand) (defs : list defeat) : list defeat :=
    let S := schwartz rem defs in
    filter (fun p => inb (fst p) S && inb (snd p) S) defs.

  (* the weakest among a list of defeats: those with nothing weaker *)
  Definition weakest (l : list defeat) : list defeat :=
    filter (fun p => forallb (fun q => negb (weaker q p)) l) l.

  Definition remove_all (l : list defeat) (defs : list defeat) : list defeat :=
    filter (fun p => negb (existsb (deq p) l)) defs.

  (* one round of A.5.7: drop the weakest defeats within the Schwartz set *)
  Definition drop_weakest (rem : list cand) (defs : list defeat) : list defeat :=
    remove_all (weakest (inner rem defs)) defs.

  (* The specification of steps 5-8, as a relation between the current list
     of defeats and the resulting winners. *)
  Inductive cssd_spec (rem : list cand) : list defeat -> list cand -> Prop :=
  | cssd_done defs :
      inner rem defs = [] ->
      cssd_spec rem defs (schwartz rem defs)
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
  (*  Rules of a particular vote: quorum and majority ratios (A.5.2, A.5.3)  *)
  (*  (placed last so that no earlier lemma depends on them)                 *)
  (* ----------------------------------------------------------------------- *)


  (* The quorum R is a (possibly non-integral) number; we represent it as a
     fraction quorum_num / quorum_den. Debian computes Q = sqrt(#developers)/2
     and uses R = 3Q for general resolutions. The majority ratio of an option
     is S for a supermajority of S:1, and 1 otherwise. *)
  Record rules := {
    quorum_num : nat;
    quorum_den : nat;
    ratio : cand -> nat
  }.

  Variable rl : rules.
  Hypothesis quorum_den_pos : quorum_den rl > 0.

  (* A.5.2 *)
  Definition passes_quorum (x : cand) : bool :=
    ceq x default || (quorum_num rl <=? quorum_den rl * Vm x default).

  (* A.5.3 *)
  Definition passes_majority (x : cand) : bool :=
    ceq x default ||
    ((ratio rl x * Vm default x <=? Vm x default) && (Vm default x <? Vm x default)).

  (* the options that survive steps 2 and 3 *)
  Definition remaining : list cand :=
    filter (fun x => passes_quorum x && passes_majority x) cand_all.

  Lemma default_remaining : In default remaining.
  Proof.
    unfold remaining. apply filter_In. split; [apply cand_fin | ].
    unfold passes_quorum, passes_majority. rewrite ceq_refl. reflexivity.
  Qed.

  (* the initial list of pairwise defeats among the remaining options *)
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

End Procedure.
