(* author: Dimitur Krustev *)
(* (re-)started: 20150503 *)

(* Finite Test Sets for a Class of Simple Programs on Binary Trees *)

Require Import List Arith.
Require Import Eqdep Eqdep_dec.
Require Fin.

(* Some utility definitions/lemmas missing from Coq's stdlib: *)

Definition optBind {X Y} (o: option X) (f: X -> option Y) : option Y :=
  match o with
  | None => None
  | Some x => f x
  end.

Definition option_eq_dec {X} (X_eq_dec: forall x y: X, {x = y} + {x <> y}) : 
  forall x y: option X, {x = y} + {x <> y}.
  decide equality.
Defined.

Lemma optBind_optBind: forall A B C (f1: A -> option B) (f2: B -> option C) x,
  optBind (optBind x f1) f2 = optBind x (fun y => optBind (f1 y) f2).
Proof.
  destruct x; auto.
Qed.

Lemma optBind_extEq: forall X Y (f g: X -> option Y) x, 
  (forall x, f x = g x) -> optBind x f = optBind x g.
Proof.
  destruct x; auto. intros. simpl. auto.
Qed.

Lemma optBind_neq_funEq: forall X Y (o1 o2: option X) (f: X -> option Y),
  optBind o1 f <> optBind o2 f -> o1 <> o2.
Proof.
  destruct o1; destruct o2; simpl; congruence.
Qed.
  
(* *** *)

(*
Definition finTryCast {n} (i: Fin.t n) : forall m, option (Fin.t m).
  induction i.
  - destruct m.
    + exact None.
    + exact (Some Fin.F1).
  - destruct m.
    + exact None.
    + destruct (IHi m).
      * rename t into j. exact (Some (Fin.FS j)).
      * exact None.
Defined.
*)

Definition finSplitLR {n m} (i: Fin.t (n + m)) : Fin.t n + Fin.t m.
  revert m i. induction n.
  - simpl. intros. right. exact i.
  - simpl. intros. remember (S (n + m)) as snm. destruct i.
    + left. exact Fin.F1.
    + injection Heqsnm. intro Heq. subst n0. clear Heqsnm. destruct (IHn m i) as [j | j].
      * left. exact (Fin.FS j).
      * right. exact j.
Defined.

Lemma finSplitLR_FinL: forall n (i: Fin.t n) m, finSplitLR (Fin.L m i) = inl i.
Proof.
  induction i; auto.
  simpl. intros. unfold eq_rec_r, eq_rec, eq_sym. simpl.
  rewrite IHi. reflexivity.
Qed.

Lemma finSplitLR_FinR: forall m (i: Fin.t m) n, finSplitLR (Fin.R n i) = inr i.
Proof.
  intros.  revert m i. induction n; auto.
  simpl. intros. unfold eq_rec_r, eq_rec, eq_sym. simpl.
  rewrite IHn. reflexivity.
Qed.

Definition Fin_eq_dep_dec: forall {m n} (x: Fin.t m) (y: Fin.t n), 
  {eq_dep nat Fin.t m x n y} + {~eq_dep nat Fin.t m x n y}.
  intros m n x. revert n. 
  induction x as [m | m x1 IHx1];
    destruct y as [n | n y1];
    try solve [right; intro H; inversion H].
  (* F1, F1 *) destruct (eq_nat_dec m n) as [Heq | Hneq].
    (* m = n *) subst n. left. reflexivity.
    (* m <> n *) right. intro H. apply Hneq. inversion H. reflexivity.
  (* fs, fs *) destruct (IHx1 n y1) as [Heq | Hneq].
    (* left *) left. inversion Heq. reflexivity.
    (* right *) right. intro H. apply Hneq. inversion H. reflexivity.
Defined.

Definition Fin_eq_dec: forall {n} (f1 f2: Fin.t n), {f1 = f2} + {f1 <> f2}.
  intros. destruct (Fin_eq_dep_dec f1 f2) as [Heq | Hneq].
  (* left *) left. apply (eq_dep_eq_dec eq_nat_dec). assumption.
  (* right *) right. intro H. apply Hneq. rewrite H. reflexivity.
Defined.

(* *** *)
(* The value domain of unlabeled binary trees: *)

Inductive Val: Set := VNil | VCons (hd tl: Val).

Fixpoint valDepth (v: Val) {struct v} : nat :=
  match v with
  | VCons v1 v2 => S (max (valDepth v1) (valDepth v2))
  | _ => 0
  end.

Definition Val_eq_dec: forall x y: Val, {x = y} + {x <> y}.
  decide equality.
Defined.

(* *** *)
(* Normal form of simple programs on binary trees and its evaluation: *)

Inductive Selector: Set := HD | TL.

Fixpoint scEval (sc: list Selector) (v: Val) {struct sc} : option Val := 
  match sc with
  | nil => Some v
  | sel::sc => match v with
    | VNil => None
    | VCons vh vt => match sel with
      | HD => scEval sc vh
      | TL => scEval sc vt
      end
    end
  end.

Inductive NTrm: Set :=
  | NNil: NTrm 
  | NCons: NTrm -> NTrm -> NTrm 
  | NSelCmp: list Selector -> NTrm
  | NIfNil: list Selector -> NTrm -> NTrm -> NTrm.

Fixpoint ntEval (t: NTrm) (v: Val) {struct t} : option Val :=
  match t with
  | NNil => Some VNil
  | NCons t1 t2 => optBind (ntEval t1 v) (fun v1 =>
      optBind (ntEval t2 v) (fun v2 => Some (VCons v1 v2)))
  | NSelCmp sc => scEval sc v
  | NIfNil sc t1 t2 => match scEval sc v with
    | None => None
    | Some VNil => ntEval t1 v
    | Some (VCons _ _) => ntEval t2 v
    end
  end.

Fixpoint ntMaxSelCmpLen (nt: NTrm) {struct nt} : nat :=
  match nt with
  | NCons nt1 nt2 => max (ntMaxSelCmpLen nt1) (ntMaxSelCmpLen nt2)
  | NSelCmp sels => length sels
  | NIfNil sels nt1 nt2 => max (S (length sels)) (max (ntMaxSelCmpLen nt1) (ntMaxSelCmpLen nt2))
  | _ => 0
  end.

(* *** *)
(* Binary trees with holes (represented by variables): *)

Inductive MVal: nat -> Set :=
  | MVNil: forall n, MVal n
  | MVVar: forall n, Fin.t n -> MVal n
  | MVCons: forall n, MVal n -> MVal n -> MVal n.

Implicit Arguments MVNil [n].
Implicit Arguments MVVar [n].
Implicit Arguments MVCons [n].

Definition Subst (n: nat) := Fin.t n -> Val.

Fixpoint mvSubstFlipped {n: nat} (t: MVal n) {struct t} : Subst n -> Val :=
  match t with
  | MVNil _ => fun _ => VNil
  | MVVar _ i => fun s => s i
  | MVCons _ t1 t2 => fun s => VCons (mvSubstFlipped t1 s) (mvSubstFlipped t2 s)
  end.

Definition mvSubst {n: nat} (s: Subst n) (t: MVal n) := mvSubstFlipped t s.

Fixpoint mvDepth {n} (mv: MVal n) {struct mv} : nat :=
  match mv with
  | MVCons _ mv1 mv2 => S (max (mvDepth mv1) (mvDepth mv2))
  | _ => 0
  end.

Fixpoint mvMinVarDepth {n} (mv: MVal n) : option nat :=
  match mv with
  | MVNil _ => None
  | MVVar _ _ => Some 0
  | MVCons _ mv1 mv2 => 
    match mvMinVarDepth mv1, mvMinVarDepth mv2 with
    | None, None => None
    | Some d, None => Some (S d)
    | None, Some d => Some (S d)
    | Some d1, Some d2 => Some (S (min d1 d2))
    end
  end.

Definition mvCast {n} (m: nat) (mv: MVal n) : MVal (n + m).
  revert m. induction mv.
  - intro m. exact MVNil.
  - rename t into i. intro m. exact (MVVar (Fin.L m i)).
  - intro m. exact (MVCons (IHmv1 m) (IHmv2 m)).
Defined.

Definition mvShift {m} (n: nat) (mv: MVal m) : MVal (n + m).
  revert n. induction mv.
  - rename n into m. intro n. exact MVNil.
  - rename n into m. rename t into i. intro n. exact (MVVar (Fin.R n i)).
  - rename n into m. intro n. exact (MVCons (IHmv1 n) (IHmv2 n)).
Defined.

Definition MVal_eq_dep_dec {m n}: forall (x: MVal m) (y: MVal n),
  {eq_dep nat MVal m x n y} + {~eq_dep nat MVal m x n y}.
  intro x. revert n. 
  induction x; destruct y; try solve [right; intro H; inversion H].
  - (* MVNil n, MVNil n0 *) destruct (eq_nat_dec n n0) as [Heq | Hneq].
    + left. subst n0. reflexivity.
    + right. intro H. apply Hneq. destruct H. reflexivity.
  - rename n into m. rename t into i. rename n0 into n. rename t0 into j.
    (* MVVar m i, MVVar n j *) destruct (Fin_eq_dep_dec i j) as [Heq | Hneq].
    + left. destruct Heq. reflexivity.
    + right. intro H. apply Hneq. inversion H. reflexivity.
  - (* MVCons n x1 x2, MVCons n0 y1 y2 *)
    destruct (IHx1 n0 y1) as [Heq1 | Hneq1].
    + destruct (IHx2 n0 y2) as [Heq2 | Hneq2].
      * left. destruct Heq1. apply (eq_dep_eq_dec eq_nat_dec) in Heq2.
        subst. reflexivity.
      * right. intro H. apply Hneq2. inversion H. reflexivity. 
    + right. intro H. apply Hneq1. inversion H. subst.
      apply (inj_pair2_eq_dec _ eq_nat_dec) in H4. subst. reflexivity.
Defined.

(* Print Assumptions MVal_eq_dep_dec. *)

Definition MVal_eq_dec {n}: forall x y: MVal n, {x = y} + {x <> y}.
  intros. destruct (MVal_eq_dep_dec x y) as [Heq | Hneq].
  - left. apply (eq_dep_eq_dec eq_nat_dec) in Heq. assumption.
  - right. intro H. apply Hneq. subst. reflexivity.
Defined.

Lemma mvDepth_mvCast: forall n (mv: MVal n) m,
  mvDepth (mvCast m mv) = mvDepth mv.
Proof.
  induction mv; auto.
  simpl. intros. rewrite IHmv1. rewrite IHmv2. reflexivity.
Qed.

Lemma mvDepth_mvShift: forall m (mv: MVal m) n,
  mvDepth (mvShift n mv) = mvDepth mv.
Proof.
  induction mv; auto.
  simpl. intros. rewrite IHmv1. rewrite IHmv2. reflexivity.
Qed.

Lemma mvMinVarDepth_mvCast: forall n (mv: MVal n) m,
  mvMinVarDepth (mvCast m mv) = mvMinVarDepth mv.
Proof.
  induction mv; auto.
  simpl. intros. rewrite IHmv1. rewrite IHmv2. reflexivity.
Qed.

Lemma mvMinVarDepth_mvShift: forall m (mv: MVal m) n,
  mvMinVarDepth (mvShift n mv) = mvMinVarDepth mv.
Proof.
  induction mv; auto.
  simpl. intros. rewrite IHmv1. rewrite IHmv2. reflexivity.
Qed.

Lemma valDepth_mvSubst_le: forall n (mv: MVal n) s d,
  (forall i, valDepth (s i) <= d) -> valDepth (mvSubst s mv) <= d + mvDepth mv.
Proof.
  induction mv; auto with arith.
  - rename t into i.
    (* MVVar i *) simpl. intros. rewrite <- plus_n_O. auto.
  - (* MVCons mv1 mv2 *) simpl. intros.
    rewrite <- plus_n_Sm. apply le_n_S.
    apply NPeano.Nat.max_lub.
    + transitivity (d + mvDepth mv1); auto with arith.
    + transitivity (d + mvDepth mv2); auto with arith.
Qed.

(* *** *)
(* A key testing lemma for binary trees with holes: *)

Lemma mvSubst_discrim: forall n (mv1 mv2: MVal n), mv1 <> mv2 -> exists s, 
  (forall i, valDepth (s i) <= 1) /\ mvSubst s mv1 <> mvSubst s mv2.
Proof.
  induction mv1; destruct mv2; try congruence; auto.
  - rename t into i. 
    (* MVNil, MVVar i *) simpl. intros. 
    exists (fun j => if Fin_eq_dec i j then VCons VNil VNil else VNil).
    split.
    + intro j. destruct (Fin_eq_dec i j); auto.
    + destruct (Fin_eq_dec i i); congruence.
  - (* MVNil, MVCons mv2_1 mv2_2 *) simpl. intros.
    exists (fun j => VNil). split; try congruence; auto.
  - rename t into i.
    (* MVVar i, MVNil *) simpl. intros.
    exists (fun j => if Fin_eq_dec i j then VCons VNil VNil else VNil).
    split.
    + intro j. destruct (Fin_eq_dec i j); auto.
    + destruct (Fin_eq_dec i i); congruence.
  - rename t into i. rename t0 into j.
    (* MVVar i, MVVar j *) simpl. intros.
    exists (fun k => if Fin_eq_dec k i then VCons VNil VNil else VNil).
    split.
    + intro k. destruct (Fin_eq_dec k i); auto.
    + destruct (Fin_eq_dec i i); destruct (Fin_eq_dec j i); congruence.
  - rename t into i.
    (* MVVar i, MVCons mv2_1 mv2_2 *) simpl. intros.
    exists (fun j => if Fin_eq_dec i j then VNil else VCons VNil VNil).
    split.
    + intro j. destruct (Fin_eq_dec i j); auto.
    + destruct (Fin_eq_dec i i); congruence.
  - (* MVCons mv1_1 mv1_2, MVNil *) simpl. intros.
    exists (fun j => VNil). split; try congruence; auto.
  - rename t into i.
    (* MVCons mv1_1 mv1_2, MVVar i *) simpl. intros.
    exists (fun j => if Fin_eq_dec i j then VNil else VCons VNil VNil).
    split.
    + intro j. destruct (Fin_eq_dec i j); auto.
    + destruct (Fin_eq_dec i i); congruence.
  - (* MVCons mv1_1 mv1_2, MVCons mv2_1 mv2_2 *) simpl. intros.
    destruct (MVal_eq_dec mv1_1 mv2_1) as [Heq1 | Hneq1].
    + subst. destruct (MVal_eq_dec mv1_2 mv2_2) as [Heq2 | Hneq2]; try congruence.
      specialize (IHmv1_2 mv2_2 Hneq2). destruct IHmv1_2 as [s [Hdepth Hneq3]].
      exists s. split; auto.
      congruence.
    + specialize (IHmv1_1 mv2_1 Hneq1). destruct IHmv1_1 as [s [Hdepth Hneq2]].
      exists s. split; auto.
      congruence.
Qed.

(* *** *)
(* Normal-form evaluator extended to operate on trees with holes: *)

Fixpoint scmvEval (sc: list Selector) : forall {n}, MVal n -> option (MVal n) :=
  match sc with
  | nil => fun _ mv => Some mv
  | sel::sc => fun _ mv => match mv with
    | MVNil _ => None
    | MVVar _ _ => None
    | MVCons _ mv1 mv2 => match sel with
      | HD => scmvEval sc mv1
      | TL => scmvEval sc mv2
      end
    end
  end.

Fixpoint ntmvEval (t: NTrm) {struct t} : forall {n}, MVal n -> option (MVal n) :=
  match t with
  | NNil => fun _ _ => Some MVNil
  | NCons t1 t2 => fun _ mv => optBind (ntmvEval t1 mv) (fun mv1 =>
      optBind (ntmvEval t2 mv) (fun mv2 => Some (MVCons mv1 mv2)))
  | NSelCmp sc => fun _ mv => scmvEval sc mv
  | NIfNil sc t1 t2 => fun _ mv => match scmvEval sc mv with
    | None => None
    | Some (MVVar _ _) => None
    | Some (MVNil _) => ntmvEval t1 mv
    | Some (MVCons _ _ _) => ntmvEval t2 mv
    end
  end.

(* *** *)
(* Key lemmas about commuting (extended) evaluation and hole-filling
  when selector-composition length <= min hole depth: *)

Lemma scmvEval_scEval: forall (sc: list Selector) n (s: Subst n) (mv: MVal n),
  match mvMinVarDepth mv with
   | None => True
   | Some d => length sc <= d
  end ->
  scEval sc (mvSubst s mv) = optBind (scmvEval sc mv) (fun mv => Some (mvSubst s mv)).
Proof.
  induction sc; auto.
  rename a into sel. simpl. intros. revert sel sc IHsc s H. destruct mv; auto.
  - (* MVVar t *) rename t into i. simpl. intros. contradict H. auto with arith.
  - (* MVCons mv1 mv2 *) simpl. intros. destruct sel.
    + apply IHsc; auto. destruct (mvMinVarDepth mv1).
      * destruct (mvMinVarDepth mv2); eauto with arith. 
      * constructor.
    + apply IHsc; auto. destruct (mvMinVarDepth mv2); auto.
      destruct (mvMinVarDepth mv1); eauto with arith.
Qed.

Lemma scmvEval_SomeMVVar_mvMinVarDepth: forall sc n (mv: MVal n) i,
  scmvEval sc mv = Some (MVVar i) -> exists d, mvMinVarDepth mv = Some d /\ d <= length sc.
Proof.
  induction sc.
  - simpl. intros. inversion H. subst. clear H. simpl. exists 0. auto with arith.
  - rename a into sel. simpl. intros.
    destruct mv; try congruence. simpl. destruct sel.
    + specialize (IHsc _ _ _ H). destruct IHsc as [d [Hmvd Hle]].
      rewrite Hmvd. destruct (mvMinVarDepth mv2); eauto with arith.
    + specialize (IHsc _ _ _ H). destruct IHsc as [d [Hmvd Hle]].
      rewrite Hmvd. destruct (mvMinVarDepth mv1); eauto with arith. 
Qed.

Lemma ntmvEval_ntEval: forall (t: NTrm) n (s: Subst n) (mv: MVal n),
  match mvMinVarDepth mv with
   | None => True
   | Some d => ntMaxSelCmpLen t <= d
  end ->
  ntEval t (mvSubst s mv) = optBind (ntmvEval t mv) (fun mv => Some (mvSubst s mv)).
Proof.
  induction t; auto.
  - (* NCons t1 t2 *) simpl. intros.
    rewrite IHt1; auto. 2: destruct (mvMinVarDepth mv); eauto with arith.
    rewrite IHt2; auto. 2: destruct (mvMinVarDepth mv); eauto with arith.
    repeat (rewrite optBind_optBind). simpl.
    apply optBind_extEq. intro mv1.
    repeat (rewrite optBind_optBind). reflexivity.
  - rename l into sc. simpl. intros.
    apply scmvEval_scEval; auto.
  - rename l into sc.
    (* NIfNil sc t1 t2 *)
    simpl. intros.
    rewrite scmvEval_scEval; auto. 2: destruct (mvMinVarDepth mv); eauto with arith.
    destruct (scmvEval sc mv) eqn: Heq; auto.
    simpl. destruct m.
    + simpl. apply IHt1. destruct (mvMinVarDepth mv); auto.
      change (max (S (length sc)) (max (ntMaxSelCmpLen t1) (ntMaxSelCmpLen t2)) <= n0) in H.
      eauto with arith.
    + rename t into i. simpl.
      apply scmvEval_SomeMVVar_mvMinVarDepth in Heq. destruct Heq as [d [Hmvd Hle]].
      rewrite Hmvd in *. contradict Hle.
      eauto with arith.
    + simpl. apply IHt2. destruct (mvMinVarDepth mv); auto.
      change (max (S (length sc)) (max (ntMaxSelCmpLen t1) (ntMaxSelCmpLen t2)) <= n0) in H.
      eauto with arith.
Qed.

(* *** *)
(* Decomposing a tree - at a given depth - to a tree with holes and a substitution
  giving subtrees for holes: *)

Definition vCutAt (d:nat) (v: Val) : {n: nat & Subst n * MVal n}%type.
  revert d. induction v.
  - (* VNil *) intro d. exists 0. split.
    + red. intro i. apply Fin.case0. exact i.
    + exact MVNil.
  - (* VCons v1 v2 *) intro d.
    destruct d as [|d].
    + exists 1. exact (fun i => VCons v1 v2, MVVar (Fin.F1)).
    + destruct (IHv1 d) as [n [s1 mv1]]. destruct (IHv2 d) as [m [s2 mv2]].
      exists (n + m).
      split.
      { intro i. destruct (finSplitLR i) as [j | j].
        - exact (s1 j).
        - exact (s2 j). }
      { exact (MVCons (mvCast m mv1) (mvShift n mv2)). }
Defined.

Lemma mvSubst_finSplitLR_mvCast: forall n m s1 s2 mv,
  mvSubst (fun i : Fin.t (n + m) =>
   match finSplitLR i with
   | inl j => s1 j
   | inr j => s2 j
   end) (mvCast m mv) = mvSubst s1 mv.
Proof.
  intros. revert m s1 s2. induction mv; auto.
  - simpl. intros.
    rewrite finSplitLR_FinL. reflexivity.
  - simpl. intros. rewrite IHmv1. rewrite IHmv2. reflexivity.
Qed.

Lemma mvSubst_finSplitLR_mvShift: forall n m s1 s2 mv,
  mvSubst (fun i : Fin.t (n + m) =>
   match finSplitLR i with
   | inl j => s1 j
   | inr j => s2 j
   end) (mvShift n mv) = mvSubst s2 mv.
Proof.
  intros. revert n s1 s2. induction mv; auto.
  - simpl. intros.
    rewrite finSplitLR_FinR. reflexivity.
  - simpl. intros. rewrite IHmv1. rewrite IHmv2. reflexivity.
Qed.

(* Correctness of tree decomposition: *)

Lemma vCutAt_mvSubst: forall d v n s mv, 
  vCutAt d v = existT (fun n => Subst n * MVal n)%type n (s, mv) ->
  mvSubst s mv = v.
Proof.
  intros d v. revert d. induction v.
  - simpl. intros. rewrite eq_sigT_iff_eq_dep in H. inversion H.
    subst.
    apply (inj_pair2_eq_dec _ eq_nat_dec) in H3.
    apply (inj_pair2_eq_dec _ eq_nat_dec) in H4.
    subst. reflexivity.
  - simpl. destruct d as [|d].
    + intros. rewrite eq_sigT_iff_eq_dep in H. inversion H.
      subst.
      apply (inj_pair2_eq_dec _ eq_nat_dec) in H3.
      apply (inj_pair2_eq_dec _ eq_nat_dec) in H4.
      subst. reflexivity.
    + intros.
      destruct (vCutAt d v1) as [n' [s1 mv1]] eqn: Heq1.
      destruct (vCutAt d v2) as [m' [s2 mv2]] eqn: Heq2.
      rewrite eq_sigT_iff_eq_dep in H. inversion H. clear H.
      subst.
      apply (inj_pair2_eq_dec _ eq_nat_dec) in H3.
      apply (inj_pair2_eq_dec _ eq_nat_dec) in H4.
      subst.
      simpl. f_equal.
      * rewrite mvSubst_finSplitLR_mvCast. eauto. 
      * rewrite mvSubst_finSplitLR_mvShift. eauto. 
Qed.
      
Lemma mvDepth_vCutAt_le: forall d v n s mv,
  vCutAt d v = existT (fun n : nat => (Subst n * MVal n)%type) n (s, mv) ->
  mvDepth mv <= d.
Proof.
  intros d v. revert d. induction v.
  - simpl. intros.
    rewrite eq_sigT_iff_eq_dep in H. inversion H. auto with arith.
  - simpl. intros. destruct d.
    + rewrite eq_sigT_iff_eq_dep in H. inversion H. auto.
    + destruct (vCutAt d v1) as [n1 [s1 mv1]] eqn: Heq1.
      destruct (vCutAt d v2) as [n2 [s2 mv2]] eqn: Heq2.
      rewrite eq_sigT_iff_eq_dep in H. inversion H.
      simpl. apply le_n_S.

      rewrite mvDepth_mvCast. rewrite mvDepth_mvShift.
      specialize (IHv1 _ _ _ _ Heq1).
      specialize (IHv2 _ _ _ _ Heq2).
      apply NPeano.Nat.max_lub; auto.
Qed.

Lemma vCutAt_mvMinVarDepth: forall d v n s mv,
  vCutAt d v = existT (fun n : nat => (Subst n * MVal n)%type) n (s, mv) ->
  mvMinVarDepth mv = None \/ mvMinVarDepth mv = Some d.
Proof.
  intros d v. revert d. induction v.
  - simpl. intros.
    rewrite eq_sigT_iff_eq_dep in H. inversion H. auto.
  - simpl. intros. destruct d.
    + rewrite eq_sigT_iff_eq_dep in H. inversion H. auto.
    + destruct (vCutAt d v1) as [n1 [s1 mv1]] eqn: Heq1.
      destruct (vCutAt d v2) as [n2 [s2 mv2]] eqn: Heq2.
      rewrite eq_sigT_iff_eq_dep in H. inversion H. subst.
      apply (inj_pair2_eq_dec _ eq_nat_dec) in H3. subst. clear H2 H.
      simpl.
      specialize (IHv1 _ _ _ _ Heq1).
      specialize (IHv2 _ _ _ _ Heq2).
      rewrite mvMinVarDepth_mvCast. rewrite mvMinVarDepth_mvShift.
      destruct IHv1 as [IHv1 | IHv1]; rewrite IHv1;
      destruct IHv2 as [IHv2 | IHv2]; rewrite IHv2;
      auto with arith.
Qed.

(* *** *)
(* Main result about discriminating inequivalent programs by a finite test set: *)

Lemma NTrm_fixed_MaxSelCmpLen_testable_aux: 
  forall d t1 t2, ntMaxSelCmpLen t1 <= d -> ntMaxSelCmpLen t2 <= d ->
  forall v, ntEval t1 v <> ntEval t2 v -> exists v1, 
  valDepth v1 <= S d /\ ntEval t1 v1 <> ntEval t2 v1.
Proof.
  intros. remember (vCutAt d v) as x. destruct x as [n [s mv]]. symmetry in Heqx.
  replace v with (mvSubst s mv) in H1. 2: apply vCutAt_mvSubst with (d:=d); auto.
  rewrite ntmvEval_ntEval in H1. 
  Focus 2. 
    apply vCutAt_mvMinVarDepth in Heqx. 
    destruct Heqx as [Heq | Heq]; rewrite Heq; auto. 
  rewrite ntmvEval_ntEval in H1. 
  Focus 2. 
    apply vCutAt_mvMinVarDepth in Heqx. 
    destruct Heqx as [Heq | Heq]; rewrite Heq; auto. 
  apply optBind_neq_funEq in H1.
  destruct (ntmvEval t1 mv) as [mv1|] eqn: Heq1;
  destruct (ntmvEval t2 mv) as [mv2|] eqn: Heq2; try congruence.
  - (* Some mv1, Some mv2 *) 
    destruct (MVal_eq_dec mv1 mv2) as [? | Hneq]; try congruence. clear H1.
    pose (HexistsSubst := mvSubst_discrim _ _ _ Hneq).
    destruct HexistsSubst as [s1 [Hdepth Hneq1]].
    exists (mvSubst s1 mv). split.
    + apply mvDepth_vCutAt_le in Heqx.
      transitivity (1 + mvDepth mv); auto with arith.
      apply valDepth_mvSubst_le; auto.
    + rewrite ntmvEval_ntEval. 
      Focus 2. 
        apply vCutAt_mvMinVarDepth in Heqx. 
        destruct Heqx as [Heq | Heq]; rewrite Heq; auto. 
      rewrite ntmvEval_ntEval. 
      Focus 2. 
        apply vCutAt_mvMinVarDepth in Heqx. 
        destruct Heqx as [Heq | Heq]; rewrite Heq; auto. 
      rewrite Heq1. rewrite Heq2. simpl. congruence.
  - (* Some mv1, None *)
    exists (mvSubst (fun _ => VNil) mv). split.
    + apply mvDepth_vCutAt_le in Heqx.
      transitivity (1 + mvDepth mv); auto with arith.
      apply valDepth_mvSubst_le; auto.
    + rewrite ntmvEval_ntEval.
      Focus 2. 
        apply vCutAt_mvMinVarDepth in Heqx. 
        destruct Heqx as [Heq | Heq]; rewrite Heq; auto. 
      rewrite ntmvEval_ntEval.
      Focus 2. 
        apply vCutAt_mvMinVarDepth in Heqx. 
        destruct Heqx as [Heq | Heq]; rewrite Heq; auto. 
      rewrite Heq1. rewrite Heq2. simpl. congruence.
  - (* None, Some mv2 *)
    exists (mvSubst (fun _ => VNil) mv). split.
    + apply mvDepth_vCutAt_le in Heqx.
      transitivity (1 + mvDepth mv); auto with arith.
      apply valDepth_mvSubst_le; auto.
    + rewrite ntmvEval_ntEval.
      Focus 2. 
        apply vCutAt_mvMinVarDepth in Heqx. 
        destruct Heqx as [Heq | Heq]; rewrite Heq; auto. 
      rewrite ntmvEval_ntEval. 
      Focus 2. 
        apply vCutAt_mvMinVarDepth in Heqx. 
        destruct Heqx as [Heq | Heq]; rewrite Heq; auto. 
      rewrite Heq1. rewrite Heq2. simpl. congruence.
Qed.

Theorem NTrm_fixed_MaxSelCmpLen_testable: 
  forall d t1 t2, ntMaxSelCmpLen t1 <= d -> ntMaxSelCmpLen t2 <= d ->
  (forall v, valDepth v <= S d -> ntEval t1 v = ntEval t2 v) -> 
  forall v, ntEval t1 v = ntEval t2 v.
Proof.
  intros d t1 t2 HscLen1 HscLen2 HallTstEq v.
  destruct (option_eq_dec Val_eq_dec (ntEval t1 v) (ntEval t2 v)) as [Heq | Hneq]; auto.
  contradict HallTstEq. intro HallTstEq. 
  pose (H := NTrm_fixed_MaxSelCmpLen_testable_aux _ _ _ HscLen1 HscLen2 _ Hneq).
  destruct H as [v1 [Hdepth Hneq1]].
  specialize (HallTstEq _ Hdepth). congruence.
Qed.

(* Print Assumptions NTrm_fixed_MaxSelCmpLen_testable. *)

(* *** *)
(* Show that bound on test set depth is tight: *)

Definition replicate {X} n (x: X) := map (fun _ => x) (seq 0 n).

(* counterexample taken from some old essays from 20100722: 
Definition undiscrTerms (n: nat) : (NTrm * NTrm) :=
  let sels := replicate n HD in
  let sels1 := sels ++ (HD::nil) in
  let sels2 := sels ++ (TL::nil) in
  let nt1 := NIfNil sels1 NNil (NIfNil sels2 NNil (NSelCmp sels1)) in
  let nt2 := NIfNil sels1 NNil (NIfNil sels2 NNil (NSelCmp sels2)) in
  (nt1, nt2).
*)

Lemma undiscrTerms_exist: forall n, exists nt1, exists nt2,
  ntMaxSelCmpLen nt1 = S n /\ ntMaxSelCmpLen nt2 = S n /\
  (forall v, valDepth v <= S n -> ntEval nt1 v = ntEval nt2 v)
  /\ exists v, ntEval nt1 v <> ntEval nt2 v.
Proof.
  intros.
  exists (NSelCmp (replicate n HD ++ (HD::nil))).
  exists (NSelCmp (replicate n HD ++ (TL::nil))).
  simpl. 
  repeat (rewrite app_length). simpl. unfold replicate.
  rewrite map_length. rewrite seq_length. rewrite plus_comm.
  split; auto with arith.
  split; auto with arith.
  split.
  - induction n.
    + simpl. destruct v; auto. simpl. 
      destruct v1; destruct v2; auto;
        simpl; try solve [intro H; contradict H; auto with arith].
    + simpl. destruct v; auto. simpl. intro Hle.
      rewrite <- seq_shift. rewrite map_map. apply IHn. 
      apply le_S_n in Hle. eapply Max.max_lub_l. eassumption.
  - induction n.
    + simpl. exists (VCons VNil (VCons VNil VNil)). congruence.
    + simpl. rewrite <- seq_shift. rewrite map_map.
      destruct IHn as [v Hneq].
      exists (VCons v VNil). assumption.
Qed.

