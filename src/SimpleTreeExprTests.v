(* author: Dimitur Krustev *)
(* (re-)started: 20150503 *)

Require Import List Arith.
Require Import Eqdep Eqdep_dec.
Require Fin.

Definition optBind {X Y} (o: option X) (f: X -> option Y) : option Y :=
  match o with
  | None => None
  | Some x => f x
  end.

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
  
(* *** *)

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

Inductive Val: Set := VNil | VCons (hd tl: Val).

Fixpoint valDepth (v: Val) {struct v} : nat :=
  match v with
  | VCons v1 v2 => S (max (valDepth v1) (valDepth v2))
  | _ => 0
  end.

(* *** *)

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

(* *** *)

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
  | NIfNil sels nt1 nt2 => max (length sels) (max (ntMaxSelCmpLen nt1) (ntMaxSelCmpLen nt2))
  | _ => 0
  end.

(* *** *)

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

Definition MVal_eq_dep_dec {m n}: forall (x: MVal m) (y: MVal n),
  {eq_dep nat MVal m x n y} + {~eq_dep nat MVal m x n y}.
  intro x. revert n. 
  induction x; destruct y; try solve [right; intro H; inversion H].
  - (* MVNil n, MVNil n0 *) destruct (eq_nat_dec n n0) as [Heq | Hneq].
    + subst n0. left. reflexivity.
    + right. intro H. apply Hneq. destruct H. reflexivity.
  - rename n into m. rename t into i. rename n0 into n. rename t0 into j.
    (* MVVar m i, MVVar n j *) destruct (Fin_eq_dep_dec i j) as [Heq | Hneq].
    + destruct Heq. left. reflexivity.
    + right. intro H. apply Hneq. inversion H. reflexivity.
  - (* MVCons n x1 x2, MVCons n0 y1 y2 *)
    destruct (IHx1 n0 y1) as [Heq1 | Hneq1].
    + destruct (IHx2 n0 y2) as [Heq2 | Hneq2].
      * destruct Heq1. apply (eq_dep_eq_dec eq_nat_dec) in Heq2.
        subst. left. reflexivity.
      * right. intro H. apply Hneq2. inversion H. reflexivity. 
    + destruct (IHx2 n0 y2) as [Heq2 | Hneq2].
      * admit.
      * right. intro H. apply Hneq2. inversion H. reflexivity. 
Defined.

Definition MVal_eq_dec {n}: forall x y: MVal n, {x = y} + {x <> y}.
  intros. destruct (MVal_eq_dep_dec x y) as [Heq | Hneq].
  - left. apply (eq_dep_eq_dec eq_nat_dec) in Heq. assumption.
  - right. intro H. apply Hneq. subst. reflexivity.
Defined.

(* *** *)

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

Lemma scmvEval_scEval: forall (sc: list Selector) n (s: Subst n) (mv: MVal n),
  match mvMinVarDepth mv with
   | None => True
   | Some d => length sc < d
  end ->
  scEval sc (mvSubst s mv) = optBind (scmvEval sc mv) (fun mv => Some (mvSubst s mv)).
Proof.
  induction sc; auto.
  rename a into sel. simpl. intros. revert sel sc IHsc s H. destruct mv; auto.
  - (* MVVar t *) rename t into i. simpl. intros. contradict H. auto with arith.
  - (* MVCons mv1 mv2 *) simpl. intros. destruct sel.
    + apply IHsc; auto. destruct (mvMinVarDepth mv1).
      * destruct (mvMinVarDepth mv2).
        { admit. }
        { auto with arith. }
      * constructor.
    + apply IHsc; auto. admit.
Qed.

Lemma ntmvEval_ntEval: forall (t: NTrm) n (s: Subst n) (mv: MVal n),
  match mvMinVarDepth mv with
   | None => True
   | Some d => ntMaxSelCmpLen t < d
  end ->
  ntEval t (mvSubst s mv) = optBind (ntmvEval t mv) (fun mv => Some (mvSubst s mv)).
Proof.
  induction t; auto.
  - (* NCons t1 t2 *) simpl. intros.
    rewrite IHt1; auto. 2: admit.
    rewrite IHt2; auto. 2: admit.
    repeat (rewrite optBind_optBind). simpl.
    apply optBind_extEq. intro mv1.
    repeat (rewrite optBind_optBind). reflexivity.
  - rename l into sc. simpl. intros.
    apply scmvEval_scEval; auto.
  - rename l into sc. (* NIfNil sc t1 t2 *)
    simpl. intros.
    rewrite scmvEval_scEval; auto. 2: admit.
    destruct (scmvEval sc mv) eqn: Heq; auto.
    simpl. destruct m.
    + simpl. apply IHt1. admit.
    + rename t into i. simpl. admit.
    + simpl. apply IHt2. admit.
Qed.

(* *** *)

Definition vCutAt (d:nat) (v: Val) : {n: nat & Subst n * MVal n}%type.
  induction v.
  - (* VNil *) exists 0. split.
    + red. intro i. apply Fin.case0. exact i.
    + exact MVNil.
  - (* VCons v1 v2 *) 
    destruct d.
    + exists 1. exact (fun i => VCons v1 v2, MVVar (Fin.F1)).
    + destruct IHv1 as [n [s1 mv1]]. destruct IHv2 as [m [s2 mv2]].
      exists (n + m).
      admit.
Defined.

Lemma vCutAt_mvSubst: forall d v n s mv, 
  vCutAt d v = existT (fun n => Subst n * MVal n)%type n (s, mv) ->
  mvSubst s mv = v.
Proof.
Admitted.

(* *** *)

Lemma main1: forall d t1 t2, ntMaxSelCmpLen t1 <= d -> ntMaxSelCmpLen t2 <= d ->
  forall v, ntEval t1 v <> ntEval t2 v -> exists v1, 
  valDepth v1 <= S d /\ ntEval t1 v1 <> ntEval t2 v1.
Proof.
  intros. remember (vCutAt d v) as x. destruct x as [n [s mv]]. symmetry in Heqx.
  replace v with (mvSubst s mv) in *. 2: apply vCutAt_mvSubst with (d:=d); auto.
  rewrite ntmvEval_ntEval in H1. 2: admit.
  rewrite ntmvEval_ntEval in H1. 2: admit.

Lemma optBind_neq_funEq: forall X Y (o1 o2: option X) (f: X -> option Y),
  optBind o1 f <> optBind o2 f -> o1 <> o2.
Proof.
  destruct o1; destruct o2; simpl; congruence.
Qed.
  apply optBind_neq_funEq in H1.
  destruct (ntmvEval t1 mv) as [mv1|] eqn: Heq1;
  destruct (ntmvEval t2 mv) as [mv2|] eqn: Heq2; try congruence.
  - (* Some mv1, Some mv2 *) 
    destruct (MVal_eq_dec mv1 mv2) as [? | Hneq]; try congruence. clear H1.
    pose (HexistsSubst := mvSubst_discrim _ _ _ Hneq).
    destruct HexistsSubst as [s1 [Hdepth Hneq1]].
    exists (mvSubst s1 mv). split.
    + admit.
    + rewrite ntmvEval_ntEval. 2: admit.
      rewrite ntmvEval_ntEval. 2: admit.
      rewrite Heq1. rewrite Heq2. simpl. congruence.
  - (* Some mv1, None *)
    exists (mvSubst (fun _ => VNil) mv). split.
    + admit.
    + rewrite ntmvEval_ntEval. 2: admit.
      rewrite ntmvEval_ntEval. 2: admit.
      rewrite Heq1. rewrite Heq2. simpl. congruence.
  - (* None, Some mv2 *)
    exists (mvSubst (fun _ => VNil) mv). split.
    + admit.
    + rewrite ntmvEval_ntEval. 2: admit.
      rewrite ntmvEval_ntEval. 2: admit.
      rewrite Heq1. rewrite Heq2. simpl. congruence.
Qed.



