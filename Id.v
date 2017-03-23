(** Borrowed from Pierce's "Software Foundations" *)

Require Import Arith Arith.EqNat.
Require Import Omega.

Inductive id : Type :=
  Id : nat -> id.

Reserved Notation "m <<= n" (at level 70, no associativity).
Reserved Notation "m >>  n" (at level 70, no associativity).
Reserved Notation "m <<  n" (at level 70, no associativity).

Inductive le_id : id -> id -> Prop :=
  le_conv : forall n m, n <= m -> (Id n) <<= (Id m)
where "n <<= m" := (le_id n m).

Inductive lt_id : id -> id -> Prop :=
  lt_conv : forall n m, n < m -> (Id n) << (Id m)
where "n << m" := (lt_id n m).

Inductive gt_id : id -> id -> Prop :=
  gt_conv : forall n m, n > m -> (Id n) >> (Id m)
where "n >> m" := (gt_id n m).

Notation "n <<= m" := (le_id n m).
Notation "n >>  m" := (gt_id n m).
Notation "n <<  m" := (lt_id n m).

Lemma lt_eq_lt_id_dec: forall (id1 id2 : id), {id1 << id2} + {id1 = id2} + {id2 << id1}.
Proof.
  intros [n1]. induction n1 as [| n1' IH].
  - intros [n2]. destruct n2 as [| n2'].
    + auto.
    + left. left. apply lt_conv. omega.
  - intros [n2]. destruct n2 as [| n2'].
    + right. apply lt_conv. omega.
    + destruct (IH (Id n2')) as [[Hl | He] | Hg].
      * left. left. inversion Hl. apply lt_conv. omega.
      * left. right. inversion He. auto.
      * right. inversion Hg. apply lt_conv. omega.
Qed.

Lemma gt_eq_gt_id_dec: forall (id1 id2 : id), {id1 >> id2} + {id1 = id2} + {id2 >> id1}.
Proof.
  intros id1 id2. remember (lt_eq_lt_id_dec id1 id2) as L.
  destruct L as [[Hl | He] | Hg].
  - right. inversion Hl. apply gt_conv. omega.
  - left. right. apply He.
  - left. left. inversion Hg. apply gt_conv. omega.
Qed.

Lemma le_gt_id_dec : forall id1 id2 : id, {id1 <<= id2} + {id1 >> id2}.
Proof.
  intros [n1] [n2]. remember (lt_eq_lt_id_dec (Id n1) (Id n2)) as L.
  destruct L as [[Hl | He] | Hg].
  - left. inversion Hl. apply le_conv. omega.
  - left. inversion He. apply le_conv. omega.
  - right. inversion Hg. apply gt_conv. omega.
Qed.

Lemma eq_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  induction n as [| n' IH].
  - destruct m.
    + left. reflexivity.
    + right. omega.
  - destruct m.
    + right. omega.
    + remember (IH m) as IHm. destruct IHm as [eqH | neqH].
      * left. omega.
      * right. omega.
Qed.

Lemma eq_id_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof.
  intros [n1] [n2]. destruct (eq_dec n1 n2) as [eqH | neqH].
  - left. apply f_equal. apply eqH.
  - right. intros eq. inversion eq as [eqH]. apply neqH. apply eqH.
Qed.

Lemma eq_id : forall (T:Type) x (p q:T), (if eq_id_dec x x then p else q) = p.
Proof.
  intros T x p q. destruct (eq_id_dec x x) as [He | Hn].
  - reflexivity.
  - contradiction.
Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> (if eq_id_dec x y then p else q) = q.
Proof.
  intros T x y p q H. destruct (eq_id_dec x y) as [He | Hn].
  - contradiction.
  - reflexivity.
Qed.

Lemma lt_gt_id_false : forall id1 id2 : id, id1 >> id2 -> id2 >> id1 -> False.
Proof.
  intros [n1] [n2]. intros H1. inversion H1. intros H3. inversion H3. omega.
Qed.

Lemma le_gt_id_false : forall id1 id2 : id, id2 <<= id1 -> id2 >> id1 -> False.
Proof.
  intros [n1] [n2]. intros H1. inversion H1. intros H3. inversion H3. omega.
Qed.

Lemma le_lt_eq_id_dec : forall id1 id2 : id, id1 <<= id2 -> {id1 = id2} + {id2 >> id1}.
Proof.
  intros [n1] [n2] H. remember (gt_eq_gt_id_dec (Id n1) (Id n2)) as L.
  destruct L as [[Hl | He] | Hg].
  - assert (contra: False).
    { apply le_gt_id_false with (id1 := Id n2) (id2 := Id n1).
      apply H. apply Hl. }
    inversion contra.
  - auto.
  - auto.
Qed.

Lemma neq_lt_gt_id_dec : forall id1 id2 : id, id1 <> id2 -> {id1 >> id2} + {id2 >> id1}.
Proof.
  intros id1 id2 H. remember (gt_eq_gt_id_dec id1 id2) as L.
  destruct L as [[Hl | He] | Hg].
  - auto.
  - remember (H He) as contra. inversion contra.
  - auto.
Qed.

Lemma eq_gt_id_false : forall id1 id2 : id, id1 = id2 -> id1 >> id2 -> False.
Proof.
    intros [n1] [n2]. intros H1. inversion H1. intros H3. inversion H3. omega.
Qed.
