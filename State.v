(** Based on Benjamin Pierce's "Software Foundations" *)

Require Import List.
Import ListNotations.
Require Import Omega.
Require Export Arith Arith.EqNat.
Require Export Id.

Section S.

  Variable A : Set.

  Definition state := list (id * A).

  Reserved Notation "st / x => y" (at level 0).

  Inductive st_binds : state -> id -> A -> Prop := 
    st_binds_hd : forall st id x, ((id, x) :: st) / id => x
  | st_binds_tl : forall st id x id' x', id <> id' -> st / id => x -> ((id', x')::st) / id => x
  where "st / x => y" := (st_binds st x y).

  Definition update (st : state) (id : id) (a : A) : state := (id, a) :: st.

  Notation "st [ x '<-' y ]" := (update st x y) (at level 0).

  Lemma state_deterministic: forall (st : state) (x : id) (n m : A),
    st / x => n -> st / x => m -> n = m.
  Proof.
    intros st x n m. induction st.
    - intros H. inversion H.
    - intros Hn. inversion Hn.
      + intros Hm. inversion Hm.
        * reflexivity.
        * contradiction.
      + intros Hm. inversion Hm.
        * symmetry in H5. contradiction.
        * auto.
  Qed.

  Lemma update_eq : forall (st : state) (x : id) (n : A),
    st [x <- n] / x => n.
  Proof.
    intros st x n. unfold update. apply st_binds_hd.
  Qed.

  Lemma update_neq : forall (st : state) (x2 x1 : id) (n m : A),
    x2 <> x1 -> st / x1 => m -> st [x2 <- n] / x1 => m.
  Proof.
    intros st x2 x1 n m nH uH. unfold update. apply st_binds_tl.
    - auto.
    - auto.
  Qed.

  Lemma update_shadow : forall (st : state) (x1 x2 : id) (n1 n2 m : A),
    st[x2 <- n1][x2 <- n2] / x1 => m -> st[x2 <- n2] / x1 => m.
  Proof.
    intros st x1 x2 n1 n2 m H. unfold update in H. inversion H.
    - apply st_binds_hd.
    - apply st_binds_tl.
      + auto.
      + inversion H6.
        * symmetry in H7. contradiction.
        * auto.
  Qed.

  Lemma update_same : forall (st : state) (x1 x2 : id) (n1 m : A),
    st / x1 => n1 -> st / x2 => m -> st [x1 <- n1] / x2 => m.
  Proof.
    intros st x1 x2 n1 m nH mH. destruct (eq_id_dec x1 x2) as [eH | neH].
    - rewrite eH. assert (mnH: m = n1).
      { apply state_deterministic with (st := st) (x := x1).
        rewrite eH. auto. auto. }
      rewrite mnH. apply st_binds_hd.
    - apply st_binds_tl. auto. auto.
  Qed.

  Lemma update_permute : forall (st : state) (x1 x2 x3 : id) (n1 n2 m : A),
    x2 <> x1 -> 
    st [x2 <- n1][x1 <- n2] / x3 => m ->
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof.
    intros st x1 x2 x3 n1 n2 m neH H. destruct (eq_id_dec x1 x3) as [eH | nH].
    - rewrite eH in H. apply st_binds_tl.
      + rewrite <- eH. intros contra. symmetry in contra. contradiction.
      + inversion H.
        * rewrite eH. apply st_binds_hd.
        * contradiction.
    - inversion H.
      + contradiction.
      + destruct (eq_id_dec x3 x2) as [eH' | nH'].
        * inversion H6.
          { apply st_binds_hd. }
          { contradiction. }
        * apply st_binds_tl. auto. apply st_binds_tl. auto.
          inversion H6.
          { symmetry in H7. contradiction. }
          { auto. }
  Qed.

End S.