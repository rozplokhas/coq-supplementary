Require Import List.
Import ListNotations.
Require Import Omega.

Require Export BigZ.
Require Export Id.
Require Export State.
Require Export Expr.

(* The type of statements *)
Inductive stmt : Type :=
  | SKIP  : stmt
  | Assn  : id -> expr -> stmt
  | READ  : id -> stmt
  | WRITE : expr -> stmt
  | Seq   : stmt -> stmt -> stmt
  | If    : expr -> stmt -> stmt -> stmt
  | While : expr -> stmt -> stmt.

(* Supplementary notation *)
Notation "x  '::=' e"                         := (Assn  x e    ) (at level 37, no associativity).
Notation "s1 ';;'  s2"                        := (Seq   s1 s2  ) (at level 35, right associativity).
Notation "'COND' e 'THEN' s1 'ELSE' s2 'END'" := (If    e s1 s2) (at level 36, no associativity).
Notation "'WHILE' e 'DO' s 'END'"             := (While e s    ) (at level 36, no associativity).

(* Configuration *)
Definition conf :=  (state Z * list Z * list Z)%type.

Reserved Notation "c1 '==' s '==>' c2" (at level 0).

(* Big-step evaluation relation *)
Notation "st [ x '<-' y ]" := (update Z st x y) (at level 0).

Inductive bs_int : stmt -> conf -> conf -> Prop := 
  | bs_Skip        : forall (c : conf), c == SKIP ==> c 
  | bs_Assign      : forall (s : state Z) (i o : list Z) (x : id) (e : expr) (z : Z), 
                       [| e |] s => z -> (s, i, o) == x ::= e ==> (s [x <- z], i, o)
  | bs_Read        : forall (s : state Z) (i o : list Z) (x : id) (z : Z),
                       (s, z::i, o) == READ x ==> (s [x <- z], i, o)
  | bs_Write       : forall (s : state Z) (i o : list Z) (e : expr) (z : Z), 
                       [| e |] s => z -> (s, i, o) == WRITE e ==> (s, i, z::o)
  | bs_Seq         : forall (c c' c'' : conf) (s1 s2 : stmt),
                       c == s1 ==> c' -> c' == s2 ==> c'' -> c ==  s1 ;; s2 ==> c''
  | bs_If_True     : forall (s : state Z) (i o : list Z) (c' : conf) (e : expr) (s1 s2 : stmt),
                       [| e |] s => Z.one -> (s, i, o) == s1 ==> c' -> (s, i, o) == COND e THEN s1 ELSE s2 END ==> c'
  | bs_If_False    : forall (s : state Z) (i o : list Z) (c' : conf) (e : expr) (s1 s2 : stmt),
                       [| e |] s => Z.zero -> (s, i, o) == s2 ==> c' -> (s, i, o) == COND e THEN s1 ELSE s2 END ==> c'
  | bs_While_True  : forall (st : state Z) (i o : list Z) (c' c'' : conf) (e : expr) (s : stmt),
                       [| e |] st => Z.one -> (st, i, o) == s ==> c' -> c' == WHILE e DO s END ==> c'' ->
                          (st, i, o) == WHILE e DO s END ==> c''
  | bs_While_False : forall (st : state Z) (i o : list Z) (e : expr) (s : stmt),
                       [| e |] st => Z.zero -> (st, i, o) == WHILE e DO s END ==> (st, i, o)
where "c1 == s ==> c2" := (bs_int s c1 c2).

(* Big-step semantics is deterministic *)
(* Note: DB did not prove this yet     *)
Lemma bs_int_deterministic : forall (c c1 c2 : conf) (s : stmt), c == s ==> c1 -> c == s ==> c2 -> c1 = c2.
Proof.
  assert (zero_one_contra: forall (e : expr) (s : state Z) (P : Prop),
                              [|e|] s => (Z.zero) -> [|e|] s => (Z.one) -> P).
  { intros. assert (contra: Z.zero = Z.one).
    * apply bs_eval_deterministic with (e := e) (s := s). auto. auto.
    * inversion contra. }
  intros c c1 c2 s FH. generalize dependent c2. induction FH.
  - intros. inversion H. reflexivity.
  - intros. inversion H0. replace z0 with z.
    + reflexivity.
    + apply bs_eval_deterministic with (e := e) (s := s). auto. auto.
  - intros. inversion H. reflexivity.
  - intros. inversion H0. replace z0 with z.
    + reflexivity.
    + apply bs_eval_deterministic with (e := e) (s := s). auto. auto.
  - intros. inversion H.
    assert (c'eq: c'= c'0). { apply IHFH1. auto. } rewrite <- c'eq in H5.
    apply IHFH2. auto.
  - intros. inversion H0.
    + apply IHFH. auto.
    + apply zero_one_contra with (e := e) (s := s). auto. auto.
  - intros. inversion H0.
    + apply zero_one_contra with (e := e) (s := s). auto. auto.
    + apply IHFH. auto.
  - intros. inversion H0.
    + assert (c'eq: c'= c'0). { apply IHFH1. auto. } rewrite <- c'eq in H9.
      apply IHFH2. auto.
    + apply zero_one_contra with (e := e) (s := st). auto. auto.
  - intros. inversion H0.
    + apply zero_one_contra with (e := e) (s := st). auto. auto.
    + reflexivity.
Qed.

Reserved Notation "s1 '~~~' s2" (at level 0).

Inductive bs_equivalent: stmt -> stmt -> Prop :=
  bs_eq_intro: forall (s1 s2 : stmt), (forall (c c' : conf), (c == s1 ==> c' <-> c == s2 ==> c')) -> s1 ~~~ s2
where "s1 '~~~' s2" := (bs_equivalent s1 s2).

Module SmokeTest.

  Lemma while_false : forall (e : expr) (s : stmt) (st : state Z) (i o : list Z) (c : conf),
                        c == WHILE e DO s END ==> (st, i, o) -> [| e |] st => Z.zero.
  Proof.
    intros. remember (WHILE e DO s END) as instr. remember (st, i, o) as c'. induction H.
    - inversion Heqinstr.
    - inversion Heqinstr.
    - inversion Heqinstr.
    - inversion Heqinstr.
    - inversion Heqinstr.
    - inversion Heqinstr.
    - inversion Heqinstr.
    - inversion Heqinstr. apply IHbs_int2. auto. auto.
    - inversion Heqinstr. inversion Heqc'. congruence.
  Qed.

  Definition X := Id 1.
  Definition True := Nat 1.

  Lemma loop_eq_undefined : (WHILE True DO SKIP END) ~~~ (WHILE True DO READ X END).
  Proof.
    assert (forall (s : stmt) (c c' : conf), ~ (c == WHILE True DO s END ==> c')) as WhileTrueDiverge.
    { intros. intros H. remember (WHILE True DO s END). induction H.
      - inversion Heqs0.
      - inversion Heqs0.
      - inversion Heqs0.
      - inversion Heqs0.
      - inversion Heqs0.
      - inversion Heqs0.
      - inversion Heqs0.
      - inversion Heqs0. auto.
      - inversion Heqs0. rewrite H1 in H. unfold True in H. inversion H. }
    apply bs_eq_intro. intros. split.
    - intros. exfalso. unfold not in WhileTrueDiverge. apply WhileTrueDiverge with SKIP c c'. auto.
    - intros. exfalso. unfold not in WhileTrueDiverge. apply WhileTrueDiverge with (READ X) c c'. auto.
  Qed.

  Lemma while_unfolding: forall (e : expr) (s : stmt),
    WHILE e DO s END ~~~ COND e THEN (s ;; WHILE e DO s END) ELSE SKIP END.
  Proof.
    intros. apply bs_eq_intro. intros. split.
    - intros. inversion H.
      + apply bs_If_True. auto. apply bs_Seq with (c' := c'0). auto. auto.
      + apply bs_If_False. auto. apply bs_Skip.
    - intros. inversion H.
      + inversion H6. apply bs_While_True with (c' := c'1). auto. auto. auto.
      + inversion H6. apply bs_While_False. auto.
  Qed.

  Lemma seq_associativity: forall (s1 s2 s3 : stmt),
    (s1 ;; (s2 ;; s3)) ~~~ ((s1 ;; s2) ;; s3).
  Proof.
    intros. apply bs_eq_intro. intros. split.
    - intros. inversion H. inversion H5. apply bs_Seq with (c' := c'1).
      apply bs_Seq with (c' := c'0). auto. auto. auto.
    - intros. inversion H. inversion H2. apply bs_Seq with (c' := c'1).
      auto. apply bs_Seq with (c' := c'0). auto. auto.
  Qed.

End SmokeTest.

Reserved Notation "s1 '~~~' s2" (at level 0).

Inductive bs_equivalent: stmt -> stmt -> Prop :=
  bs_eq_intro: forall (s1 s2 : stmt) (c c' : conf), (c == s1 ==> c' <-> c == s2 ==> c') -> s1 ~~~ s2
where "s1 '~~~' s2" := (bs_equivalent s1 s2).

Module SmokeTest.

  Lemma while_false : forall (e : expr) (s : stmt) (st : state Z) (i o : list Z) (c : conf),
                        c == WHILE e DO s END ==> (st, i, o) -> [| e |] st => Z.zero.
  Proof. admit. Admitted.

  Definition X := Id 1.
  Definition Y := Id 2.
  Definition True := Nat 1.

  Lemma loop_eq_undefined : (WHILE True DO SKIP END) ~~~ (X ::= Var Y).
  Proof. admit. Admitted.  
  
End SmokeTest.

(* CPS-style semantics *)
Inductive cont : Type := 
| KEmpty : cont
| KStmt  : stmt -> cont.

Definition Kapp (l r : cont) : cont :=
  match (l, r) with
  | (KStmt ls, KStmt rs) => KStmt (ls ;; rs)
  | (KEmpty  , _       ) => r
  | (_       , _       ) => l
  end.

Notation "'!' s" := (KStmt s) (at level 0).
Notation "s1 @ s2" := (Kapp s1 s2) (at level 0).

Reserved Notation "k '|-' c1 '--' s '-->' c2" (at level 0).

Inductive cps_int : cont -> cont -> conf -> conf -> Prop :=
| cps_Empty       : forall (c : conf), KEmpty |- c -- KEmpty --> c
| cps_Skip        : forall (c c' : conf) (k : cont), 
                      KEmpty |- c -- k --> c' -> 
                      k |- c -- !SKIP --> c'
| cps_Assn        : forall (s : state Z) (i o : list Z) (c' : conf) (k : cont) (x : id) (e : expr) (n : Z),
                      [| e |] s => n ->
                      KEmpty |- (s [x <- n], i, o) -- k --> c' ->
                      k |- (s, i, o) -- !(x ::= e) --> c'
| cps_Read        : forall (s : state Z) (i o : list Z) (c' : conf) (k : cont) (x : id) (z : Z),
                      KEmpty |- (s [x <- z], i, o) -- k --> c' ->
                      k |- (s, z::i, o) -- !(READ x) --> c'
| cps_Write       : forall (s : state Z) (i o : list Z) (c' : conf) (k : cont) (e : expr) (z : Z),
                      [| e |] s => z ->
                      KEmpty |- (s, i, z::o) -- k --> c' ->
                      k |- (s, i, o) -- !(WRITE e) --> c'
| cps_Seq         : forall (c c' : conf) (k : cont) (s1 s2 : stmt), 
                      !s2 @ k |- c -- !s1 --> c' ->
                      k |- c -- !(s1 ;; s2) --> c'
| cps_If_True     : forall (s : state Z) (i o : list Z) (c' : conf) (k : cont) (e : expr) (s1 s2 : stmt),
                      [| e |] s => Z.one ->
                      k |- (s, i, o) -- !s1 --> c' ->
                      k |- (s, i, o) -- !(COND e THEN s1 ELSE s2 END) --> c'
| cps_If_False    : forall (s : state Z) (i o : list Z) (c' : conf) (k : cont) (e : expr) (s1 s2 : stmt),
                      [| e |] s => Z.zero ->
                      k |- (s, i, o) -- !s2 --> c' ->
                      k |- (s, i, o) -- !(COND e THEN s1 ELSE s2 END) --> c'
| cps_While_True  : forall (st : state Z) (i o : list Z) (c' : conf) (k : cont) (e : expr) (s : stmt),
                      [| e |] st => Z.one ->
                      !(WHILE e DO s END) @ k |- (st, i, o) -- !s --> c' ->
                      k |- (st, i, o) -- !(WHILE e DO s END) --> c'
| cps_While_False : forall (st : state Z) (i o : list Z) (c' : conf) (k : cont) (e : expr) (s : stmt),
                      [| e |] st => Z.zero ->
                      KEmpty |- (st, i, o) -- k --> c' ->
                      k |- (st, i, o) -- !(WHILE e DO s END) --> c'
where "k |- c1 -- s --> c2" := (cps_int k s c1 c2).

Lemma bs_int_to_cps_int: forall (st : state Z) (i o : list Z) (c' : conf) (s : stmt),
  (st, i, o) == s ==> c' -> KEmpty |- (st, i, o) -- !s --> c'.
Proof. admit. Admitted.

Lemma cps_int_to_bs_int: forall (st : state Z) (i o : list Z) (c' : conf) (s : stmt),
  KEmpty |- (st, i, o) -- !s --> c' -> (st, i, o) == s ==> c'.
Proof. admit. Admitted.
