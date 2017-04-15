Add LoadPath "~/AU/Coq/coq-supplementary".

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
  bs_eq_intro: forall (s1 s2 : stmt), 
                 (forall (c c' : conf), c == s1 ==> c' <-> c == s2 ==> c') -> s1 ~~~ s2
where "s1 '~~~' s2" := (bs_equivalent s1 s2).

Module SmokeTest.

  Lemma seq_assoc : forall (s1 s2 s3 : stmt),
                      ((s1 ;; s2) ;; s3) ~~~ (s1 ;; (s2 ;; s3)).
  Proof.
    intros. apply bs_eq_intro. intros. split.
    - intros. inversion H. inversion H2. apply bs_Seq with (c' := c'1).
      auto. apply bs_Seq with (c' := c'0). auto. auto.
    - intros. inversion H. inversion H5. apply bs_Seq with (c' := c'1).
      apply bs_Seq with (c' := c'0). auto. auto. auto.
  Qed.

  Lemma while_unfolds : forall (e : expr) (s : stmt),
                          (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof.
    intros. apply bs_eq_intro. intros. split.
    - intros. inversion H.
      + apply bs_If_True. auto. apply bs_Seq with (c' := c'0). auto. auto.
      + apply bs_If_False. auto. apply bs_Skip.
    - intros. inversion H.
      + inversion H6. apply bs_While_True with (c' := c'1). auto. auto. auto.
      + inversion H6. apply bs_While_False. auto.
  Qed.

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

  Definition True := Nat 1.

  Lemma loop_eq_undefined : (WHILE True DO SKIP END) ~~~ (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof.
    constructor. intros. split.
    - intros. exfalso. remember (WHILE True DO SKIP END). induction H.
      + inversion Heqs.
      + inversion Heqs.
      + inversion Heqs.
      + inversion Heqs.
      + inversion Heqs.
      + inversion Heqs.
      + inversion Heqs.
      + auto.
      + inversion Heqs. rewrite H1 in H. inversion H.
    - intros. inversion H.
      + inversion H5.
      + inversion H5.
Qed.

End SmokeTest.

(* Contextual equivalence *)
Inductive Context : Type :=
| Hole 
| SeqL   : Context -> stmt -> Context
| SeqR   : stmt -> Context -> Context
| IfThen : expr -> Context -> stmt -> Context
| IfElse : expr -> stmt -> Context -> Context
| WhileC : expr -> Context -> Context.

(* Plugging a statement into a context *)
Fixpoint plug (C : Context) (s : stmt) : stmt := 
  match C with
  | Hole => s
  | SeqL     C  s1 => Seq (plug C s) s1
  | SeqR     s1 C  => Seq s1 (plug C s) 
  | IfThen e C  s1 => If e (plug C s) s1
  | IfElse e s1 C  => If e s1 (plug C s)
  | WhileC   e  C  => While e (plug C s)
  end.  

Notation "C '<~' e" := (plug C e) (at level 43, no associativity).

(* Contextual equivalence *)
Reserved Notation "e1 '~c~' e2" (at level 42, no associativity).

Inductive contextual_equivalent: stmt -> stmt -> Prop :=
  ceq_intro : forall (s1 s2 : stmt),
                (forall (C : Context), (C <~ s1) ~~~ (C <~ s2)) -> s1 ~c~ s2
where "s1 '~c~' s2" := (contextual_equivalent s1 s2).

(* Ltac siin h := simpl in h.

Ltac rew h := rewrite h.

Ltac rev_rew h := rewrite <- h.

Ltac on_plug s t1 t2 :=
  match goal with
  | H: (_ = _ <~ s) |- _ => (t1 H; t2 H)
  end. *)

Lemma eq_to_ceq: forall (s1 s2 p1 p2 : stmt) (C : Context) (c c' : conf),
  c == p1 ==> c' -> p1 = C <~ s1 -> p2 = C <~ s2 ->
    (forall (c0 c1 : conf), c0 == s1 ==> c1 -> c0 == s2 ==> c1) -> c == p2 ==> c'.
Proof.
  intros s1 s2 p1 p2 C c c' H. revert s1 s2 p2 C. induction H.
  - intros. destruct C.
    + (match goal with H: (p2 = _ <~ _) |- _ => simpl in H; rewrite H end).
      (match goal with H: (forall _ _ : conf, _ -> _) |- _ => apply H end).
      (match goal with H: (_ = _ <~ s1) |- _ => simpl in H; rewrite <- H end).
      constructor.
    + (match goal with H: (_ = _ <~ s1) |- _ => simpl in H; inversion H end).
    + (match goal with H: (_ = _ <~ s1) |- _ => simpl in H; inversion H end).
    + (match goal with H: (_ = _ <~ s1) |- _ => simpl in H; inversion H end).
    + (match goal with H: (_ = _ <~ s1) |- _ => simpl in H; inversion H end).
    + (match goal with H: (_ = _ <~ s1) |- _ => simpl in H; inversion H end).
  - intros. destruct C.
    + (match goal with H: (p2 = _ <~ _) |- _ => simpl in H; rewrite H end).
      (match goal with H: (forall _ _ : conf, _ -> _) |- _ => apply H end).
      (match goal with H: (_ = _ <~ s1) |- _ => simpl in H; rewrite <- H end).
      constructor. assumption.
    + (match goal with H: (_ = _ <~ s1) |- _ => simpl in H; inversion H end).
    + (match goal with H: (_ = _ <~ s1) |- _ => simpl in H; inversion H end).
    + (match goal with H: (_ = _ <~ s1) |- _ => simpl in H; inversion H end).
    + (match goal with H: (_ = _ <~ s1) |- _ => simpl in H; inversion H end).
    + (match goal with H: (_ = _ <~ s1) |- _ => simpl in H; inversion H end).
  - intros. destruct C.
    + (match goal with H: (p2 = _ <~ _) |- _ => simpl in H; rewrite H end).
      (match goal with H: (forall _ _ : conf, _ -> _) |- _ => apply H end).
      (match goal with H: (_ = _ <~ s1) |- _ => simpl in H; rewrite <- H end).
      constructor.
    + (match goal with H: (_ = _ <~ s1) |- _ => simpl in H; inversion H end).
    + (match goal with H: (_ = _ <~ s1) |- _ => simpl in H; inversion H end).
    + (match goal with H: (_ = _ <~ s1) |- _ => simpl in H; inversion H end).
    + (match goal with H: (_ = _ <~ s1) |- _ => simpl in H; inversion H end).
    + (match goal with H: (_ = _ <~ s1) |- _ => simpl in H; inversion H end).
  - intros. destruct C.
    + (match goal with H: (p2 = _ <~ _) |- _ => simpl in H; rewrite H end).
      (match goal with H: (forall _ _ : conf, _ -> _) |- _ => apply H end).
      (match goal with H: (_ = _ <~ s1) |- _ => simpl in H; rewrite <- H end).
      constructor. assumption.
    + (match goal with H: (_ = _ <~ s1) |- _ => simpl in H; inversion H end).
    + (match goal with H: (_ = _ <~ s1) |- _ => simpl in H; inversion H end).
    + (match goal with H: (_ = _ <~ s1) |- _ => simpl in H; inversion H end).
    + (match goal with H: (_ = _ <~ s1) |- _ => simpl in H; inversion H end).
    + (match goal with H: (_ = _ <~ s1) |- _ => simpl in H; inversion H end).
  - intros. destruct C.
    + simpl in H2. rewrite H2. apply H3. simpl in H1. rewrite <- H1. apply bs_Seq with c'; assumption.
    + simpl in H2. rewrite H2. simpl in H1. inversion H1. apply bs_Seq with c'.
      * apply IHbs_int1 with (s2 := s0) (s3 := s3) (C := C); auto.
      * congruence.
    + simpl in H2. rewrite H2. simpl in H1. inversion H1. apply bs_Seq with c'.
      * congruence.
      * apply IHbs_int2 with (s1 := s0) (s3 := s3) (C := C); auto.
    + simpl in H1. inversion H1.
    + simpl in H1. inversion H1.
    + simpl in H1. inversion H1.
  - intros. destruct C.
    + simpl in H2. rewrite H2. apply H3. simpl in H1. rewrite <- H1. apply bs_If_True; assumption.
    + simpl in H1. inversion H1.
    + simpl in H1. inversion H1.
    + simpl in H2. rewrite H2. simpl in H1. inversion H1. apply bs_If_True.
      * congruence.
      * apply IHbs_int with (s2 := s0) (s3 := s3) (C := C); auto.
    + simpl in H2. rewrite H2. simpl in H1. inversion H1. apply bs_If_True; congruence.
    + simpl in H1. inversion H1.
  - intros. destruct C.
    + simpl in H2. rewrite H2. apply H3. simpl in H1. rewrite <- H1. apply bs_If_False; assumption.
    + simpl in H1. inversion H1.
    + simpl in H1. inversion H1.
    + simpl in H2. rewrite H2. simpl in H1. inversion H1. apply bs_If_False; congruence.
    + simpl in H2. rewrite H2. simpl in H1. inversion H1. apply bs_If_False.
      * congruence.
      * apply IHbs_int with (s1 := s0) (s3 := s3) (C := C); auto.
    + simpl in H1. inversion H1.
  - intros. destruct C.
    + simpl in H3. rewrite H3. apply H4. simpl in H2. rewrite <- H2. apply bs_While_True with c'; assumption.
    + simpl in H2. inversion H2.
    + simpl in H2. inversion H2.
    + simpl in H2. inversion H2.
    + simpl in H2. inversion H2.
    + simpl in H3. rewrite H3. simpl in H2. inversion H2. apply bs_While_True with c'.
      * congruence.
      * apply IHbs_int1 with (s1 := s1) (s2 := s2) (C := C); auto.
      * apply IHbs_int2 with (s1 := s1) (s2 := s2) (C := WhileC e C).
        { simpl. congruence. }
        { simpl. congruence. }
        { auto. }
  - intros. destruct C.
    + simpl in H1. rewrite H1. apply H2. simpl in H0. rewrite <- H0. apply bs_While_False; assumption.
    + simpl in H0. inversion H0.
    + simpl in H0. inversion H0.
    + simpl in H0. inversion H0.
    + simpl in H0. inversion H0.
    + simpl in H1. rewrite H1. simpl in H0. inversion H0. apply bs_While_False; congruence.
Qed.

(* Contextual equivalence is equivalent to the semantic one *)
Lemma eq_eq_ceq: forall (s1 s2 : stmt), s1 ~~~ s2 <-> s1 ~c~ s2.
Proof.
  intros. split.
  - intros. inversion_clear H. constructor. intros.
    constructor. intros. split.
    + intros. apply eq_to_ceq with s1 s2 (C <~ s1) C; auto. apply H0.
    + intros. apply eq_to_ceq with s2 s1 (C <~ s2) C; auto. apply H0.
  - intros. inversion_clear H. apply (H0 Hole).
Qed.

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

Lemma bs_int_to_cps_int_segment: forall (c c' c'' : conf) (s : stmt) (k : cont),
  c == s ==> c' -> KEmpty |- c' -- k --> c'' -> k |- c -- !s --> c''.
Proof.
  intros c c' c'' s k H. revert c'' k. induction H.
  - intros. apply cps_Skip. assumption.
  - intros. apply cps_Assn with z. assumption. assumption.
  - intros. apply cps_Read. assumption.
  - intros. apply cps_Write with z. assumption. assumption.
  - intros. apply cps_Seq. apply IHbs_int1. unfold Kapp. destruct k.
    + inversion H1. apply IHbs_int2. rewrite H5. apply cps_Empty.
    + apply cps_Seq. unfold Kapp. apply IHbs_int2. assumption.
  - intros. apply cps_If_True. assumption. apply IHbs_int. assumption.
  - intros. apply cps_If_False. assumption. apply IHbs_int. assumption.
  - intros. apply cps_While_True. assumption. apply IHbs_int1. unfold Kapp. destruct k.
    + inversion H2. apply IHbs_int2. rewrite H6. apply cps_Empty.
    + apply cps_Seq. unfold Kapp. apply IHbs_int2. assumption.
  - intros. apply cps_While_False. assumption. assumption.
Qed.


Lemma bs_int_to_cps_int: forall (st : state Z) (i o : list Z) (c' : conf) (s : stmt),
  (st, i, o) == s ==> c' -> KEmpty |- (st, i, o) -- !s --> c'.
Proof.
  intros. apply bs_int_to_cps_int_segment with c'. assumption. constructor.
Qed.

Lemma bs_int_to_cps_int_gen: forall (c c' : conf) (s s_all : stmt) (k : cont),
  k |- c -- !s --> c' -> !s_all = !s @ k ->  c == s_all ==> c'.
Proof.
  intros c c' s s_all k H. revert s_all. induction H.
  - unfold Kapp. intros. inversion H.
  - unfold Kapp. destruct k.
    + inversion H. intros. inversion H0. apply bs_Skip.
    + intros. inversion H0. apply bs_Seq with c. apply bs_Skip. apply IHcps_int.
      unfold Kapp. reflexivity.
  - unfold Kapp. destruct k.
    + inversion H0. intros. inversion H1. apply bs_Assign. assumption.
    + intros. inversion H1. apply bs_Seq with ((s0) [x <- n], i, o).
      apply bs_Assign. assumption. apply IHcps_int. unfold Kapp. reflexivity.
  - unfold Kapp. destruct k.
    + inversion H. intros. inversion H0. apply bs_Read.
    + intros. inversion H0. apply bs_Seq with ((s0) [x <- z], i, o).
      apply bs_Read. apply IHcps_int. unfold Kapp. reflexivity.
  - unfold Kapp. destruct k.
    + inversion H0. intros. inversion H1. apply bs_Write. assumption.
    + intros. inversion H1. apply bs_Seq with (s0, i, z :: o).
      apply bs_Write. assumption. apply IHcps_int. unfold Kapp. reflexivity.
  - unfold Kapp. destruct k.
    + intros. apply IHcps_int. unfold Kapp. apply H0.
    + intros. inversion H0. assert ((c) == s1;; s2;; s0 ==> (c')).
      { apply IHcps_int. unfold Kapp. reflexivity. }
      inversion H1. inversion H8. apply bs_Seq with c'1.
      * apply bs_Seq with c'0. assumption. assumption.
      * assumption.
  - unfold Kapp. destruct k.
    + intros. inversion H1. apply bs_If_True. assumption. apply IHcps_int.
      unfold Kapp. reflexivity.
    + intros. inversion H1. assert ((s0, i, o) == s1 ;; s3 ==> c').
      { auto. }
      inversion H2. apply bs_Seq with c'0. apply bs_If_True.
      assumption. assumption. assumption.
  - unfold Kapp. destruct k.
    + intros. inversion H1. apply bs_If_False. assumption. apply IHcps_int.
      unfold Kapp. reflexivity.
    + intros. inversion H1. assert ((s0, i, o) == s2 ;; s3 ==> c').
      { auto. }
      inversion H2. apply bs_Seq with c'0. apply bs_If_False.
      assumption. assumption. assumption.
  - unfold Kapp. destruct k.
    + assert (((st, i, o)) == s0 ;; WHILE e DO s0 END ==> (c')).
      { apply IHcps_int. unfold Kapp. reflexivity. }
      intros. inversion H2. inversion H1. apply bs_While_True with c'0.
      assumption. assumption. assumption.
    + assert (((st, i, o)) == s0 ;; WHILE e DO s0 END ;; s1 ==> (c')).
      { apply IHcps_int. unfold Kapp. reflexivity. }
      inversion H1. inversion H7. intros. inversion H14. apply bs_Seq with c'1.
      * apply bs_While_True with c'0. assumption. assumption. assumption.
      * assumption.
  - unfold Kapp. destruct k.
    + inversion H0. intros. inversion H1. apply bs_While_False. assumption.
    + intros. inversion H1. apply bs_Seq with (st, i, o).
      * apply bs_While_False. assumption.
      * apply IHcps_int. unfold Kapp. reflexivity.
Qed.

Lemma cps_int_to_bs_int: forall (st : state Z) (i o : list Z) (c' : conf) (s : stmt),
  KEmpty |- (st, i, o) -- !s --> c' -> (st, i, o) == s ==> c'.
Proof. intros. apply bs_int_to_cps_int_gen with (s := s) (k := KEmpty).
       assumption. auto. Qed.
