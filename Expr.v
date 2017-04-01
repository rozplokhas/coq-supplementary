Require Export BigZ.
Require Export Id.
Require Export State.

(* Type of arithmetic expressions *)
Inductive expr : Type :=
  | Nat : nat  -> expr
  | Var : id   -> expr
  | Add : expr -> expr -> expr
  | Sub : expr -> expr -> expr
  | Mul : expr -> expr -> expr
  | Div : expr -> expr -> expr
  | Mod : expr -> expr -> expr
  | Le  : expr -> expr -> expr
  | Lt  : expr -> expr -> expr
  | Ge  : expr -> expr -> expr
  | Gt  : expr -> expr -> expr
  | Eq  : expr -> expr -> expr
  | Ne  : expr -> expr -> expr
  | And : expr -> expr -> expr
  | Or  : expr -> expr -> expr.

(* Supplementary notation *)
Notation "x '[+]'  y" := (Add x y) (at level 40, left associativity).
Notation "x '[-]'  y" := (Sub x y) (at level 40, left associativity).
Notation "x '[*]'  y" := (Mul x y) (at level 41, left associativity).
Notation "x '[/]'  y" := (Div x y) (at level 41, left associativity).
Notation "x '[%]'  y" := (Mod x y) (at level 41, left associativity).
Notation "x '[<=]' y" := (Le  x y) (at level 39, no associativity).
Notation "x '[<]'  y" := (Lt  x y) (at level 39, no associativity).
Notation "x '[>=]' y" := (Ge  x y) (at level 39, no associativity).
Notation "x '[>]'  y" := (Gt  x y) (at level 39, no associativity).
Notation "x '[==]' y" := (Eq  x y) (at level 39, no associativity).
Notation "x '[/=]' y" := (Ne  x y) (at level 39, no associativity).
Notation "x '[&]'  y" := (And x y) (at level 38, left associativity).
Notation "x '[\/]' y" := (Or  x y) (at level 38, left associativity).

Definition zbool (x : Z) : Prop := x = Z.one \/ x = Z.zero.

Definition zor (x y : Z) : Z :=
  if Z_le_gt_dec (Z.of_nat 1) (x + y) then Z.one else Z.zero.

Reserved Notation "[| e |] st => z" (at level 0).
Notation "st / x => y" := (st_binds Z st x y) (at level 0).

(* Big-step evaluation relation *)
Inductive bs_eval : expr -> state Z -> Z -> Prop := 
  bs_Nat  : forall (s : state Z) (n : nat), [| Nat n |] s => (Z.of_nat n)
| bs_Var  : forall (s : state Z) (i : id) (z : Z), s / i => z -> [| Var i |] s => z

| bs_Add  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| a [+] b |] s => (za + zb)
| bs_Sub  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| a [-] b |] s => (za - zb)
| bs_Mul  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| a [*] b |] s => (za * zb)
| bs_Div  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| a [/] b |] s => (Z.div za zb)
| bs_Mod  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| a [%] b |] s => (Z.modulo za zb)

| bs_Le_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.le za zb -> [| a [<=] b |] s => Z.one
| bs_Le_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.gt za zb -> [| a [<=] b |] s => Z.zero

| bs_Lt_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.lt za zb -> [| a [<] b |] s => Z.one
| bs_Lt_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.ge za zb -> [| a [<] b |] s => Z.zero

| bs_Ge_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.ge za zb -> [| a [>=] b |] s => Z.one
| bs_Ge_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.lt za zb -> [| a [>=] b |] s => Z.zero

| bs_Gt_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.gt za zb -> [| a [>] b |] s => Z.one
| bs_Gt_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.le za zb -> [| a [>] b |] s => Z.zero

| bs_Eq_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.eq za zb -> [| a [==] b |] s => Z.one
| bs_Eq_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> ~ Z.eq za zb -> [| a [==] b |] s => Z.zero

| bs_Ne_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> ~ Z.eq za zb -> [| a [/=] b |] s => Z.one
| bs_Ne_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.eq za zb -> [| a [/=] b |] s => Z.zero

| bs_And  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> zbool za -> zbool zb -> [| a [&] b |] s => (za * zb)

| bs_Or   : forall (s : state Z) (a b : expr) (za zb : Z), 
              [| a |] s => za -> [| b |] s => zb -> zbool za -> zbool zb -> [| a [\/] b |] s => (zor za zb)
where "[| e |] st => z" := (bs_eval e st z). 

Hint Constructors bs_eval.

Module SmokeTest.

  Lemma nat_always :
    forall (n : nat) (s : state Z), [| Nat n |] s => (Z.of_nat n).
  Proof. auto. Qed.

  Lemma double_and_sum : 
    forall (s : state Z) (e : expr) (z : Z), 
      [| e [*] (Nat 2) |] s => z -> [| e [+] e |] s => z.
  Proof.
    intros s e z H. inversion H. inversion H5.
    replace (Z.mul za (Z.of_nat 2)) with (Z.add za za).
    - apply bs_Add. auto. auto.
    - simpl. omega. Qed.

End SmokeTest.

Reserved Notation "x ? e" (at level 0).

(* Set of variables is an expression *)
Inductive V : expr -> id -> Prop := 
  v_Var : forall (id : id), id ? (Var id)
| v_Add : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [+]  b)
| v_Sub : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [-]  b)
| v_Mul : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [*]  b)
| v_Div : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [/]  b)
| v_Mod : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [%]  b)
| v_Le  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [<=] b)
| v_Lt  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [<]  b)
| v_Ge  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [>=] b)
| v_Gt  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [>]  b)
| v_Eq  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [==] b)
| v_Ne  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [/=] b)
| v_And : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [&]  b)
| v_Or  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [\/] b)
where "x ? e" := (V e x).

(* If an expression is defined in some state, then each its' variable is
   defined in that state
*)
Lemma defined_expression: forall (e : expr) (s : state Z) (z : Z) (id : id),
  [| e |] s => z -> id ? e -> exists z', s / id => z'.
Proof.
  intros e s z id H. induction H.
  - intros contra. inversion contra.
  - intros iH. inversion iH. exists z. rewrite <- H0. apply H.
  - intros H'. inversion H'. destruct H4. auto. auto.
  - intros H'. inversion H'. destruct H4. auto. auto.
  - intros H'. inversion H'. destruct H4. auto. auto.
  - intros H'. inversion H'. destruct H4. auto. auto.
  - intros H'. inversion H'. destruct H4. auto. auto.
  - intros H'. inversion H'. destruct H5. auto. auto.
  - intros H'. inversion H'. destruct H5. auto. auto.
  - intros H'. inversion H'. destruct H5. auto. auto.
  - intros H'. inversion H'. destruct H5. auto. auto.
  - intros H'. inversion H'. destruct H5. auto. auto.
  - intros H'. inversion H'. destruct H5. auto. auto.
  - intros H'. inversion H'. destruct H5. auto. auto.
  - intros H'. inversion H'. destruct H5. auto. auto.
  - intros H'. inversion H'. destruct H5. auto. auto.
  - intros H'. inversion H'. destruct H5. auto. auto.
  - intros H'. inversion H'. destruct H5. auto. auto.
  - intros H'. inversion H'. destruct H5. auto. auto.
  - intros H'. inversion H'. destruct H6. auto. auto.
  - intros H'. inversion H'. destruct H6. auto. auto.
Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable: forall (e : expr) (s : state Z) (id : id),
  id ? e -> (forall (z : Z), ~ (s / id => z)) -> (forall (z : Z), ~ ([| e |] s => z)).
Proof.
  intros e s id. unfold not. induction e.
  - intros H. inversion H.
  - intros iH. inversion iH. intros nH z H. inversion H.
    remember (nH z) as contra. contradiction.
  - intros. inversion H1. inversion H. destruct H11.
    + apply IHe1 with (z := za). auto. auto. auto.
    + apply IHe2 with (z := zb). auto. auto. auto.
  - intros. inversion H1. inversion H. destruct H11.
    + apply IHe1 with (z := za). auto. auto. auto.
    + apply IHe2 with (z := zb). auto. auto. auto.
  - intros. inversion H1. inversion H. destruct H11.
    + apply IHe1 with (z := za). auto. auto. auto.
    + apply IHe2 with (z := zb). auto. auto. auto.
  - intros. inversion H1. inversion H. destruct H11.
    + apply IHe1 with (z := za). auto. auto. auto.
    + apply IHe2 with (z := zb). auto. auto. auto.
  - intros. inversion H1. inversion H. destruct H11.
    + apply IHe1 with (z := za). auto. auto. auto.
    + apply IHe2 with (z := zb). auto. auto. auto.
  - intros. inversion H1.
    + inversion H. destruct H12.
      * apply IHe1 with (z := za). auto. auto. auto.
      * apply IHe2 with (z := zb). auto. auto. auto.
    + inversion H. destruct H12.
      * apply IHe1 with (z := za). auto. auto. auto.
      * apply IHe2 with (z := zb). auto. auto. auto.
  - intros. inversion H1.
    + inversion H. destruct H12.
      * apply IHe1 with (z := za). auto. auto. auto.
      * apply IHe2 with (z := zb). auto. auto. auto.
    + inversion H. destruct H12.
      * apply IHe1 with (z := za). auto. auto. auto.
      * apply IHe2 with (z := zb). auto. auto. auto.
  - intros. inversion H1.
    + inversion H. destruct H12.
      * apply IHe1 with (z := za). auto. auto. auto.
      * apply IHe2 with (z := zb). auto. auto. auto.
    + inversion H. destruct H12.
      * apply IHe1 with (z := za). auto. auto. auto.
      * apply IHe2 with (z := zb). auto. auto. auto.
  - intros. inversion H1.
    + inversion H. destruct H12.
      * apply IHe1 with (z := za). auto. auto. auto.
      * apply IHe2 with (z := zb). auto. auto. auto.
    + inversion H. destruct H12.
      * apply IHe1 with (z := za). auto. auto. auto.
      * apply IHe2 with (z := zb). auto. auto. auto.
  - intros. inversion H1.
    + inversion H. destruct H12.
      * apply IHe1 with (z := za). auto. auto. auto.
      * apply IHe2 with (z := zb). auto. auto. auto.
    + inversion H. destruct H12.
      * apply IHe1 with (z := za). auto. auto. auto.
      * apply IHe2 with (z := zb). auto. auto. auto.
  - intros. inversion H1.
    + inversion H. destruct H12.
      * apply IHe1 with (z := za). auto. auto. auto.
      * apply IHe2 with (z := zb). auto. auto. auto.
    + inversion H. destruct H12.
      * apply IHe1 with (z := za). auto. auto. auto.
      * apply IHe2 with (z := zb). auto. auto. auto.
  - intros. inversion H1. inversion H. destruct H13.
    + apply IHe1 with (z := za). auto. auto. auto.
    + apply IHe2 with (z := zb). auto. auto. auto.
  - intros. inversion H1. inversion H. destruct H13.
    + apply IHe1 with (z := za). auto. auto. auto.
    + apply IHe2 with (z := zb). auto. auto. auto.
Qed.

(* The evaluation relation is deterministic *)
Lemma bs_eval_deterministic: forall (e : expr) (s : state Z) (z1 z2 : Z),
  [| e |] s => z1 -> [| e |] s => z2 -> z1 = z2.
Proof.
  intros e s. induction e.
  - intros. inversion H. inversion H0. reflexivity.
  - intros. inversion H. inversion H0. apply state_deterministic with (st := s) (x := i).
    auto. auto.
  - intros. inversion H. inversion H0. replace za0 with za. replace zb0 with zb.
    reflexivity. auto. auto.
  - intros. inversion H. inversion H0. replace za0 with za. replace zb0 with zb.
    reflexivity. auto. auto.
  - intros. inversion H. inversion H0. replace za0 with za. replace zb0 with zb.
    reflexivity. auto. auto.
  - intros. inversion H. inversion H0. replace za0 with za. replace zb0 with zb.
    reflexivity. auto. auto.
  - intros. inversion H. inversion H0. replace za0 with za. replace zb0 with zb.
    reflexivity. auto. auto.
  - intros. inversion H.
    + inversion H0.
      * reflexivity.
      * assert (eq_a: za = za0). auto. assert (eq_b: zb = zb0). auto. omega.
    + inversion H0.
      * assert (eq_a: za = za0). auto. assert (eq_b: zb = zb0). auto. omega.
      * reflexivity.
  - intros. inversion H.
    + inversion H0.
      * reflexivity.
      * assert (eq_a: za = za0). auto. assert (eq_b: zb = zb0). auto. omega.
    + inversion H0.
      * assert (eq_a: za = za0). auto. assert (eq_b: zb = zb0). auto. omega.
      * reflexivity.
  - intros. inversion H.
    + inversion H0.
      * reflexivity.
      * assert (eq_a: za = za0). auto. assert (eq_b: zb = zb0). auto. omega.
    + inversion H0.
      * assert (eq_a: za = za0). auto. assert (eq_b: zb = zb0). auto. omega.
      * reflexivity.
  - intros. inversion H.
    + inversion H0.
      * reflexivity.
      * assert (eq_a: za = za0). auto. assert (eq_b: zb = zb0). auto. omega.
    + inversion H0.
      * assert (eq_a: za = za0). auto. assert (eq_b: zb = zb0). auto. omega.
      * reflexivity.
  - intros. inversion H.
    + inversion H0.
      * reflexivity.
      * assert (eq_a: za = za0). auto. assert (eq_b: zb = zb0). auto. congruence.
    + inversion H0.
      * assert (eq_a: za = za0). auto. assert (eq_b: zb = zb0). auto. congruence.
      * reflexivity.
  - intros. inversion H.
    + inversion H0.
      * reflexivity.
      * assert (eq_a: za = za0). auto. assert (eq_b: zb = zb0). auto. congruence.
    + inversion H0.
      * assert (eq_a: za = za0). auto. assert (eq_b: zb = zb0). auto. congruence.
      * reflexivity.
  - intros. inversion H. inversion H0. replace za0 with za. replace zb0 with zb.
    reflexivity. auto. auto.
  - intros. inversion H. inversion H0. replace za0 with za. replace zb0 with zb.
    reflexivity. auto. auto.
Qed.

(* Equivalence of states w.r.t. an identifier *)
Definition equivalent_states (s1 s2 : state Z) (id : id) :=
  forall z :Z, s1 /id => z <-> s2 / id => z.

(* The result of expression evaluation in a state dependes only on the values
   of occurring variables
*)
Lemma variable_relevance: forall (e : expr) (s1 s2 : state Z) (z : Z),
  (forall (id : id) (z : Z), id ? e -> equivalent_states s1 s2 id) -> 
  [| e |] s1 => z -> [| e |] s2 => z.
Proof.
  intros e s1 s2. induction e.
  - intros z _ H. inversion H. auto.
  - intros z eqH H. assert (equi: equivalent_states s1 s2 i).
    { apply eqH. apply (Z.of_nat 42). apply v_Var. } unfold equivalent_states in equi.
    apply bs_Var. apply equi. inversion H. auto.
  - intros. inversion H0. assert (lH: [|e1|] s2 => (za)).
    { apply IHe1. intros. apply H. apply (Z.of_nat 42). apply v_Add. auto. auto. }
    assert (rH: [|e2|] s2 => (zb)).
    { apply IHe2. intros. apply H. apply (Z.of_nat 42). apply v_Add. auto. auto. }
    auto.
  - intros. inversion H0. assert (lH: [|e1|] s2 => (za)).
    { apply IHe1. intros. apply H. apply (Z.of_nat 42). apply v_Sub. auto. auto. }
    assert (rH: [|e2|] s2 => (zb)).
    { apply IHe2. intros. apply H. apply (Z.of_nat 42). apply v_Sub. auto. auto. }
    auto.
  - intros. inversion H0. assert (lH: [|e1|] s2 => (za)).
    { apply IHe1. intros. apply H. apply (Z.of_nat 42). apply v_Mul. auto. auto. }
    assert (rH: [|e2|] s2 => (zb)).
    { apply IHe2. intros. apply H. apply (Z.of_nat 42). apply v_Mul. auto. auto. }
    auto.
  - intros. inversion H0. assert (lH: [|e1|] s2 => (za)).
    { apply IHe1. intros. apply H. apply (Z.of_nat 42). apply v_Div. auto. auto. }
    assert (rH: [|e2|] s2 => (zb)).
    { apply IHe2. intros. apply H. apply (Z.of_nat 42). apply v_Div. auto. auto. }
    auto.
  - intros. inversion H0. assert (lH: [|e1|] s2 => (za)).
    { apply IHe1. intros. apply H. apply (Z.of_nat 42). apply v_Mod. auto. auto. }
    assert (rH: [|e2|] s2 => (zb)).
    { apply IHe2. intros. apply H. apply (Z.of_nat 42). apply v_Mod. auto. auto. }
    auto.
  - intros. inversion H0.
      + assert (lH: [|e1|] s2 => (za)).
        { apply IHe1. intros. apply H. apply (Z.of_nat 42). apply v_Le. auto. auto. }
        assert (rH: [|e2|] s2 => (zb)).
        { apply IHe2. intros. apply H. apply (Z.of_nat 42). apply v_Le. auto. auto. }
        apply bs_Le_T with (za := za) (zb := zb). auto. auto. auto.
      + assert (lH: [|e1|] s2 => (za)).
        { apply IHe1. intros. apply H. apply (Z.of_nat 42). apply v_Le. auto. auto. }
        assert (rH: [|e2|] s2 => (zb)).
        { apply IHe2. intros. apply H. apply (Z.of_nat 42). apply v_Le. auto. auto. }
        apply bs_Le_F with (za := za) (zb := zb). auto. auto. auto.
  - intros. inversion H0.
      + assert (lH: [|e1|] s2 => (za)).
        { apply IHe1. intros. apply H. apply (Z.of_nat 42). apply v_Lt. auto. auto. }
        assert (rH: [|e2|] s2 => (zb)).
        { apply IHe2. intros. apply H. apply (Z.of_nat 42). apply v_Lt. auto. auto. }
        apply bs_Lt_T with (za := za) (zb := zb). auto. auto. auto.
      + assert (lH: [|e1|] s2 => (za)).
        { apply IHe1. intros. apply H. apply (Z.of_nat 42). apply v_Lt. auto. auto. }
        assert (rH: [|e2|] s2 => (zb)).
        { apply IHe2. intros. apply H. apply (Z.of_nat 42). apply v_Lt. auto. auto. }
        apply bs_Lt_F with (za := za) (zb := zb). auto. auto. auto.
  - intros. inversion H0.
      + assert (lH: [|e1|] s2 => (za)).
        { apply IHe1. intros. apply H. apply (Z.of_nat 42). apply v_Ge. auto. auto. }
        assert (rH: [|e2|] s2 => (zb)).
        { apply IHe2. intros. apply H. apply (Z.of_nat 42). apply v_Ge. auto. auto. }
        apply bs_Ge_T with (za := za) (zb := zb). auto. auto. auto.
      + assert (lH: [|e1|] s2 => (za)).
        { apply IHe1. intros. apply H. apply (Z.of_nat 42). apply v_Ge. auto. auto. }
        assert (rH: [|e2|] s2 => (zb)).
        { apply IHe2. intros. apply H. apply (Z.of_nat 42). apply v_Ge. auto. auto. }
        apply bs_Ge_F with (za := za) (zb := zb). auto. auto. auto.
  - intros. inversion H0.
      + assert (lH: [|e1|] s2 => (za)).
        { apply IHe1. intros. apply H. apply (Z.of_nat 42). apply v_Gt. auto. auto. }
        assert (rH: [|e2|] s2 => (zb)).
        { apply IHe2. intros. apply H. apply (Z.of_nat 42). apply v_Gt. auto. auto. }
        apply bs_Gt_T with (za := za) (zb := zb). auto. auto. auto.
      + assert (lH: [|e1|] s2 => (za)).
        { apply IHe1. intros. apply H. apply (Z.of_nat 42). apply v_Gt. auto. auto. }
        assert (rH: [|e2|] s2 => (zb)).
        { apply IHe2. intros. apply H. apply (Z.of_nat 42). apply v_Gt. auto. auto. }
        apply bs_Gt_F with (za := za) (zb := zb). auto. auto. auto.
  - intros. inversion H0.
      + assert (lH: [|e1|] s2 => (za)).
        { apply IHe1. intros. apply H. apply (Z.of_nat 42). apply v_Eq. auto. auto. }
        assert (rH: [|e2|] s2 => (zb)).
        { apply IHe2. intros. apply H. apply (Z.of_nat 42). apply v_Eq. auto. auto. }
        apply bs_Eq_T with (za := za) (zb := zb). auto. auto. auto.
      + assert (lH: [|e1|] s2 => (za)).
        { apply IHe1. intros. apply H. apply (Z.of_nat 42). apply v_Eq. auto. auto. }
        assert (rH: [|e2|] s2 => (zb)).
        { apply IHe2. intros. apply H. apply (Z.of_nat 42). apply v_Eq. auto. auto. }
        apply bs_Eq_F with (za := za) (zb := zb). auto. auto. auto.
  - intros. inversion H0.
      + assert (lH: [|e1|] s2 => (za)).
        { apply IHe1. intros. apply H. apply (Z.of_nat 42). apply v_Ne. auto. auto. }
        assert (rH: [|e2|] s2 => (zb)).
        { apply IHe2. intros. apply H. apply (Z.of_nat 42). apply v_Ne. auto. auto. }
        apply bs_Ne_T with (za := za) (zb := zb). auto. auto. auto.
      + assert (lH: [|e1|] s2 => (za)).
        { apply IHe1. intros. apply H. apply (Z.of_nat 42). apply v_Ne. auto. auto. }
        assert (rH: [|e2|] s2 => (zb)).
        { apply IHe2. intros. apply H. apply (Z.of_nat 42). apply v_Ne. auto. auto. }
        apply bs_Ne_F with (za := za) (zb := zb). auto. auto. auto.
  - intros. inversion H0. assert (lH: [|e1|] s2 => (za)).
    { apply IHe1. intros. apply H. apply (Z.of_nat 42). apply v_And. auto. auto. }
    assert (rH: [|e2|] s2 => (zb)).
    { apply IHe2. intros. apply H. apply (Z.of_nat 42). apply v_And. auto. auto. }
    auto.
  - intros. inversion H0. assert (lH: [|e1|] s2 => (za)).
    { apply IHe1. intros. apply H. apply (Z.of_nat 42). apply v_Or. auto. auto. }
    assert (rH: [|e2|] s2 => (zb)).
    { apply IHe2. intros. apply H. apply (Z.of_nat 42). apply v_Or. auto. auto. }
    auto.
Qed.

(* Semantic equivalence *)
Reserved Notation "e1 '~~' e2" (at level 42, no associativity).

Inductive equivalent: expr -> expr -> Prop := 
  eq_intro : forall (e1 e2 : expr), 
               (forall (n : Z) (s : state Z), 
                 [| e1 |] s => n <-> [| e2 |] s => n
               ) -> e1 ~~ e2
where "e1 '~~' e2" := (equivalent e1 e2).

(* Semantic equivalence is an equivalence relation *)
Lemma eq_refl: forall (e : expr), e ~~ e.
Proof.
  intros. apply eq_intro. intros. split. auto. auto. Qed.

Lemma eq_symm: forall (e1 e2 : expr), e1 ~~ e2 -> e2 ~~ e1.
Proof.
  intros. inversion H. apply eq_intro. intros. split.
  - intros. apply H0. auto.
  - intros. apply H0. auto.
Qed.

Lemma eq_trans: forall (e1 e2 e3 : expr), e1 ~~ e2 -> e2 ~~ e3 -> e1 ~~ e3.
Proof.
  intros. inversion H. inversion H0. apply eq_intro. intros. split.
  + intros. apply H4. apply H1. auto.
  + intros. apply H1. apply H4. auto.
Qed.

(* Contexts *)
Inductive Context : Type :=
  | Hole : Context
  | AddL : Context -> expr -> Context
  | SubL : Context -> expr -> Context
  | MulL : Context -> expr -> Context
  | DivL : Context -> expr -> Context
  | ModL : Context -> expr -> Context
  | LeL  : Context -> expr -> Context
  | LtL  : Context -> expr -> Context
  | GeL  : Context -> expr -> Context
  | GtL  : Context -> expr -> Context
  | EqL  : Context -> expr -> Context
  | NeL  : Context -> expr -> Context
  | AndL : Context -> expr -> Context
  | OrL  : Context -> expr -> Context
  | AddR : expr -> Context -> Context
  | SubR : expr -> Context -> Context
  | MulR : expr -> Context -> Context
  | DivR : expr -> Context -> Context
  | ModR : expr -> Context -> Context
  | LeR  : expr -> Context -> Context
  | LtR  : expr -> Context -> Context
  | GeR  : expr -> Context -> Context
  | GtR  : expr -> Context -> Context
  | EqR  : expr -> Context -> Context
  | NeR  : expr -> Context -> Context
  | AndR : expr -> Context -> Context
  | OrR  : expr -> Context -> Context.

(* Plugging an expression into a context *)
Fixpoint plug (C : Context) (e : expr) : expr := 
  match C with
  | Hole => e
  | AddL C e1 => Add (plug C e) e1
  | SubL C e1 => Sub (plug C e) e1
  | MulL C e1 => Mul (plug C e) e1
  | DivL C e1 => Div (plug C e) e1
  | ModL C e1 => Mod (plug C e) e1
  | LeL  C e1 => Le  (plug C e) e1
  | LtL  C e1 => Lt  (plug C e) e1
  | GeL  C e1 => Ge  (plug C e) e1
  | GtL  C e1 => Gt  (plug C e) e1
  | EqL  C e1 => Eq  (plug C e) e1
  | NeL  C e1 => Ne  (plug C e) e1
  | AndL C e1 => And (plug C e) e1
  | OrL  C e1 => Or  (plug C e) e1
  | AddR e1 C => Add e1 (plug C e)
  | SubR e1 C => Sub e1 (plug C e)
  | MulR e1 C => Mul e1 (plug C e)
  | DivR e1 C => Div e1 (plug C e)
  | ModR e1 C => Mod e1 (plug C e)
  | LeR  e1 C => Le  e1 (plug C e)
  | LtR  e1 C => Lt  e1 (plug C e)
  | GeR  e1 C => Ge  e1 (plug C e)
  | GtR  e1 C => Gt  e1 (plug C e)
  | EqR  e1 C => Eq  e1 (plug C e)
  | NeR  e1 C => Ne  e1 (plug C e)
  | AndR e1 C => And e1 (plug C e)
  | OrR  e1 C => Or  e1 (plug C e)
  end.

Notation "C '<~' e" := (plug C e) (at level 43, no associativity).

(* Contextual equivalence *)
Reserved Notation "e1 '~c~' e2" (at level 42, no associativity).

Inductive contextual_equivalent: expr -> expr -> Prop :=
  ceq_intro : forall (e1 e2 : expr),
                (forall (C : Context), (C <~ e1) ~~ (C <~ e2)) -> e1 ~c~ e2
where "e1 '~c~' e2" := (contextual_equivalent e1 e2).

(* Contextual equivalence is equivalent to the semantic one *)
Lemma eq_eq_ceq: forall (e1 e2 : expr), e1 ~~ e2 <-> e1 ~c~ e2.
Proof.
  intros. split.
  - intros. inversion H. apply ceq_intro. intros. apply eq_intro. intros.
    assert (T: forall (C : Context) (e1 e2 : expr) (s : state Z) (n : Z),
                  (forall (m : Z) (s' : state Z), [|e1|] s' => (m) -> [|e2|] s' => (m)) ->
                  [|C <~ e1|] s => (n) -> [|C <~ e2|] s => (n) ).
    { clear. intros C. induction C.
      - simpl. intros. auto.
      - simpl. intros. inversion H0. remember (IHC e1 e2 s za H H3). auto.
      - simpl. intros. inversion H0. remember (IHC e1 e2 s za H H3). auto.
      - simpl. intros. inversion H0. remember (IHC e1 e2 s za H H3). auto.
      - simpl. intros. inversion H0. remember (IHC e1 e2 s za H H3). auto.
      - simpl. intros. inversion H0. remember (IHC e1 e2 s za H H3). auto.
      - simpl. intros. inversion H0.
        + remember (IHC e1 e2 s za H H3). apply bs_Le_T with za zb. auto. auto. auto.
        + remember (IHC e1 e2 s za H H3). apply bs_Le_F with za zb. auto. auto. auto.
      - simpl. intros. inversion H0.
        + remember (IHC e1 e2 s za H H3). apply bs_Lt_T with za zb. auto. auto. auto.
        + remember (IHC e1 e2 s za H H3). apply bs_Lt_F with za zb. auto. auto. auto.
      - simpl. intros. inversion H0.
        + remember (IHC e1 e2 s za H H3). apply bs_Ge_T with za zb. auto. auto. auto.
        + remember (IHC e1 e2 s za H H3). apply bs_Ge_F with za zb. auto. auto. auto.
      - simpl. intros. inversion H0.
        + remember (IHC e1 e2 s za H H3). apply bs_Gt_T with za zb. auto. auto. auto.
        + remember (IHC e1 e2 s za H H3). apply bs_Gt_F with za zb. auto. auto. auto.
      - simpl. intros. inversion H0.
        + remember (IHC e1 e2 s za H H3). apply bs_Eq_T with za zb. auto. auto. auto.
        + remember (IHC e1 e2 s za H H3). apply bs_Eq_F with za zb. auto. auto. auto.
      - simpl. intros. inversion H0.
        + remember (IHC e1 e2 s za H H3). apply bs_Ne_T with za zb. auto. auto. auto.
        + remember (IHC e1 e2 s za H H3). apply bs_Ne_F with za zb. auto. auto. auto.
      - simpl. intros. inversion H0. remember (IHC e1 e2 s za H H3). auto.
      - simpl. intros. inversion H0. remember (IHC e1 e2 s za H H3). auto.
      - simpl. intros. inversion H0. remember (IHC e1 e2 s zb H H6). auto.
      - simpl. intros. inversion H0. remember (IHC e1 e2 s zb H H6). auto.
      - simpl. intros. inversion H0. remember (IHC e1 e2 s zb H H6). auto.
      - simpl. intros. inversion H0. remember (IHC e1 e2 s zb H H6). auto.
      - simpl. intros. inversion H0. remember (IHC e1 e2 s zb H H6). auto.
      - simpl. intros. inversion H0.
        + remember (IHC e1 e2 s zb H H4). apply bs_Le_T with za zb. auto. auto. auto.
        + remember (IHC e1 e2 s zb H H4). apply bs_Le_F with za zb. auto. auto. auto.
      - simpl. intros. inversion H0.
        + remember (IHC e1 e2 s zb H H4). apply bs_Lt_T with za zb. auto. auto. auto.
        + remember (IHC e1 e2 s zb H H4). apply bs_Lt_F with za zb. auto. auto. auto.
      - simpl. intros. inversion H0.
        + remember (IHC e1 e2 s zb H H4). apply bs_Ge_T with za zb. auto. auto. auto.
        + remember (IHC e1 e2 s zb H H4). apply bs_Ge_F with za zb. auto. auto. auto.
      - simpl. intros. inversion H0.
        + remember (IHC e1 e2 s zb H H4). apply bs_Gt_T with za zb. auto. auto. auto.
        + remember (IHC e1 e2 s zb H H4). apply bs_Gt_F with za zb. auto. auto. auto.
      - simpl. intros. inversion H0.
        + remember (IHC e1 e2 s zb H H4). apply bs_Eq_T with za zb. auto. auto. auto.
        + remember (IHC e1 e2 s zb H H4). apply bs_Eq_F with za zb. auto. auto. auto.
      - simpl. intros. inversion H0.
        + remember (IHC e1 e2 s zb H H4). apply bs_Ne_T with za zb. auto. auto. auto.
        + remember (IHC e1 e2 s zb H H4). apply bs_Ne_F with za zb. auto. auto. auto.
      - simpl. intros. inversion H0. remember (IHC e1 e2 s zb H H4). auto.
      - simpl. intros. inversion H0. remember (IHC e1 e2 s zb H H4). auto. }
    split.
    + intros. apply T with e1. intros. apply H0. auto. auto.
    + intros. apply T with e2. intros. apply H0. auto. auto.
  - intros. inversion H. remember (H0 Hole). auto.
Qed.
