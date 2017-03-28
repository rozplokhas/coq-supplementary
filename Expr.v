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
