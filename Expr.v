Add LoadPath "~/AU/Coq/coq-supplementary".

Require Export BigZ.
Require Export Id.
Require Export State.

(* Type of binary operators *)
Inductive bop : Type :=
| Add : bop
| Sub : bop
| Mul : bop
| Div : bop
| Mod : bop
| Le  : bop
| Lt  : bop
| Ge  : bop
| Gt  : bop
| Eq  : bop
| Ne  : bop
| And : bop
| Or  : bop.

Definition zbool (x : Z) : Prop := x = Z.one \/ x = Z.zero.

Inductive bop_eval : bop -> Z -> Z -> Z -> Prop :=
  bop_Add : forall (za zb : Z), bop_eval Add za zb (za + zb)
| bop_Sub : forall (za zb : Z), bop_eval Sub za zb (za - zb)
| bop_Mul : forall (za zb : Z), bop_eval Mul za zb (za * zb)
| bop_Div : forall (za zb : Z), bop_eval Div za zb (Z.div za zb)
| bop_Mod : forall (za zb : Z), bop_eval Mod za zb (Z.modulo za zb)
| bop_Le_T : forall (za zb : Z), Z.le za zb -> bop_eval Le za zb Z.one
| bop_Le_F : forall (za zb : Z), Z.gt za zb -> bop_eval Le za zb Z.zero
| bop_Lt_T : forall (za zb : Z), Z.lt za zb -> bop_eval Lt za zb Z.one
| bop_Lt_F : forall (za zb : Z), Z.ge za zb -> bop_eval Lt za zb Z.zero
| bop_Ge_T : forall (za zb : Z), Z.ge za zb -> bop_eval Ge za zb Z.one
| bop_Ge_F : forall (za zb : Z), Z.lt za zb -> bop_eval Ge za zb Z.zero
| bop_Gt_T : forall (za zb : Z), Z.gt za zb -> bop_eval Gt za zb Z.one
| bop_Gt_F : forall (za zb : Z), Z.le za zb -> bop_eval Gt za zb Z.zero
| bop_Eq_T : forall (za zb : Z), Z.eq za zb -> bop_eval Eq za zb Z.one
| bop_Eq_F : forall (za zb : Z), ~ Z.eq za zb -> bop_eval Eq za zb Z.zero
| bop_Ne_T : forall (za zb : Z), ~ Z.eq za zb -> bop_eval Ne za zb Z.one
| bop_Ne_F : forall (za zb : Z), Z.eq za zb -> bop_eval Ne za zb Z.zero
| bop_And : forall (za zb : Z), zbool za -> zbool zb -> bop_eval And za zb (za * zb)
| bop_Or : forall (za zb : Z), zbool za -> zbool zb -> bop_eval Or za zb (1 - (1 - za) * (1 - zb)).

(* Type of arithmetic expressions *)
Inductive expr : Type :=
(* | Nat : nat -> expr *)
| Const : Z -> expr
| Var : id  -> expr
| Bop : bop -> expr -> expr -> expr.

(* Supplementary notation *)
Notation "x '[+]'  y" := (Bop Add x y) (at level 40, left associativity).
Notation "x '[-]'  y" := (Bop Sub x y) (at level 40, left associativity).
Notation "x '[*]'  y" := (Bop Mul x y) (at level 41, left associativity).
Notation "x '[/]'  y" := (Bop Div x y) (at level 41, left associativity).
Notation "x '[%]'  y" := (Bop Mod x y) (at level 41, left associativity).
Notation "x '[<=]' y" := (Bop Le  x y) (at level 39, no associativity).
Notation "x '[<]'  y" := (Bop Lt  x y) (at level 39, no associativity).
Notation "x '[>=]' y" := (Bop Ge  x y) (at level 39, no associativity).
Notation "x '[>]'  y" := (Bop Gt  x y) (at level 39, no associativity).
Notation "x '[==]' y" := (Bop Eq  x y) (at level 39, no associativity).
Notation "x '[/=]' y" := (Bop Ne  x y) (at level 39, no associativity).
Notation "x '[&]'  y" := (Bop And x y) (at level 38, left associativity).
Notation "x '[\/]' y" := (Bop Or  x y) (at level 38, left associativity).

Reserved Notation "[| e |] st => z" (at level 0).
Notation "st / x => y" := (st_binds Z st x y) (at level 0).

(* Big-step evaluation relation *)
Inductive bs_eval : expr -> state Z -> Z -> Prop :=
(*  bs_Nat  : forall (s : state Z) (n : nat), [| Nat n |] s => (Z.of_nat n) *)
  bs_Const  : forall (s : state Z) (z : Z), [| Const z |] s => z
| bs_Var  : forall (s : state Z) (i : id) (z : Z), s / i => z -> [| Var i |] s => z
| bs_Bop  : forall (s : state Z) (op : bop) (a b : expr) (za zb zr : Z),
             [| a |] s => za -> [| b |] s => zb -> bop_eval op za zb zr -> [| Bop op a b |] s => zr
where "[| e |] st => z" := (bs_eval e st z).

Hint Constructors bs_eval.

Module SmokeTest.

  Lemma nat_always :
    (* forall (n : nat) (s : state Z), [| Nat n |] s => (Z.of_nat n). *)
    forall (z : Z) (s : state Z), [| Const z |] s => z.
  Proof. auto. Qed.

  Lemma double_and_sum : 
    forall (s : state Z) (e : expr) (z : Z),
      (* [| e [*] (Nat 2) |] s => z -> [| e [+] e |] s => z. *)
      [| e [*] (Const 2) |] s => z -> [| e [+] e |] s => z.
  Proof.
    intros s e z H. inversion_clear H. inversion_clear H2. inversion_clear H1.
    econstructor.
    - eassumption.
    - eassumption.
    - (* replace (Z.mul za (Z.of_nat 2)) with (Z.add za za). *)
      replace (Z.mul za 2) with (Z.add za za).
      + constructor.
      + simpl. omega.
  Qed.

End SmokeTest.

Reserved Notation "x ? e" (at level 0).

(* Set of variables is an expression *)
Inductive V : expr -> id -> Prop := 
  v_Var : forall (id : id), id ? (Var id)
| v_Bop : forall (id : id) (a b : expr) (op : bop), id ? a \/ id ? b -> id ? (Bop op a b)
where "x ? e" := (V e x).

Ltac destruct_disj :=
  match goal with 
  | H: (_ \/ _) |- _ => destruct H
  end.

(* If an expression is defined in some state, then each its' variable is
   defined in that state
*)
Lemma defined_expression: forall (e : expr) (s : state Z) (z : Z) (id : id),
  [| e |] s => z -> id ? e -> exists z', s / id => z'.
Proof.
  intros e s z id H; induction H;
  intros H'; inversion H'; solve
  [ exists z; rewrite <- H0; apply H
  | destruct_disj; auto ].
Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable: forall (e : expr) (s : state Z) (id : id),
  id ? e -> (forall (z : Z), ~ (s / id => z)) -> (forall (z : Z), ~ ([| e |] s => z)).
Proof.
  unfold not; intros e s id; induction e; solve
  [ intros H; inversion H
  | intros iH; inversion iH; intros nH z H; inversion H;
    remember (nH z) as contra; contradiction
  | intros; inversion H1; inversion H; destruct_disj;
    [ apply IHe1 with (z := za); auto
    | apply IHe2 with (z := zb); auto ]
  | intros; inversion H1;
    inversion H; destruct_disj; solve
    [ apply IHe1 with (z := za); auto
    | apply IHe2 with (z := zb); auto ] ].
Qed.

(* The evaluation relation is deterministic *)
Lemma bs_eval_deterministic: forall (e : expr) (s : state Z) (z1 z2 : Z),
  [| e |] s => z1 -> [| e |] s => z2 -> z1 = z2.
Proof.
  intros e s; induction e; intros; inversion H; inversion H0.
  - congruence. (* reflexivity. *)
  - eapply state_deterministic; eauto.
  - assert (bop_det: forall (b : bop) (za zb z1 z2 : Z),
        bop_eval b za zb z1 -> bop_eval b za zb z2 -> z1 = z2);
    [ clear; intros; inversion H; solve
      [ match goal with H: (_ = b) |- _ => rewrite <- H in H0 end; inversion H0; reflexivity
      | match goal with H: (_ = b) |- _ => rewrite <- H in H0 end; inversion H0; solve
        [ reflexivity
        | omega 
        | contradiction ] ]
    | eapply bop_det; eauto;
      assert (eq_a: za = za0);
      [ apply IHe1; auto; auto
      | assert (eq_b: zb = zb0);
        [ apply IHe2; auto; auto
        | congruence ] ] ].
Qed.

(* Equivalence of states w.r.t. an identifier *)
Definition equivalent_states (s1 s2 : state Z) (id : id) :=
  forall z :Z, s1 / id => z <-> s2 / id => z.

Ltac inversion_eval :=
  match goal with
  | H: ([| _ |] _ => _) |- _ => inversion_clear H
  end.

(* The result of expression evaluation in a state dependes only on the values
   of occurring variables
*)
Lemma variable_relevance: forall (e : expr) (s1 s2 : state Z) (z : Z),
  (forall (id : id), id ? e -> equivalent_states s1 s2 id) -> 
  [| e |] s1 => z -> [| e |] s2 => z.
Proof.
  intros e s1 s2; induction e.
  - intros. inversion_eval. auto.
  - intros. remember (H i (v_Var i)) as eq. 
    unfold equivalent_states in eq. inversion_eval. constructor.
    destruct (eq z). auto.
  - intros. inversion_eval. econstructor. 
    + apply IHe1.
      * intros.  apply H. constructor. auto.
      * eassumption.
    + apply IHe2.
      * intros.  apply H. constructor. auto.
      * eassumption.
    + assumption.
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
| BopL : bop -> Context -> expr -> Context
| BopR : bop -> expr -> Context -> Context.

(* Plugging an expression into a context *)
Fixpoint plug (C : Context) (e : expr) : expr := 
  match C with
  | Hole => e
  | BopL b C e1 => Bop b (plug C e) e1
  | BopR b e1 C => Bop b (plug C e) e1
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
  intros; split;
  [ intros; constructor; intros C; constructor; inversion_clear H;
    generalize dependent H0; revert e1 e2; induction C; solve
    [ intros; simpl; split;
      ( intros; inversion_clear H; econstructor;
        [ eapply IHC;
          [ intros; solve
            [ eapply (H0 n0 s0)
            | symmetry; eapply (H0 n0 s0) ]
          | eassumption ]
        | eassumption
        | assumption ] )
    | auto ]
  | intros; inversion H; remember (H0 Hole); auto ].
Qed.


(* Small-step semantics *)

Reserved Notation "e -- st --> r" (at level 0).

(* One step reduction relation *)
Inductive ss_step : state Z -> expr -> expr -> Prop :=
| ss_Var    : forall (s : state Z) (i : id) (z : Z), s / i => z -> (Var i) -- s --> (Const z)
| ss_Bop_L  : forall (s : state Z) (op : bop) (a a2 b : expr),
                a -- s --> a2 -> (Bop op a b) -- s --> (Bop op a2 b)
| ss_Bop_R  : forall (s : state Z) (op : bop) (b b2 : expr) (za : Z),
                b -- s --> b2 -> (Bop op (Const za) b) -- s --> (Bop op (Const za) b2)
| ss_Bop_Ev : forall (s : state Z) (op : bop) (za zb zr : Z),
                bop_eval op za zb zr -> (Bop op (Const za) (Const zb)) -- s --> (Const zr)
where "e -- st --> r" := (ss_step st e r).

Reserved Notation "e -- st -->> r" (at level 0).

(* Many step reduction relation *)
Inductive ss_chain : state Z -> expr -> expr -> Prop :=
| ss_Id   : forall (s : state Z) (e : expr), e -- s -->> e
| ss_Step : forall (s : state Z) (e e2 r : expr),
              e -- s --> e2 -> e2 -- s -->> r -> e -- s -->> r
where "e -- st -->> r" := (ss_chain st e r).


Lemma ss_chain_transitivity : forall (s : state Z) (a b c : expr),
  a -- s -->> b -> b -- s -->> c -> a -- s -->> c.
Proof.
  intros. induction H.
  - assumption.
  - econstructor; eauto.
Qed.


Reserved Notation "[| e |] st --> z" (at level 0).

(* Small step evaluation relation *)
Inductive ss_eval : expr -> state Z -> Z -> Prop :=
| ss_Eval : forall (e : expr) (s : state Z) (z : Z), e -- s -->> (Const z) -> [| e |] s --> z
where "[| e |] st --> z" := (ss_eval e st z).


Lemma back_correctness : forall (e e2 : expr) (s : state Z) (z : Z),
  e -- s --> e2 -> [| e2 |] s => z -> [| e |] s => z.
Proof.
  intros e e2 s z H. revert z. induction H.
  - intros. inversion H0. constructor. congruence.
  - intros. inversion_clear H0. econstructor.
    + match goal with H: (_ -> _) |- _ => eapply H end. eassumption.
    + eassumption.
    + assumption.
  - intros. inversion_clear H0. inversion_clear H1. econstructor.
    + econstructor.
    + match goal with H: (_ -> _) |- _ => eapply H end. eassumption.
    + assumption.
  - intros. inversion H0. econstructor.
    + econstructor.
    + econstructor.
    + congruence.
Qed.

Lemma ss_to_bs : forall (e : expr) (s : state Z) (z : Z),
  [| e |] s --> z -> [| e |] s => z.
Proof.
  intros. inversion_clear H. remember (Const z). induction H0.
  - match goal with H: (_ = _) |- _ => rewrite H end. auto.
  - eapply back_correctness. eauto. auto.
Qed.

Lemma bs_to_ss : forall (e : expr) (s : state Z) (z : Z),
  [| e |] s => z -> [| e |] s --> z.
Proof.
  intros e. induction e.
  - intros. inversion_clear H. constructor. constructor.
  - intros. inversion_clear H. constructor. econstructor.
    + econstructor. eassumption.
    + constructor.
  - intros. inversion_clear H. apply IHe1 in H0. apply IHe2 in H1.
    inversion_clear H0. inversion_clear H1.
    assert (L: e1 -- s -->> (Const za) -> (Bop b e1 e2) -- s -->> (Bop b (Const za) e2)).
    { clear. intros H. induction H.
      - constructor.
      - econstructor.
        + eapply ss_Bop_L. eassumption.
        + assumption. }
    apply L in H. clear L.
    assert (R: e2 -- s -->> (Const zb) -> (Bop b (Const za) e2) -- s -->> (Bop b (Const za) (Const zb))).
    { clear. intros H. induction H.
      - constructor.
      - econstructor.
        + eapply ss_Bop_R. eassumption.
        + assumption. }
    apply R in H0. clear R.
    econstructor. eapply ss_chain_transitivity.
    + eassumption.
    + eapply ss_chain_transitivity.
      * eassumption.
      * econstructor.
        { apply ss_Bop_Ev. eassumption. }
        { constructor. }
Qed.
