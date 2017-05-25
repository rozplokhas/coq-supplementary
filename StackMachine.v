Require Import List.
Import ListNotations.
Require Import Omega.

Require Export BigZ.
Require Export Id.
Require Export State.
Require Export Expr.

(* Sublist *)
Fixpoint suffix (A : Type) (p : list A) (n : nat) :=
  match n with
  | 0   => p
  | S k => match p with [] => [] | h :: tl => h :: suffix A tl k end
  end.

(* Stack machine instructions *)
Inductive insn : Type :=
| R  : insn
| W  : insn
| L  : id -> insn
| S  : id -> insn
| B  : bop -> insn
| C  : nat -> insn
| J  : nat -> insn
| JT : nat -> insn
| JF : nat -> insn.

(* Program *)
Definition prog := list insn.

(* Subprogram *)
Notation "p '<[' k ']>'" := (suffix insn p k) (at level 0, no associativity).

Definition subprogram p k n := firstn n p<[k]>.

Notation "p '<[' k ':' n ]>" := (subprogram p k n) (at level 39, no associativity).

(* Configuration *)
Definition conf := (list Z * state Z * list Z * list Z)%type.

(* Big-step evaluation relation *)
Reserved Notation "p '|-' c1 '--' q '-->' c2" (at level 0).
Notation "st [ x '<-' y ]" := (update Z st x y) (at level 0).

Inductive sm_int : prog -> conf -> prog -> conf -> Prop :=
| sm_End   : forall (p : prog) (c : conf), p |- c -- [] --> c
| sm_Read  : forall (p q : prog) (z : Z) (m : state Z) (s i o : list Z) (c' : conf), 
               p |- (z::s, m, i, o) -- q --> c' -> p |- (s, m, z::i, o) -- R::q --> c'
| sm_Write : forall (p q : prog) (z : Z) (m : state Z) (s i o : list Z) (c' : conf), 
               p |- (s, m, i, z::o) -- q --> c' -> p |- (z::s, m, i, o) -- W::q --> c'
| sm_Load  : forall (p q : prog) (x : id) (z : Z) (m : state Z) (s i o : list Z) (c' : conf), 
               m / x => z -> p |- (z::s, m, i, o) -- q --> c' -> p |- (s, m, i, o) -- (L x)::q --> c'
| sm_Store : forall (p q : prog) (x : id) (z : Z) (m : state Z) (s i o : list Z) (c' : conf), 
               p |- (s, m [x <- z], i, o) -- q --> c' -> p |- (z::s, m, i, o) -- (S x)::q --> c'
| sm_Add   : forall (p q : prog) (x y : Z) (m : state Z) (s i o : list Z) (c' : conf), 
               p |- ((x + y)%Z::s, m, i, o) -- q --> c' -> p |- (y::x::s, m, i, o) -- (B Add)::q --> c'
| sm_Sub   : forall (p q : prog) (x y : Z) (m : state Z) (s i o : list Z) (c' : conf), 
               p |- ((x - y)%Z::s, m, i, o) -- q --> c' -> p |- (y::x::s, m, i, o) -- (B Sub)::q --> c'
| sm_Mul   : forall (p q : prog) (x y : Z) (m : state Z) (s i o : list Z) (c' : conf), 
               p |- ((x * y)%Z::s, m, i, o) -- q --> c' -> p |- (y::x::s, m, i, o) -- (B Mul)::q --> c'
| sm_Div   : forall (p q : prog) (x y : Z) (m : state Z) (s i o : list Z) (c' : conf), 
               p |- ((Z.div x y)::s, m, i, o) -- q --> c' -> p |- (y::x::s, m, i, o) -- (B Div)::q --> c'
| sm_Mod   : forall (p q : prog) (x y : Z) (m : state Z) (s i o : list Z) (c' : conf), 
               p |- ((Z.modulo x y)::s, m, i, o) -- q --> c' -> p |- (y::x::s, m, i, o) -- (B Mod)::q --> c'
| sm_Le_T  : forall (p q : prog) (x y : Z) (m : state Z) (s i o : list Z) (c' : conf), 
               Z.le x y -> p |- (Z.one::s, m, i, o) -- q --> c' -> p |- (y::x::s, m, i, o) -- (B Le)::q --> c'
| sm_Le_F  : forall (p q : prog) (x y : Z) (m : state Z) (s i o : list Z) (c' : conf), 
               Z.gt x y -> p |- (Z.zero::s, m, i, o) -- q --> c' -> p |- (y::x::s, m, i, o) -- (B Le)::q --> c'
| sm_Ge_T  : forall (p q : prog) (x y : Z) (m : state Z) (s i o : list Z) (c' : conf), 
               Z.ge x y -> p |- (Z.one::s, m, i, o) -- q --> c' -> p |- (y::x::s, m, i, o) -- (B Ge)::q --> c'
| sm_Ge_F  : forall (p q : prog) (x y : Z) (m : state Z) (s i o : list Z) (c' : conf), 
               Z.lt x y -> p |- (Z.zero::s, m, i, o) -- q --> c' -> p |- (y::x::s, m, i, o) -- (B Ge)::q --> c'
| sm_Lt_T  : forall (p q : prog) (x y : Z) (m : state Z) (s i o : list Z) (c' : conf), 
               Z.lt x y -> p |- (Z.one::s, m, i, o) -- q --> c' -> p |- (y::x::s, m, i, o) -- (B Lt)::q --> c'
| sm_Lt_F  : forall (p q : prog) (x y : Z) (m : state Z) (s i o : list Z) (c' : conf), 
               Z.ge x y -> p |- (Z.zero::s, m, i, o) -- q --> c' -> p |- (y::x::s, m, i, o) -- (B Lt)::q --> c'
| sm_Gt_T  : forall (p q : prog) (x y : Z) (m : state Z) (s i o : list Z) (c' : conf), 
               Z.gt x y -> p |- (Z.one::s, m, i, o) -- q --> c' -> p |- (y::x::s, m, i, o) -- (B Gt)::q --> c'
| sm_Gt_F  : forall (p q : prog) (x y : Z) (m : state Z) (s i o : list Z) (c' : conf), 
               Z.le x y -> p |- (Z.zero::s, m, i, o) -- q --> c' -> p |- (y::x::s, m, i, o) -- (B Gt)::q --> c'
| sm_Eq_T  : forall (p q : prog) (x y : Z) (m : state Z) (s i o : list Z) (c' : conf), 
               Z.eq x y -> p |- (Z.one::s, m, i, o) -- q --> c' -> p |- (y::x::s, m, i, o) -- (B Eq)::q --> c'
| sm_Eq_F  : forall (p q : prog) (x y : Z) (m : state Z) (s i o : list Z) (c' : conf), 
               ~ Z.eq x y -> p |- (Z.zero::s, m, i, o) -- q --> c' -> p |- (y::x::s, m, i, o) -- (B Eq)::q --> c'
| sm_Ne_T  : forall (p q : prog) (x y : Z) (m : state Z) (s i o : list Z) (c' : conf), 
               ~ Z.eq x y -> p |- (Z.one::s, m, i, o) -- q --> c' -> p |- (y::x::s, m, i, o) -- (B Ne)::q --> c'
| sm_Ne_F  : forall (p q : prog) (x y : Z) (m : state Z) (s i o : list Z) (c' : conf), 
               Z.eq x y -> p |- (Z.zero::s, m, i, o) -- q --> c' -> p |- (y::x::s, m, i, o) -- (B Ne)::q --> c'
| sm_And   : forall (p q : prog) (x y : Z) (m : state Z) (s i o : list Z) (c' : conf), 
               zbool x -> zbool y -> p |- ((x * y)%Z::s, m, i, o) -- q --> c' -> p |- (y::x::s, m, i, o) -- (B And)::q --> c'
| sm_Or    : forall (p q : prog) (x y : Z) (m : state Z) (s i o : list Z) (c' : conf), 
               zbool x -> zbool y -> p |- ((zor x y)::s, m, i, o) -- q --> c' -> p |- (y::x::s, m, i, o) -- (B Or)::q --> c'
| sm_Const : forall (p q : prog) (n : nat) (m : state Z) (s i o : list Z) (c' : conf), 
               p |- ((Z.of_nat n)::s, m, i, o) -- q --> c' -> p |- (s, m, i, o) -- (C n)::q --> c'
| sm_J     : forall (p q : prog) (n : nat) (c c' : conf), 
               p |- c -- p<[n]> --> c' -> p |- c -- (J n)::q --> c'
| sm_JT_T  : forall (p q : prog) (n : nat) (m : state Z) (s i o : list Z) (c' : conf), 
               p |- (s, m, i, o) -- p<[n]> --> c' -> p |- (Z.one::s, m, i, o) -- (JT n)::q --> c'
| sm_JT_F  : forall (p q : prog) (n : nat) (m : state Z) (s i o : list Z) (c' : conf), 
               p |- (s, m, i, o) -- q --> c' -> p |- (Z.zero::s, m, i, o) -- (JT n)::q --> c'
| sm_JF_T  : forall (p q : prog) (n : nat) (m : state Z) (s i o : list Z) (c' : conf), 
               p |- (s, m, i, o) -- q --> c' -> p |- (Z.one::s, m, i, o) -- (JT n)::q --> c'
| sm_JF_F  : forall (p q : prog) (n : nat) (m : state Z) (s i o : list Z) (c' : conf), 
               p |- (s, m, i, o) -- p<[n]> --> c' -> p |- (Z.zero::s, m, i, o) -- (JT n)::q --> c'
where "p '|-' c1 '--' q '-->' c2" := (sm_int p c1 q c2).

(* Expression compiler *)
Fixpoint compile_expr (e : expr) :=
  match e with
  | Var  x       => [L x]
  | Nat  n       => [C n]
  | Bop op e1 e2 => compile_expr e1 ++ compile_expr e2 ++ [B op]
  end.

(* Partial correctness of expression compiler *)
Lemma compiled_expr_correct: forall (e : expr) (st : state Z) (s i o : list Z) (n : Z),
                               [| e |] st => n -> (compile_expr e) |- (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o).
Proof. admit. Admitted.