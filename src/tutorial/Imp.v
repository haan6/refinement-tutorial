From sflib Require Import sflib.
From Paco Require Import paco.
From Tutorial Require Import Refinement.
From Coq Require Import Strings.String List.

Set Implicit Arguments.

(* Reference: Software Foundations Volume 1, Imp.v *)


(** ** A simple memory model for Imp. *)
Module Mem.

  Definition t := nat -> option Z.

  Definition load (m : t) (x : nat) : option Z := (m x).

  Definition store (m : t) (x : nat) (v : Z): t :=
    fun y => if (Nat.eqb x y) then (Some v) else (m y).

  Definition init : t := fun _ => None.

  Variant label : Type :=
    | LLoad (x : nat) (v : Z) : label
    | LStore (x : nat) (v : Z) : label
  .

End Mem.


(** ** A simple register (local environment) for Imp. *)
Module Reg.

  Definition t := string -> option Z.

  Definition read (r : t) (x : string) : option Z := (r x).

  Definition write (r : t) (x : string) (v : Z): t :=
    fun y => if (String.eqb x y) then (Some v) else (r y).

  Definition init : t := fun _ => None.

End Reg.


(** ** Labels for transitions in Imp. *)
Variant label : Type :=
  | LInternal
  | LExternal (name : string) (args : list Z) (retv : Z)
.

Definition Imp_label := (Mem.label + label)%type.

Definition Imp_Event (ekind : Imp_label -> kind) : Event :=
  mk_event ekind.


(** ** Expressions - syntax. *)
Variant bin_op : Type :=
  | BOpAdd
  | BOpSub
  | BOpMult.

Inductive aexp : Type :=
| AAny
| ANum (n : Z)
| AId (x : string)
| ABinOp (op : bin_op) (a1 a2 : aexp).


(** ** Expressions - Notations. *)
(* You don't need to understand this part. *)

Coercion AId : string >-> aexp.
Coercion ANum : Z >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.

Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                         (in custom com at level 0, only parsing,
                             f constr at level 0, x constr at level 9,
                             y constr at level 9) : com_scope.
Notation "x + y"   := (ABinOp BOpAdd x y) (in custom com at level 50, left associativity).
Notation "x - y"   := (ABinOp BOpSub x y) (in custom com at level 50, left associativity).
Notation "x * y"   := (ABinOp BOpMult x y) (in custom com at level 40, left associativity).

Open Scope com_scope.


(** ** Expressions - semantics. *)
Reserved Notation " '[' r ',' a ']' '==>' n" (at level 90, left associativity).

Definition bin_op_eval (op : bin_op) (a1 a2 : Z) : Z :=
  match op with
  | BOpAdd => a1 + a2
  | BOpSub => a1 - a2
  | BOpMult => a1 * a2
  end.

Inductive aeval : Reg.t -> aexp -> Z -> Prop :=
| E_Any r (n : Z) :
  [r, AAny] ==> n
| E_ANum r (n : Z) :
  [r, n] ==> n
| E_AId r (x : string) :
  forall v, (r x = Some v) -> [r, x] ==> v
| E_ABinOp r (op: bin_op) (a1 a2 : aexp) (n1 n2 : Z) :
  ([r, a1] ==> n1) -> ([r, a2] ==> n2) -> [r, ABinOp op a1 a2] ==> (bin_op_eval op n1 n2)

where " '[' r ',' a ']' '==>' n" := (aeval r a n) : type_scope.


(** ** Commands - syntax. *)
Inductive com : Type :=
| CSkip
| CAsgn (x : string) (a : aexp)
| CSeq (c1 c2 : com)
| CIf (b : aexp) (c1 c2 : com)
| CWhile (b : aexp) (c : com)
| CRet (a: aexp)
| CMemLoad (x : string) (loc : nat)
| CMemStore (l : nat) (a : aexp)
| CExternal (x : string) (name : string) (args : list aexp).


(** ** Commands - notations. *)
(* You don't need to understand this part. *)

Notation "'skip'"  :=
  CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
  (CAsgn x y)
    (in custom com at level 0, x constr at level 0,
        y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
  (CSeq x y)
    (in custom com at level 90,
        right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
  (CIf x y z)
    (in custom com at level 89, x at level 99,
        y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
  (CWhile x y)
    (in custom com at level 89, x at level 99,
        y at level 99) : com_scope.
Notation "'ret' x" :=
  (CRet x)
    (in custom com at level 0,
        x at level 85) : com_scope.
Notation "x := '&<' l '>'" :=
  (CMemLoad x l)
    (in custom com at level 0, x constr at level 0,
        l at level 0, no associativity) : com_scope.
Notation "'&<' l '>' := y" :=
  (CMemStore l y)
    (in custom com at level 0, l at level 0,
        y at level 0, no associativity) : com_scope.
Notation "x ':=@' f '<' a '>'" :=
  (CExternal x f a)
    (in custom com at level 0, x constr at level 0,
        a at level 85, no associativity) : com_scope.

Coercion Z.to_nat : Z >-> nat.


(** ** Commands - semantics. *)
Inductive cont :=
| Kstop : cont
| Kseq : com -> cont -> cont
.

Variant state :=
  | Normal (r : Reg.t) (c : com) (k: cont)
  | Return (v : Z)
  | Undef.

Definition Imp_state := (Mem.t * state)%type.

Reserved Notation
         "st '=(' l ')=>' st'"
         (at level 40, l custom com at level 99,
           st constr, st' constr at next level).

Inductive ceval : Imp_state -> Imp_label -> Imp_state -> Prop :=
| E_Skip : forall m r c k,
    (m, Normal r CSkip (Kseq c k)) =(inr LInternal)=> (m, Normal r c k)
| E_Asgn  : forall m r x a k n,
    aeval r a n ->
    (m, Normal r (CAsgn x a) k) =(inr LInternal)=> (m, Normal (Reg.write r x n) CSkip k)
| E_Seq : forall m r c1 c2 k,
    (m, Normal r (CSeq c1 c2) k) =(inr LInternal)=> (m, Normal r c1 (Kseq c2 k))
| E_IfTrue : forall m r b c1 c2 k n,
    aeval r b n ->
    n <> 0 ->
    (m, Normal r (CIf b c1 c2) k) =(inr LInternal)=> (m, Normal r c1 k)
| E_IfFalse : forall m r b c1 c2 k n,
    aeval r b n ->
    n = 0 ->
    (m, Normal r (CIf b c1 c2) k) =(inr LInternal)=> (m, Normal r c1 k)
| E_WhileFalse : forall m r b c k n,
    aeval r b n ->
    n = 0 ->
    (m, Normal r (CWhile b c) k) =(inr LInternal)=> (m, Normal r CSkip k)
| E_WhileTrue : forall m r b c k n,
    aeval r b n ->
    n <> 0 ->
    (m, Normal r (CWhile b c) k) =(inr LInternal)=> (m, Normal r c (Kseq (CWhile b c) k))
| E_Ret : forall m r a k retv,
    aeval r a retv ->
    (m, Normal r (CRet a) k) =(inr LInternal)=> (m, Return retv)
| E_MemLoad : forall m r x loc k v,
    Mem.load m loc = Some v ->
    (m, Normal r (CMemLoad x loc) k) =(inl (Mem.LLoad loc v))=> (m, Normal (Reg.write r x v) CSkip k)
| E_MemStore : forall m r loc a k v m',
    aeval r a v ->
    Mem.store m loc v = m' ->
    (m, Normal r (CMemStore loc a) k) =(inl (Mem.LStore loc v))=> (m', Normal r CSkip k)
| E_External : forall m r x name eargs k vargs retv,
    Forall2 (aeval r) eargs vargs ->
    (m, Normal r (CExternal x name eargs) k) =(inr (LExternal name vargs retv))=> (m, Normal (Reg.write r x retv) CSkip k)

where "st =( l )=> st'" := (ceval st l st').

Variant step : Imp_state -> Imp_label -> Imp_state -> Prop :=
  | Step_normal
      st e st'
      (STEP: st =(e)=> st')
    :
    step st e st'
  | Step_undefined
      m lst
      (UNDEF: forall e st', ~ ((m, lst) =(e)=> st'))
    :
    step (m, lst) (inr LInternal) (m, Undef).

Definition Imp_init (c : com) : Imp_state := (Mem.init, Normal Reg.init c Kstop).


(** ** Imp - STS. *)
Definition Imp_sort (s : Imp_state) : sort :=
  match s with
  | (_, Normal _ _ _) => normal
  | (_, Return v) => final v
  | (_, Undef) => undef
  end.

Definition Imp_STS (ekind : Imp_label -> kind) (c : com) : STS :=
  mk_sts (Imp_Event ekind) (Imp_init c) ceval Imp_sort.

Definition ekind_memory (l : Imp_label) : kind :=
  match l with
  | inl _ => observableE
  | inr e => match e with
            | LInternal => silentE
            | LExternal _ _ _ => observableE
            end
  end.

Definition ekind_external (l : Imp_label) : kind :=
  match l with
  | inl _ => silentE
  | inr e => match e with
            | LInternal => silentE
            | LExternal _ _ _ => observableE
            end
  end.

Definition Imp_STS1 c : STS := Imp_STS ekind_memory c.
Definition Imp_STS2 c : STS := Imp_STS ekind_external c.
