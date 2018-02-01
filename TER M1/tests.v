Require Import notations.

Set Implicit Arguments.
Set Strict Implicit.
Set Asymmetric Patterns.
Set Universe Polymorphism.
Set Printing Universes.


(** Core Type and Functions **)
Section hlist.
  Polymorphic Universe Ui Uv.

  Context {iT : Type@{Ui}}.
  Variable F : iT -> Type@{Uv}.

  Inductive hlist : list iT -> Type :=
  | Hnil  : hlist nil
  | Hcons : forall l ls, F l -> hlist ls -> hlist (l :: ls).

  Local Open Scope list_scope.

  Definition hlist_hd {a b} (hl : hlist (a :: b)) : F a :=
    match hl in hlist x return match x with
                               | nil => unit
                               | l :: _ => F l
                               end with
    | Hnil => tt
    | Hcons _ _ x _ => x
    end.

  Definition hlist_tl {a b} (hl : hlist (a :: b)) : hlist b :=
    match hl in hlist x return match x with
                                 | nil => unit
                                 | _ :: ls => hlist ls
                               end with
      | Hnil => tt
      | Hcons _ _ _ x => x
    end.

  Lemma hlist_eta : forall ls (h : hlist ls),
    h = match ls as ls return hlist ls -> hlist ls with
          | nil => fun _ => Hnil
          | a :: b => fun h => Hcons (hlist_hd h) (hlist_tl h)
        end h.
  Proof.
    intros. destruct h; auto.
  Qed.

  Fixpoint hlist_app ll lr (h : hlist ll) : hlist lr -> hlist (ll ++ lr) :=
    match h in hlist ll return hlist lr -> hlist (ll ++ lr) with
      | Hnil => fun x => x
      | Hcons _ _ hd tl => fun r => Hcons hd (hlist_app tl r)
    end.

End hlist.

Arguments Hnil {_ _}.
Arguments Hcons {_ _ _ _} _ _.

Eval compute in Hcons true  Hnil.

Section hlist.

Inductive hlist (A:Type): list A -> Type :=
| HNil : hlist A nil
| HCons : forall (x:A)(ls:list A), F x -> hlist A ls -> hlist A (x::ls).

(* Implicit Arguments hlist [A F]. *)
Implicit Arguments HCons [A F x ls].
Implicit Arguments HNil [A F].
Print hlist.

Open Scope list_scope.
Eval compute in HCons true HNil.

Definition someTypes : list Set := nat :: nil.
Example someValues : hlist (Set) (fun T : Set => T) someTypes := 
HCons 2 HNil.
Example someValues : hlist (Set) (fun T : Set => T) someTypes := 
HCons 2 (HCons true nil nil HNil).

Eval compute in HCons true  HNil.
Eval compute in HCons 2 (HCons true (HNil)).

Variable A : Type.
Variable B : A -> Type.

Inductive hlist : list A -> Type :=
| HNil : hlist nil
| HCons : forall (x:A)(ls:list A), B x -> hlist ls -> hlist (x::ls).
  
Variable elm: A.

Inductive member : list A -> Type :=
| HFirst : forall ls, member (elm :: ls)
| HNext : forall x ls, member ls -> member (x :: ls).
Print HNil.
(*
Arguments HNil [A B].
Implicit Arguments HCons [ A B x ls ]. *)
Open Scope list_scope.

Print hlist.
Implicit Arguments hlist [A].

Definition someTypes : list Set := nat :: bool :: nil.
Example someValues : hlist (fun T : Set => T) someTypes.
Print HCons.

Implicit Arguments HCons [x ls (B x)].
Print HCons.

Definition test : nat -> nat := fun x => 2.

Eval compute in HCons test 2 (HCons true (HNil)).
Implicit Arguments HCons [A B x ls].

Example someValues : hlist someTypes := HCons 2 (HCons true (HNil)).
Eval compute in HCons 2 (HCons true (HNil)).

End hlist.