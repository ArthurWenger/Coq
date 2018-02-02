Require Import notations.
Require Import option.
Require Import String.

Import ListNotations.
Local Open Scope list_scope.

Section list_prob.
Variable A:Type. (* a changer / modifier *)

Fixpoint last {A:Type}(l:list A): option :=
    match l with
    | nil => None
    | x :: nil => Some x
    | x :: y => last y
    end. 

Fixpoint last_but_one {A:Type}(l:list A): option :=
    match l with
    | nil => None
    | x :: y :: nil => Some x
    | x :: y => last_but_one y
    end.

(* en commencant la notation à 0 *)
Fixpoint element_at {A:Type}(l:list A)(n: nat): option :=
    match n, l with
    | _, nil => None
    | O, x :: y => Some x
    | S n', x :: y => element_at y n'
    end.

(* en commencant la notation à 1 *)
Fixpoint element_at_bis {A:Type}(l:list A)(n: nat): option :=
    match n, l with
    | _, nil => None
    | O, _ => None
    | S O, x :: y => Some x
    | S n', x :: y => element_at_bis y n'
    end.

Fixpoint card_list {A:Type}(l:list A): nat :=
    match l with
    | nil => O
    | x :: y => S (card_list y)
    end.

Fixpoint rev_list {A:Type}(l:list A): list A :=
    match l with
    | nil => nil
    | x :: y =>  rev_list y ++ [ x ]
    end.

(* sans utiliser ++ *)
Fixpoint rev_list_bis {A:Type}(l:list A): list A :=
    (fix sub(l l':list A): list A :=
    match l with
    | nil => l'
    | x :: y =>  sub y (x :: l')
    end) l nil.

Hypothesis A_dec : forall x y:A, {x = y} + {x <> y}.

Fixpoint equal_lists (l l':list A): bool :=
match l, l' with
| nil, nil => true
| x :: y, x' :: y' => match A_dec x x' with
                      | left _ => equal_lists y y'
                      | right _ => false
                      end
| _, _ => false 
end.

Definition is_palindrome (l:list A): bool :=
    equal_lists l (rev_list l).


(*
Variable B : Type.
Variable F : B -> Type.

Inductive hlist : list B -> Type :=
| Hnil : hlist nil
| Hcons : forall (x:B)(ls:list B), F x -> hlist ls -> hlist (x::ls).

(* DefinBion hlist_hd {T Ts} (h : hlist (T :: Ts)) : F T :=
  match h wBh
  | Hcons x _ => x
  | Hnil => tt
  end. *)
  
Variable elm: B.

Inductive member : list B -> Type :=
| HFirst : forall ls, member (elm :: ls)
| HNext : forall x ls, member ls -> member (x :: ls).
Print Hnil.
Implicit Arguments Hnil [B F].
Implicit Arguments Hcons [ B F x ls ].

Eval compute in Hcons 2 (Hcons [3,4] (Hnil)). 

TODO: implementer les listes heterogenes *)

(* Utilisation de A_dec *)
Fixpoint compress (l:list A): list A :=
match l with
| nil => nil
| h :: t => match t with
            | h' :: t' => match A_dec h h' with
                          | left _ => compress t
                          | right _ => h :: compress t
                          end
            | nil => l
            end
end.


(* Utilisation de A_dec *)
Fixpoint compress_bis (l:list A): list A :=
match l with
|nil => nil
| h :: t => h :: (fix sub (l:list A) (last:A): list A :=
                match l with
                |nil => nil
                | h :: t => match A_dec h last with
                            | left _ => sub t last
                            | right _ => h :: (sub t h)
                            end
                end) l h
end.

(* Fixpoint pack (l:list A):list A. implementer listlist... *)

(* 1.14 *)
Fixpoint dupli {A:Type}(l:list A): list A :=
match l with
| nil => nil
| h :: t => h :: h :: dupli t
end.

Fixpoint dupli_elm {A:Type}(x:A)(n:nat) : list A :=
match n with
| O => nil
| S n' => x :: dupli_elm x n'
end.


Fixpoint dupli_nth {A:Type}(l:list A)(n:nat) : list A :=
match l with
| nil => nil
| h :: t => (dupli_elm h n) ++ (dupli_nth t n)
end.

Fixpoint scroll_drop_list {A:Type}(l:list A)(n:nat) : list A :=
match n, l with
| _, nil => nil
| O, h :: t => t
| S n', h :: t => h :: scroll_drop_list t n'
end.

(* En commencant à O *)
Fixpoint drop {A:Type}(l:list A)(n:nat) : list A :=
(fix sub (l:list A)(n cpt:nat) : list A :=
match l, cpt with
| nil, _ => nil
| h :: t, O => sub t n n
| h :: t, S n' => h :: sub t n n'
end) l n n.

(* En commencant à 1 *)
Fixpoint drop_bis {A:Type}(l:list A)(n:nat) : list A :=
let pn := pred n in 
(fix sub (l:list A)(n cpt:nat) : list A :=
match l, cpt with
| nil, _ => nil
| h :: t, O => sub t n n
| h :: t, S n' => h :: sub t n n'
end) l pn pn.

Locate split.

(*
Fixpoint drop {A:Type}(l:list A)(n:nat) : list A :=
match l with
| nil => nil
| h :: t => drop (scroll_drop_list l n) n
end.


Fixpoint drop_bis {A:Type}(l:list A)(n:nat) : list A :=
(fix sub (l:list A)(n cpt:nat) : list A :=
match 

) l n n

*)

Fixpoint split {A : Type} (l : list A) (n : nat) : (list A) * (list A) :=
  match l, n with
    | [], _ => ([], [])
    | h::t, S n' => let (l1, l2) := split t n' in (h::l1, l2)
    | _, O => (nil, l)
end.

(* en partant de 0 *)
Fixpoint slice {A:Type}(l:list A)(m n:nat) : list A :=
match l, m, n with
| nil, _, _ => nil 
| h::t, _, O => h :: nil
| h::t, O, S n' => h :: slice t m n'
| h::t, S m', S n' => slice t m' n' 
end.

(* en partant de 1 *)
Fixpoint slice_bis {A:Type}(l:list A)(m n:nat) : list A :=
match l, m, n with
| nil, _, _ => nil 
| _, _, O => nil
| h::t, O, S n' => h :: slice_bis t m n'
| h::t, S O, S n' => h :: slice_bis t O n'
| h::t, S m', S n' => slice_bis t m' n' 
end.

Fixpoint rotate {A:Type}(l:list A)(n:nat) : list A :=
let lth := List.length l in 
let modn := Nat.modulo n lth in
let (l1, l2) := split l modn in
l2 ++ l1.

(* sans split *)
Fixpoint rotate_bis {A:Type}(l:list A)(n:nat) : list A :=
let lth := List.length l in 
let modn := Nat.modulo n lth in
(fix sub (l s:list A)(n:nat) : list A :=
match l, n with
| nil, _ => nil 
| _, O => l ++ s
| h::t, S n' => sub t (s ++ [h]) n'
end) l nil modn.

(* en conservant l'element supprimé et en partant de 1 *)
Fixpoint remove_kth {A:Type}(l:list A)(n:nat) : (option) * (list A) :=
match l, n with
| nil, _ => (None, nil)
| h::t, O => (Some h, t)
| h::t, S O => (Some h, t)
| h::t, S n' => let (elm, ls) := remove_kth t n' in (elm, h :: ls)
end.

(* en gardant seulement la liste et en partant de 1 *)
Fixpoint remove_kth_bis {A:Type}(l:list A)(n:nat) : list A :=
match l, n with
| nil, _ => nil
| h::t, O => t
| h::t, S O => t
| h::t, S n' => h :: remove_kth_bis t n'
end.

(* en partant de 1 *)
Fixpoint insert_at {A:Type}(e:A)(l:list A)(n:nat) : list A :=
match l, n with
| nil, _ | _, O | _, S O => e :: l
| h::t, S n' => h:: insert_at e t n'
end.

End list_prob.

Open Scope string_scope.
(* Eval compute in last ["a","b","c","d"].
Eval compute in last_but_one ["a","b","c","d"].
Eval compute in element_at ["a","b","c","d"] 3.
Eval compute in element_at_bis ["a","b","c","d"] 1.
Eval compute in card_list ["a","b","c","d"].
Eval compute in rev_list ["a","b","c","d"].
Eval compute in rev_list_bis ["a","b","c","d"].
Eval compute in is_palindrome string String.string_dec ["a","b","b","a"].
Eval compute in is_palindrome nat PeanoNat.Nat.eq_dec [2,3,3,2].
Eval compute in compress nat PeanoNat.Nat.eq_dec [2,3,3,2,2,1,1,1].
Eval compute in compress_bis nat PeanoNat.Nat.eq_dec [2,3,3,2,2,1,1,1].
Eval compute in dupli ["a","b","b","c","d"].
Eval compute in dupli_nth ["a","b","c"] 3. 
Eval compute in drop ["a","b","c","a","b","c","a","b","c"] 3.
Eval compute in drop_bis ["a","b","c","a","b","c","a","b","c"] 3.
Eval compute in slice ["a","b","c","d", "e", "f"] 3 5.
Eval compute in slice_bis ["a","b","c","d", "e", "f"] 3 5.
Eval compute in rotate ["a","b","c","d", "e", "f"] 4. *)
Eval compute in split ["a","b","c","d", "e", "f"] 4.
Eval compute in remove_kth ["a","b","c","d", "e", "f"] 2.
Eval compute in remove_kth_bis ["a","b","c","d", "e", "f"] 2.
Eval compute in insert_at "c" ["a","b","d"] 2.





