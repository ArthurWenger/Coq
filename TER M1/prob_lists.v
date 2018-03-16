(*Require Import notations.
Require Import option.
Require Import String.*)

Require Import List.
Import ListNotations.
Local Open Scope list_scope.
Require Import Datatypes.
Require Import Ascii.

Section list_prob.
(* Variable A:Type.  a changer / modifier *)

(* 1.01 Find the last element of a list. *)
Fixpoint last {A:Type}(l:list A): option A :=
    match l with
    | nil => None
    | x :: nil => Some x
    | _ :: y => last y
    end. 

Theorem last_append {A:Type}: forall (x:A) (l:list A), last(l++[x]) = Some x.
Proof.
    intros x l.
    induction l. 
    - reflexivity.
    - simpl. rewrite IHl. destruct (l++[x]).
        * (* last [] = Some x impossible *) inversion IHl.
        * reflexivity.
Qed.

Theorem last_rev {A:Type}: forall (x:A) (l:list A), last (List.rev (x::l)) = Some x .
Proof.
    intros x l.
    simpl. apply last_append.
Qed.

(* 1.02 Find the last but one element of a list. *)
Fixpoint last_but_one {A:Type}(l:list A): option A :=
    match l with
    | nil => None
    | x :: y :: nil => Some x
    | _ :: y => last_but_one y
    end.

Theorem last_but_one_append {A:Type}: forall (l:list A) (x:A) (y:A),
    last_but_one (l ++ [x;y]) = Some x.
  Proof.
    intros l x y.
    induction l.
    - reflexivity.
    - simpl. destruct (l ++ [x;y]).
        * (* last_but_one [] = Some x impossible *) inversion IHl.
        * rewrite IHl. destruct l0.
            ** (* Some a = Some x impossible *) inversion IHl.
            ** reflexivity.
  Qed.

(* 1.03 Find the K'th element of a list. *) 
(* en commencant la notation à 0 *)
Fixpoint element_at {A:Type}(l:list A)(n: nat): option A :=
    match n, l with
    | _, nil => None
    | O, x :: _ => Some x
    | S n', _ :: y => element_at y n'
    end.

(* en commencant la notation à 1 *)
Fixpoint element_at_bis {A:Type}(l:list A)(n: nat): option A :=
    match n, l with
    | _, nil => None
    | O, _ => None
    | S O, x :: _ => Some x
    | S n', _ :: y => element_at_bis y n'
    end.

Theorem element_at_bis_0 {A:Type}: forall (l:list A), element_at_bis l 0 = None.
Proof.
    intro l. 
    case l. 
    - reflexivity.
    - intros x l'. reflexivity.
Qed.

Theorem element_at_bis_append {A:Type}: forall (l:list A) (x:A),
    element_at_bis (l ++ [x]) (length l + 1) = Some x.
  Proof.
    intros l x.
    induction l.
    - reflexivity.
    - simpl. destruct (length l + 1).
        * rewrite element_at_bis_0 in IHl. (* None = Some x impossible *) inversion IHl.
        * apply IHl.
  Qed.

(* 1.04 Find the number of elements of a list. *) 
Fixpoint card_list {A:Type}(l:list A): nat :=
    match l with
    | nil => O
    | x :: y => S (card_list y)
    end.

(* 1.05 Reverse a list. *) 
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

(* 1.06 Find out whether a list is a palindrome. *) 
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

(* 1.08 Eliminate consecutive duplicates of list elements. *) 
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

(* 1.14 Duplicate the elements of a list. *) 
Fixpoint dupli {A:Type}(l:list A): list A :=
match l with
| nil => nil
| h :: t => h :: h :: dupli t
end.

(* 1.15 Duplicate the elements of a list a given number of times. *) 
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

(* 1.16 Drop every N'th element from a list. *) 
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
(* 1.17 Split a list into two parts; the length of the first part is given. *) 
Locate split.

Fixpoint split {A : Type} (l : list A) (n : nat) : (list A) * (list A) :=
match l, n with
    | [], _ => ([], [])
    | h::t, S n' => let (l1, l2) := split t n' in (h::l1, l2)
    | _, O => (nil, l)
end.

(* 1.18 Extract a slice from a list. *) 
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

(* 1.19 Rotate a list N places to the left. *) 
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

(* 1.20 Remove the K'th element from a list. *) 
(* en renvoyant un couple et en partant de 1 *)
Fixpoint remove_kth {A:Type}(l:list A)(n:nat) : (option) * (list A) :=
match l, n with
| nil, _ => (None, nil)
| h::t, O => (Some h, t)
| h::t, S O => (Some h, t)
| h::t, S n' => let (elm, ls) := remove_kth t n' in (elm, h :: ls)
end.

(* en renvoyant seulement la liste et en partant de 1 *)
Fixpoint remove_kth_bis {A:Type}(l:list A)(n:nat) : list A :=
match l, n with
| nil, _ => nil
| h::t, O => t
| h::t, S O => t
| h::t, S n' => h :: remove_kth_bis t n'
end.

(* 1.21 Insert an element at a given position into a list. *) 
(* en partant de 1 *)
Fixpoint insert_at {A:Type}(e:A)(l:list A)(n:nat) : list A :=
match l, n with
| nil, _ | _, O | _, S O => e :: l
| h::t, S n' => h :: insert_at e t n'
end.

(* 1.22 Create a list containing all integers within a given range. *) 
Fixpoint range (a b:nat) : list nat :=
let diff := b - a in 
(fix sub (b diff:nat) : list nat :=
match diff with
| O => [b]
| S d' => (b-diff) :: sub b d'
end) b diff.

Fixpoint range_bis (a b:nat) : list nat :=
if Arith.Compare_dec.le_lt_dec a b then  
match b with
| O => [O]
| S b' => (range a b') ++ [b]
end
else nil.

(* 1.28 Sorting a list of lists according to length of sublists  *) 
Inductive listlist (A:Type) : Type :=
  | lnil : listlist A
  | lcons : list A -> listlist A -> listlist A.

Implicit Arguments lnil [A].
Implicit Arguments lcons [A].

Fixpoint lcount {A:Type}(l:listlist A): nat :=
match l with
| lnil => 0
| lcons _ l' => 1 + lcount l'
end.

Notation "'{ }" := lnil.
Notation "'{ x , .. , y }" := (lcons x .. (lcons y lnil) ..).

Fixpoint sub_lsort {A:Type} (l:list A)(m:listlist A)(length:nat) : listlist A :=
match m with
| lnil => lcons l lnil
| lcons h t => if Arith.Compare_dec.le_lt_dec length (List.length h) then 
               lcons l m
               else lcons h (sub_lsort l t length)
end. 

Eval compute in sub_lsort [1,2,2] '{[1],[1,2,3,4]} 3.

Fixpoint lsort {A:Type}(l:listlist A) : listlist A :=
match l with
| lnil => lnil
| lcons h t => sub_lsort h (lsort t) (List.length h)
end.

Fixpoint lsort_bis {A:Type}(l:listlist A) : listlist A :=
(fix sub (m res:listlist A) : listlist A :=
match m with
| lnil => res
| lcons h t => sub t (sub_lsort h res (List.length h))
end) l lnil.


Eval compute in lsort '{[1],[1,2,3,4],[1,2],[1,4,5]}.
Eval compute in lsort_bis '{[1],[1,2,3,4],[1,2],[1,4,5]}.

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
Eval compute in range_bis 5 8.





