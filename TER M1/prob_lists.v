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
Fixpoint length2 {A:Type}(l:list A): nat :=
    match l with
    | nil => O
    | _ :: y => S (length2 y)
    end.

Theorem length2_append {A:Type}: forall (l1 l2:list A),
    length2 l1 + length2 l2 = length2 (l1 ++ l2).
  Proof.
    intros l1 l2.
    induction l1.
    - (* length l2 = length l2 *) reflexivity.
    - simpl. rewrite IHl1. reflexivity.
  Qed.

Theorem length2_eq_length {A:Type}: forall (l:list A),
  length2 l = length l.
Proof.
  intro l.
  induction l.
  - (* 0=0 *) reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

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

Theorem rev_list_append {A:Type}: forall (l:list A)(x:A), 
rev_list (l++[x]) = x::(rev_list l).
Proof.
    intros l x.
    induction l.
    - reflexivity.
    - simpl. rewrite IHl. reflexivity.    
Qed.

Theorem rev_cons {A:Type}: forall (l:list A)(x:A), 
rev_list (x::l) = (rev_list l)++[x].
Proof.
    intros l x.
    case l.
    - reflexivity.
    - simpl. reflexivity.    
Qed.

Theorem rev_list_involutive {A:Type}: forall (l:list A), 
    rev_list (rev_list l) = l.
Proof.
    intro l.
    induction l. 
    - reflexivity.
    - simpl. rewrite rev_list_append. rewrite IHl. reflexivity.    
Qed.

Theorem rev_eq_rev_list {A:Type}: forall (l:list A), 
    rev_list l = rev l.
Proof.
    intro l.
    induction l.
    - reflexivity.
    - simpl. rewrite IHl. reflexivity.    
Qed.

(* 1.06 Find out whether a list is a palindrome. *) 
Section pal_A_dec.
Variable A:Type. (* on crée une variable pour pouvoir indiquer que A doit être décidable *)
Hypothesis A_dec : forall x y:A, {x = y} + {x <> y}.

Theorem not_x_x: forall (x:A), x <> x -> false = true.
Proof.
    intros. pose (Bool.absurd_eq_true) as X. apply X. apply H. apply (eq_refl x).
Qed.

Theorem not_x_x_bis: forall (x:A)(P:Prop), x <> x -> P.
Proof.
    intros.
    apply not_x_x in H. discriminate.
Qed.


Fixpoint equal_lists (l l':list A): bool :=
match l, l' with
| nil, nil => true
| x :: y, x' :: y' => match A_dec x x' with
                      | left _ => equal_lists y y'
                      | right _ => false
                      end
| _, _ => false 
end.

(* en utilisant list_eq_dec *)
Fixpoint equal_lists_bis (l l':list A): bool :=
match list_eq_dec A_dec l l' with
| left _ => true
| right _ => false
end.

Theorem equal_lists_l_l: forall (l:list A), equal_lists l l = true .
Proof.
    intro l. induction l. 
    - reflexivity. 
    - simpl. case (A_dec a a). 
        * intro h. apply IHl.
        * apply not_x_x.
Qed.

Definition is_palindrome (l:list A): bool :=
    equal_lists l (rev_list l).

(* Alternativement on peut définir un type inductif *)
Inductive palindrome : list A -> Prop :=
|Empty : palindrome nil
|Single : forall n, palindrome [n]
|Rcons : forall (n : A)(l : list A), palindrome l -> palindrome (n :: l ++ [n]).

Theorem is_palindrome_nil: is_palindrome [] = true.
Proof.
    unfold is_palindrome.
    simpl. reflexivity.
Qed.

Theorem equal_lists_cons: forall (x:A)(l l':list A), 
    equal_lists (x::l) (x::l') = equal_lists l l'.
Proof.
    intros. destruct (A_dec x x).
    - simpl. destruct (A_dec x x).
        * reflexivity.
        * absurd (x=x). apply n. apply e.
    -  pose (Bool.absurd_eq_bool) as X. apply X. apply n. apply (eq_refl x). 
Qed.

Lemma nil_cons (x:A)(l:list A)
: not (nil=cons x l).
intro.
discriminate.
Qed.

Lemma nil_app (x:A)(l:list A)
: not (nil= l++[x]).
destruct l. simpl. discriminate.
discriminate.
Qed.

Theorem palindrome_self_rev : forall (l: list A),
  palindrome (l ++ rev l). 
Proof.
  intros. induction l.
  - simpl. apply Empty. 
  - simpl. rewrite app_assoc. apply Rcons. apply IHl.
Qed.

Theorem palindrome_rev: forall (l:list A), palindrome l -> l = rev l.
  intros. induction H.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite rev_unit. rewrite <- IHpalindrome. reflexivity.
Qed.

(* ############ Demo l = rev l -> palindrome l ############## *)

Lemma fib_ind :
 forall P:nat -> Prop,
   P 0 ->
   P 1 -> 
  (forall n:nat, P n -> P (S n) -> P (S (S n))) -> 
  forall n:nat, P n.
Proof.
 intros P H0 H1 HSSn n. cut (P n /\ P (S n)).
 - intro H. inversion H. apply H2.
 - induction n.
    * split.
        ** apply H0.
        ** apply H1.
    * split.
        ** inversion IHn. apply H2.
        ** apply HSSn.
            *** inversion IHn. apply H.
            *** inversion IHn. apply H2.
Qed.

Definition lfirst {X} (l: list X) : list X :=
  match l with
  | [] => []
  | x :: l => [x]
end.

Definition init {X} (l: list X) : list X := rev (tail (rev l)).

Definition llast {X} (l: list X) : list X := rev (lfirst (rev l)).

Theorem app_r_nil : forall X (l: list X),
  l ++ [] = l.
Proof. intros. induction l. reflexivity. simpl. rewrite IHl. reflexivity.
Qed.

Lemma rev_app_rev : forall X (a b:list X),
  rev a ++ rev b = rev (b ++ a).
Proof. intros X a. induction a; intros.
  rewrite app_r_nil. reflexivity.
  simpl. rewrite <- app_assoc.
  remember ([a] ++ rev b) as xrb.
  rewrite <- rev_involutive with X xrb. rewrite IHa.
  simpl in Heqxrb. rewrite Heqxrb. simpl. 
  rewrite rev_involutive. rewrite <- app_assoc. simpl. reflexivity.
Qed.

Theorem rev_bij : forall X (l1 l2: list X),
  l1 = l2 <-> rev l1 = rev l2.
Proof. intros. split. intro H. rewrite H. reflexivity.
  intro H. rewrite <- rev_involutive. rewrite <- rev_involutive at 1.
  rewrite H. rewrite ? rev_involutive. reflexivity.
Qed.


Theorem first_app_tail : forall X (l: list X),
  l = lfirst l ++ tail l.
Proof. intros.
  destruct l. reflexivity.
  simpl. reflexivity.
Qed.

Theorem init_app_last : forall X (l: list X),
  l = init l ++ llast l.
Proof. intros.
  unfold init. unfold llast. rewrite rev_app_rev.
  rewrite <- rev_involutive at 1. rewrite <- rev_bij.
  apply first_app_tail.
Qed.

Theorem snoc_tail_almost_comm : forall X (x: X) (l: list X),
  l <> [] -> tail (l ++ [x]) = (tail l) ++ [x].
Proof. intros. destruct l. 
    - exfalso. apply H. reflexivity. 
    - reflexivity.
Qed.

Lemma lfirst_almost_init_inv : forall X (x y: X) (l: list X),
  lfirst (init (x::y::l)) = lfirst (x::y::l).
Proof. intros. unfold init. remember (y::l) as yl. simpl.
  rewrite snoc_tail_almost_comm.
  rewrite rev_unit. reflexivity.
  rewrite Heqyl. rewrite rev_bij. rewrite rev_involutive. simpl. 
  discriminate.
Qed.

Theorem split_ends : forall X (l: list X) (x y: X),
 (x::y::l) = lfirst (x::y::l) ++ tail (init (x::y::l)) ++ llast (x::y::l).
Proof. intros.  
  rewrite init_app_last at 1.
  rewrite first_app_tail with (l := init (x::y::l)) at 1.
  rewrite lfirst_almost_init_inv. reflexivity.
Qed.

Theorem first_single : forall X (x y:X) (l: list X), l <> [] -> exists k, lfirst (l) = [k].
Proof. intros. induction l. unfold not in H. exfalso. apply H. reflexivity.
  exists a. reflexivity.
Qed.

Theorem last_single : forall X (x y:X) (l: list X), l <> [] -> exists k, llast (l) = [k].
Proof. intros. induction l. unfold not in H.  exfalso. apply H. reflexivity.
unfold llast. assert (exists z, lfirst (rev (a :: l)) =  [z]).
  apply first_single. assumption. assumption. rewrite rev_bij. rewrite rev_involutive. simpl. discriminate.
  inversion H0. rewrite H1. exists x0. reflexivity.
Qed.

Lemma length_app :
 forall X (l l':list X), length (l ++ l') = length l + length l'.
Proof.
  intros X l; elim l; simpl; auto.
Qed.

Require Import Arith.

Theorem list_induction : forall X (P : list X -> Prop),
       P [] -> 
       (forall (x : X), P [x]) ->
       (forall (x y : X) (l : list X), P l -> P (x :: l ++ [y])) ->
       forall l : list X, P l.
Proof. 
 intros.
 cut (forall (n:nat) (l:list X), length l = n -> P l).
 - (* Case "Proof of assertion" *) intros. eapply H2. reflexivity.
 - intro n. pattern n. apply fib_ind.
    * (* Case "length is 0". *) intros. apply length_zero_iff_nil in H2. rewrite H2. apply H.
    * (* Case "length is 1". *) intros. destruct l0.
        ** simpl in H2. inversion H2.
        ** simpl in H2. inversion H2. apply length_zero_iff_nil in H4. rewrite H4. apply H0.
    * (*  Case "length is S S n". *) intros. destruct l0.
        ** simpl in H4. inversion H4.
        ** destruct l0.
            *** simpl in H4. inversion H4.
            *** rewrite split_ends. simpl. rewrite split_ends in H4. simpl in H4. inversion H4. 
                assert(x::x0::l0 <> []).
                + unfold not. intro contra. inversion contra.
                + apply last_single in H5.
                    ++ inversion H5. rewrite H7.  apply H1. apply H2. rewrite H7 in H6. 
                       rewrite length_app in H6. simpl in H6. rewrite plus_comm in H6. 
                      inversion H6. reflexivity.
                    ++ assumption.
                    ++ assumption.
Qed.

Theorem app_l_eq : forall X (l1 l2 m: list X), m ++ l1 = m ++ l2 -> l1 = l2.
Proof. intros. induction m. simpl in H. apply H.
 inversion H. apply IHm in H1. apply H1.
Qed.

Theorem app_r_eq : forall X (l1 l2 m: list X), l1 ++ m = l2 ++ m -> l1 = l2.
Proof. intros. rewrite rev_bij in H. rewrite <- 2? rev_app_rev in H.
 apply app_l_eq in H. rewrite <- rev_bij in H. apply H.
Qed. 

Theorem rev_pal : forall (l: list A),
  l = rev l -> palindrome l.
intros l. pattern l. apply list_induction; intros. Print palindrome.
 apply Empty.  apply Single. simpl in H0.
 rewrite rev_unit in H0.
 simpl in H0. inversion H0.
 apply Rcons.
 apply H.
 apply app_r_eq in H3. apply H3.
Qed.

(* ############ Fin Demo l = rev l -> palindrome l ############## *)

(*Lemma palindromic_rev : forall l:list A, palindrome l -> rev_list l = l.
Proof.
    intros l H.
    induction l. reflexivity.
    simpl. generalize IHl. inversion H. simpl. reflexivity.
    simpl. intros. rewrite rev_list_append. simpl.
    elim H. destruct l. discriminate.
    elim H. reflexivity.
    reflexivity.
    intros. simpl. rewrite rev_list_append. simpl.

intros l H. elim H. simpl. auto with datatypes.
intros a l0 m H0 H1 H2.
generalize H1; inversion_clear H2.
simpl; auto.
rewrite (remove_last_inv H3).
simpl.
repeat (rewrite rev_app; simpl).
intro eg; rewrite eg.
simpl; auto.
Qed. *)


Theorem equal_lists_append: forall (x:A)(l1 l2:list A), 
    equal_lists (l1 ++ [x]) (l2 ++ [x]) = equal_lists l1 l2.
Proof.
    intros.
    Admitted.

Theorem is_palindrome_append: forall (l:list A)(x:A),
    is_palindrome l = is_palindrome (x :: (l ++ [x])).
Proof.
    intros l x.
    unfold is_palindrome.
    rewrite rev_cons. rewrite rev_list_append. rewrite <- app_comm_cons. 
    rewrite (equal_lists_cons x). rewrite (equal_lists_append x). reflexivity.
Qed.

Theorem palindrome_nil: forall (l:list A), l=[] -> palindrome l.
Proof.
    intros.
    subst.
    constructor.
Qed.

Theorem cons_app_pal: forall (l:list A)(a:A), 
    is_palindrome l = true -> is_palindrome (a :: l ++ [a]) = true.
Proof.
    intros.
    induction l.
    - simpl. unfold is_palindrome. simpl. case (A_dec a a).
        * reflexivity.
        * apply not_x_x.
    - simpl. unfold is_palindrome in *. Admitted.


Theorem pal_self_rev : forall (l: list A),
  is_palindrome (l ++ rev l) = true.
intros. induction l.
    - reflexivity.
    - simpl. assert (P: a :: (l ++ rev l) ++ [a] = a :: l ++ rev l ++ [a]). 
        * rewrite app_assoc. reflexivity. 
        * rewrite <- P. apply (cons_app_pal (l ++ rev l) a). apply IHl.
Qed. 
End pal_A_dec.

(* Theorem rev_eq_pal_length: forall (n: nat) (l: list A), 
    length l <= n -> l = rev l -> palindrome l.
Proof.
(* by induction on [n], not [l] *)
    intros.
    induction n. 
    - destruct l as [|a l'].
        * constructor.
        * simpl in H. inversion H.
    - destruct l as [|a l'].
        * constructor.
        * inversion H0. destruct (rev l').
            ** simpl in H2. inversion H2. constructor.
            ** rewrite H2. induction l.
                *** simpl. simpl in H2. inversion H2. subst. assert (P:[a0;a0]=a0::[]++[a0]). reflexivity. rewrite P. constructor.
                *** inversion H2. subst. 
             subst. simpl in H. inversion H. subst. simpl in IHn.
Qed. *)

(*    simpl.
    destruct l.
    - simpl. case (A_dec x x). 
        * reflexivity.
        * intro n. pose (Bool.absurd_eq_true) as X. apply eq_sym. apply X. apply n. apply (eq_refl x).
    - apply f_equal. simpl.


    - intro. destruct l. simpl. apply e. reflexivity. 
    
    rewrite <- (equal_lists_eq l (rev_list l)). case (A_dec x x).
    intro n.



    induction l.
    - unfold is_palindrome. simpl. case (A_dec x x). 
        * reflexivity.
        * unfold not. intro n. pose (Bool.absurd_eq_true) as X. apply eq_sym. apply X. apply n. apply (eq_refl x).
    - unfold is_palindrome. rewrite rev_cons. inversion IHl.
     simpl. case rev_list l ++ [a].
        
        
        apply (not(eq_refl x)). intro t. Print eq_refl. apply (eq_refl x) in t. intro test. rewrite test in t. Print absurd. rewrite test. intro t. 
        simpl.  Locate "<>". inversion n.   *)


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


(* 1.07 Flatten a nested list structure. *)

(* probleme pour le cas [1;[1;2];3] => concatenation de listes mais pas d'imbrication *)
Inductive nlist (A:Type): Type :=
| n0 : nlist A
| ucons : A -> nlist A -> nlist A
| lcons : nlist A -> nlist A -> nlist A.

Implicit Arguments n0 [A].
Implicit Arguments ucons [A].
Implicit Arguments lcons [A].

(*
Notation "x :: l" := (ucons x l)(at level 60, right associativity) : nlist_scope.
Notation "[ ]" := n0 : nlist_scope.
Notation "[ x ]" := (ucons x n0) : nlist_scope.
Notation "[ x ; .. ; y ]" := (ucons x .. (ucons y n0) ..) : nlist_scope.
Notation "[ x , .. , y , z ]" := (lcons x .. (lcons y z) ..) : nlist_scope. 
Local Open Scope nlist_scope. *)

Eval compute in lcons (ucons 1 n0) (ucons 1 (ucons 1 n0)).
Eval compute in ucons 1 (ucons  2 n0).
Eval compute in lcons (ucons 1  (ucons 2 (ucons 3 n0))) (ucons 1 (ucons 2 n0)).
 (* Eval compute in lcons [ 1 ; 2 ; 3 ] [1;2].
Eval compute in lcons [ 1 ; 2 ; 3 ] (lcons [1;2] [1;2;3;4]) . *)

Fixpoint nlength {A:Type} (l:nlist A): nat :=
match l with
| n0 => 0
| ucons h t => S (nlength t)
| lcons l1 l2 => 2            
end.

Fixpoint my_flatten {A:Type} (l:nlist A): list A :=
match l with
| n0 => nil
| ucons h t => h :: my_flatten t
| lcons l1 l2 => my_flatten l1 ++ my_flatten l2            
end.

Eval compute in my_flatten (lcons (ucons 1  (ucons 2 (ucons 3 n0))) (ucons 1 (ucons 2 n0))).
(* Eval compute in my_flatten (lcons [ 1 ; 2 ; 3 ] (lcons [1;2] [1;2;3;4])).
Local Close Scope nlist_scope.
Local Open Scope list_scope. *)


(* 1.08 Eliminate consecutive duplicates of list elements. *) 
Section compress_A_dec.
Variable A:Type.
Hypothesis A_dec : forall x y:A, {x = y} + {x <> y}.

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

Theorem compress_append: forall (x:A)(l:list A), 
    compress ([x;x] ++ l) = compress (x::l) .
Proof.
    intros. simpl. case (A_dec x x).
    - intro. destruct l.
        * reflexivity.
        * reflexivity.
    - simpl. apply not_x_x_bis. 
Qed.

Theorem compress_cons: forall (x:A)(l:list A), 
    compress (x::l) = x::(compress l) \/ compress (x::l) = compress l.
Proof.
    intros x l. destruct l.
    - simpl. left. reflexivity.
    - simpl. case (A_dec x a).
        * right. reflexivity.
        * left. reflexivity.    
Qed.
End compress_A_dec.

(* 1.09 Pack consecutive duplicates of list elements into sublists. *)

Inductive depth2list (A:Type): Type :=
| d20 : depth2list A
| d2lcons : list A -> depth2list A -> depth2list A.

Implicit Arguments d20 [A].
Implicit Arguments d2lcons [A].

Section pack_A_dec.
Variable A:Type.
Hypothesis A_dec : forall x y:A, {x = y} + {x <> y}.

Fixpoint pack (l:list A): depth2list A :=
match l with
| nil => d20
| h :: t => 
    (fix sub (l:list A) (last:A) (current:list A): depth2list A :=
        match l with
        | nil => d2lcons current d20
        | h :: t => match A_dec h last with
                    | left _ => sub t h (h :: current)
                    | right _ => d2lcons current (sub t h [h])
                    end
        end) t h [h]
end.

End pack_A_dec.
Eval compute in pack nat Nat.eq_dec [1;1;1;2;2;2;3;4;4;4].

(* Fixpoint pack (l:list A): nlist A :=
match l with
| nil => n0
| h :: t => lcons (
    (fix sub (l:list A) (last:A) (current:nlist A): nlist A :=
        match l with
        | nil => n0
        | h :: t => match A_dec h last with
                    | left _ => sub t h (ucons h current)
                    | right _ => lcons current (sub t h n0)
                    end
        end) l h (ucons h n0)) n0
end. *)


(* 1.10 Run-length encoding of a list. *)
Section encode_A_dec.
Variable A:Type.
Hypothesis A_dec : forall x y:A, {x = y} + {x <> y}.

Print hd.
(* Avec option *)
Fixpoint encode (l:list A): list (nat * option A) :=
let lpack:=pack A A_dec l in (
    (fix sub (l:depth2list A): list (nat * option A) :=
        match l with
        | d20 => nil
        | d2lcons l1 l2 => (length l1, hd_error l1) :: (sub l2)
        end )) lpack.

(* Sans option *)
Fixpoint encode_bis (l:list A): list (nat * A) :=
let lpack:=pack A A_dec l in (
    (fix sub (l:depth2list A): list (nat * A) :=
        match l with
        | d20 => nil
        | d2lcons l1 l2 => match l1 with
                           | nil => (sub l2)
                           | h :: t => (length l1, h) :: (sub l2)
                           end
        end )) lpack.

End encode_A_dec.        
Eval compute in pack nat Nat.eq_dec ([1;1;1;2;2;4;5;5;4]).
Eval compute in encode nat Nat.eq_dec ([1;1;1;2;2;4;5;5;4]).
Eval compute in encode_bis nat Nat.eq_dec ([1;1;1;2;2;4;5;5;4]).

(* 1.11 Modified run-length encoding. *)
(* Implementer une liste heterogene *)
Section hlist.
Variable iT : Type.
Variable F : iT -> Type.

Inductive hlist : list iT -> Type :=
| Hnil : hlist nil
| Hcons : forall {T Ts}, F T -> hlist Ts -> hlist (T :: Ts).

Definition hlist_hd {T Ts} (h : hlist (T :: Ts)) : F T :=
match h with
  | Hcons x _ => x
  | Hnil => tt
end.

Definition hlist_tl {T Ts} (h : hlist (T :: Ts)) : hlist Ts :=
match h with
  | Hcons _ t => t
  | Hnil => tt
end.

Print hlist_tl.
End hlist.


Section encode2_A_dec.
Variable A:Type.
Hypothesis A_dec : forall x y:A, {x = y} + {x <> y}.

Inductive dlist (A:Type): Type :=
| Dn0 : dlist A
| Dcons : A -> dlist A -> dlist A
| DLcons : (nat*A) -> dlist A -> dlist A.

Implicit Arguments Dn0 [A].
Implicit Arguments Dcons [A].
Implicit Arguments DLcons [A].

Check Dn0.
Check (Dcons 1 (Dcons 2 Dn0)).
Check DLcons (2,1) (Dcons 1 (Dcons 2 Dn0)).


(* Notation "x :: l" := (Dcons x l)(at level 60, right associativity) : dlist_scope.
Notation "[ ]" := Dn0 : dlist_scope.
Notation "[ x ]" := (Dcons x n0) : dlist_scope.
Notation "[ x ; .. ; y ]" := (Dcons x .. (Dcons y Dn0) ..) : dlist_scope.
Notation "[ x , .. , y , z ]" := (DLcons x .. (DLcons y z) ..) : dlist_scope. 
Local Open Scope dlist_scope. *)


Fixpoint encode_modified (l:list A): dlist A :=
match l with
| nil => Dn0
| h :: t => 
    (fix sub (l:list A) (last:A) (count:nat): dlist A :=
        match l with
        | nil => if count =? 1 then 
                    Dcons last Dn0
                else
                    DLcons (count, last) Dn0
        | h :: t => match A_dec h last with
                    | left _ => sub t h (S count)
                    | right _ => if count =? 1 then 
                                    Dcons last (sub t h 1)
                                 else
                                    DLcons (count, last) (sub t h 1)
                    end
        end) t h 1
end.



(* Eval compute in encode_modified nat Nat.eq_dec ([1;1;1;2;3;3;4]). *)

(* 1.12 Decode a run-length encoded list. *)
Fixpoint decode {A:Type} (l:list (nat * A)): list A :=
match l with
| nil => nil
| (l,r) :: t => (fix dup (x:A)(n:nat): list A :=
                match n with
                | O => nil
                | S n' => x :: dup x n'
                end) r l ++ decode t
end.

Eval compute in encode nat Nat.eq_dec [1;1;1;2;2;4;5;5;4].
Eval compute in decode [(3,1); (2,2); (1,4); (2,5); (1,4)].


(* 1.13 Run-length encoding of a list (direct solution). *)
Fixpoint encode_direct (l:list A): list (nat * A) :=
match l with
| nil => nil
| h :: t => 
    (fix sub (l:list A) (last:A) (count:nat): list (nat * A) :=
        match l with
        | nil => (count, last) :: nil
        | h :: t => match A_dec h last with
                    | left _ => sub t h (S count)
                    | right _ => (count, last) :: (sub t h 1)
                    end
        end) t h 1
end.

Theorem decode_inv_encode: forall(l:list A), decode (encode_direct l) = l.
Proof.
    Admitted.
       
End encode2_A_dec.



(* Theorem compress_cons2: forall (a:A)(l:list A), exists (l':list A), compress (a::l) = a::l'.
Proof.
    Admitted.   

Theorem list_neq_cons: forall (a:A)(l:list A), a::l <> l.
Proof.
    intros. Admitted.


Theorem compress_cons_not: forall (x a:A)(l:list A), 
    x::compress(a::l) <> compress(a::l).
Proof.
    intros. apply list_neq_cons.
Qed.

Theorem compress_cons_right: forall (x:A)(l:list A), 
    compress (x::l) = compress l -> exists (a:A)(l':list A), l = a::l' /\ a = x.
Proof.
    intros x l.
    simpl.
    destruct l as [| a l2]. 
    - discriminate.
    - case (A_dec x a).
        * intros. exists a. exists l2. split. reflexivity. apply eq_sym in e. apply e.
        * intros e. simpl. destruct l2. 
            ** discriminate.
            ** simpl. Admitted. *)


(* Fixpoint pack (l:list A):list A. implementer listlist... *)

(* 1.14 Duplicate the elements of a list. *) 
Fixpoint dupli {A:Type}(l:list A): list A :=
match l with
| nil => nil
| h :: t => h :: h :: dupli t
end.

Theorem dupli_cons {A:Type}: forall (x:A)(l:list A), dupli (x::l) = [x;x] ++ dupli l.
Proof.
    intros x l.
    eauto.  
Qed.

(*
Theorem dupli_compress {A:Type}: forall(l:list A), compress (dupli l) = compress l.
Proof.
    intro l. induction l.
    - reflexivity.
    - rewrite dupli_cons. rewrite compress_append. pose compress_cons as C.
        elim (C a l). intro H. rewrite <- IHl in H. rewrite H.
        elim (C a (dupli l)). trivial.
        intros. rewrite H0. rewrite IHl in H. 
        pose (list_neq_cons a (compress (dupli l))) as X. unfold not in X. elim X. 
Admitted. *)
  (*    destruct (C a (dupli l)). rewrite H. rewrite IHl. apply eq_sym. destruct (C a l).
      rewrite H0. reflexivity.
      simpl.
      rewrite H0. simpl. 
      simpl. destruct l. discriminate. 
        simpl.
      rewrite <- H0 in IHl. rewrite IHl in H. rewrite H0 in H.

      
      rewrite H. rewrite H0. rewrite IHl. reflexivity.
      rewrite H0. rewrite IHl. rewrite H. 
      rewrite H. rewrite H0. rewrite IHl.
       split. rewrite (C a l). 
Qed. *)

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
Fixpoint remove_kth {A:Type}(l:list A)(n:nat) : (option A) * (list A) :=
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

(* En utilisant le_lt_dec := {n <= m} + {m < n} *)
Fixpoint range_bis (a b:nat) : list nat :=
if Arith.Compare_dec.le_lt_dec a b then  
    match b with
    | O => [O]
    | S b' => (range a b') ++ [b]
    end
else nil.

(* 1.23 Extract a given number of randomly selected elements from a list. *)
(* utiliser seed pour générer des nombres aléatoires ? *)
Require Import Streams.
CoFixpoint rand (seed n1 n2 : nat) : Stream nat :=
    let seed' := Nat.modulo seed n2 in Cons seed' (rand (seed' * n1) n1 n2).


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





