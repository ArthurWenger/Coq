Require Import notations.
Import ListNotations.
Local Open Scope list_scope.

Section listlist.
(* Le type inductif listlist permet de construire des listes de listes.
   Le constructeur lnil permet de définir la listlist qui ne contient aucune listes.
   La listlist [ [] ] n'est donc pas vide car elle contient une liste (meme si cette liste est vide).
   Le constructeur lcons concatene une liste à une listlist.
   Chaque liste peut être vue comme une colonne dans un tableau non homogene. *)
Inductive listlist (A:Type) : Type :=
  | lnil : listlist A
  | lcons : list A -> listlist A -> listlist A.

Implicit Arguments lnil [A].
Implicit Arguments lcons [A].

  
(* Permet de récupérer la n ième colonne d'une [listlist]  *)
Fixpoint get_col {A:Type}(m:listlist A)(n:nat): list A :=
  match m, n with
  | lnil, _ => nil
  | lcons l m', 0 => l
  | lcons l m', S n' => get_col m' n'
  end.


Notation "'{ }" := lnil.
Notation "'{ x , .. , y }" := (lcons x .. (lcons y lnil) ..).


Print lcons.
Open Scope list_scope.
Definition mylistlist := lcons [1,2] lnil.
Eval compute in mylistlist.
Eval compute in '{[7,8,9],[1,2,3]}.