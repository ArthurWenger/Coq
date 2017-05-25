Require Import region.
Require Import option.

Section customlist.
(* Le type inductif [clist] permet de construire de listes.
   Le parametre A permet de garantir le polymorphisme des listes. *)
Inductive clist (A:Type): Type :=
  | nil : clist A
  | cons : A -> clist A -> clist A.

(* Il n'est pas nécessaire de spécifier le type de liste A pour les constructeurs nil et cons. 
   Celui-ci peut être déduit des autres éléments de la liste. On le défini donc comme implicite. *)
Implicit Arguments nil [A].
Implicit Arguments cons [A].

(* Permet de compter le nombre d'éléments d'une liste. 
   La notation {A:Type} permet d'inférer le type de la liste à partir de l.
   Le paramètre A est donc implicite.  
   Pour déclarer explicitement A dans une preuve, utiliser la notation: @list_count A l *)
Fixpoint list_count {A:Type} (l:clist A) : nat := 
  match l with
  | nil => 0
  | cons n l' =>  1 + list_count l'
  end.

(* Permet de concatener deux listes de meme type. *)
Fixpoint concat_list {A:Type}(l1 l2:clist A): clist A :=
match l1 with
| nil => l2
| cons n l' => cons n (concat_list l' l2)
end.

(* Permet de récuperer l'élement d'une liste l à la position n.
   On renvoie [None] lorsque la liste est trop courte et [Some x] 
   lorsqu'elle est assez longue et contient x. *)
Fixpoint get_list_elm {A:Type}(l:clist A)(n:nat): option :=
  match l, n with
  | nil, _ => None
  | cons x l', 0 => Some x
  | cons x l', S n' => get_list_elm l' n'
  end.

End customlist.
Implicit Arguments nil [A].
Implicit Arguments cons [A].

(* Notations standard pour les listes *)
Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).
Notation "x ++ y" := (concat_list x y) (at level 60, right associativity).

(* Permet de vérifier qu'une region est dans une liste de regions.
   Si on voulait généraliser cette fonction pour tous les types de liste [A]
   il faudrait définir l'égalité pour des types polymorphes. (contrairement au == en scala) *)
Fixpoint is_in_list (l:clist region)(x:region): bool :=
match l with
| nil => false
| cons n l' => if equal_region x n then
                true
               else
                is_in_list l' x
end.

(* Permet de récupérer la position d'une region dans une liste de regions. *)
Fixpoint get_row_region (l:clist region)(x:region): option :=
match l with
| nil => None (* x n'est pas dans l *)
| cons n l' => if equal_region x n then
                Some 0
               else
                add_opt (Some 1) (get_row_region l' x)
end.

Eval compute in [1].
Eval compute in [OO Z].

Eval compute in list_count [OO Z, IO(II Z), OO Z, IO Z].
Eval compute in list_count [0, 1, 2].
Eval compute in list_count [].

Eval compute in [1,2] ++ [3,4].
Eval compute in [OO Z,IO Z] ++ [OI Z,II Z].

Eval compute in get_list_elm [1,2,3] 1.

Eval compute in is_in_list [OO Z,OI Z,IO Z] (II Z).  
Eval compute in is_in_list [OO Z,OI Z,IO Z] (IO Z). 

(* Permet d'alléger le code lorsqu'on récupère des region à partir d'option *)
Definition get_list_reg (l:clist region)(n:nat): region := option_elim Z (get_list_elm l n). 

Eval compute in get_list_reg [OO Z,IO Z,II Z] 2.
Eval compute in get_row_region [OO Z, IO Z, II Z] (II Z).
Eval compute in get_row_region [OO Z, IO Z, II Z] (II (OO Z)).

(* Permet de vérifier que 2 listes de regions sont égales *)
Fixpoint equal_list_region (l1 l2:clist region): bool :=
match l1, l2 with 
| nil, nil => true
| cons x1 l1', cons x2 l2' => if(equal_region x1 x2) then equal_list_region l1' l2' else false
| _, _ => false
end.

Eval compute in equal_list_region [OO Z, II Z, IO Z] [OO Z, II Z].
Eval compute in equal_list_region [OO Z, II Z, IO Z] [OO Z, II Z, IO Z, II Z].
Eval compute in equal_list_region [OO Z, II Z, IO Z] [OO Z, II Z, IO Z].

(* ### Preuves ### *)

Theorem concat_list_count {A:Type}(l1 l2:clist A): 
list_count (l1 ++ l2) = list_count l1 + list_count l2 .
Proof. 
  induction l1.
  reflexivity.
  simpl. 
  rewrite IHl1. 
  reflexivity.
Qed.

Theorem concat_list_nil {A:Type}(l:clist A): l ++ [] = l.
Proof.
 induction l. 
 reflexivity.
 simpl. 
 rewrite IHl. 
 reflexivity.
Qed.