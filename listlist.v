Require Import region.
Require Import option.
Require Import clist.

Section listlist.
(* Le type inductif listlist permet de construire des listes de listes.
   Le constructeur lnil permet de définir la listlist qui ne contient aucune listes.
   La listlist [ [] ] n'est donc pas vide car elle contient une liste (meme si cette liste est vide).
   Le constructeur lcons concatene une liste à une listlist.
   Chaque liste peut être vue comme une colonne dans un tableau non homogene. *)
Inductive listlist (A:Type) : Type :=
  | lnil : listlist A
  | lcons : clist A -> listlist A -> listlist A.

Implicit Arguments lnil [A].
Implicit Arguments lcons [A].

(* Nombre de colonnes dans une [listlist] *)
Fixpoint mat_count {A:Type}(m:listlist A): nat :=
match m with
| lnil => 0
| lcons l m' => 1 + mat_count m'
end.

(* Concatene deux [listlist] horizontalement *)
Fixpoint horcat {A:Type}(l1 l2:listlist A): listlist A :=
match l1 with
| lnil => l2
| lcons v l' => lcons v (horcat l' l2)
end.

(* Concatene deux [listlist] verticalement *)
Fixpoint vertcat {A:Type}(m1 m2:listlist A): listlist A :=
match m1, m2 with
| lcons l1 m1', lcons l2 m2' => lcons (l1 ++ l2) (vertcat m1' m2')
| lnil, _ => m2
| _, lnil => m1
end.

(* Permet de vérifier qu'une liste de listes est une matrice *)
Fixpoint is_matrix {A:Type}(m:listlist A) : bool :=
match m with
| lnil => true
| lcons l m' => match m' with
                | lnil => true
                | lcons l' m'' => Nat.eqb (list_count l) (list_count l') && is_matrix m''
                end
end.

(* Fixpoint is_matrix_bis {A:Type}(m:listlist A) : bool.
case_eq m. intro H. exact true.
intros. pose (e := list_count c).
case_eq l. intro H0. exact true.
intros. exact (Nat.eqb e (list_count c0) && (is_matrix_bis A l0)).
Qed. *)
(* OLD
  Definition is_matrix {A:Type}(m:listlist A) : bool :=
  let compare_first_list_count := 
  (fix sub (m:listlist A)(first_list_count:nat) : bool := 
    match m with
    | lnil => true
    | lcons l' m' => if Nat.eqb first_list_count (list_count l') then
                        sub m' first_list_count
                    else
                        false
    end) in
  match m with
  | lnil => true
  | lcons l' m' => compare_first_list_count m' (list_count l')
  end. *)
  
Definition is_square_matrix {A:Type}(m:listlist A) : bool :=
match m with
| lnil => true
| lcons l' m' => andb (is_matrix m) (Nat.eqb (list_count l') (mat_count m))
end. 

(* OLD
Definition is_square_matrix_bis {A:Type}(m:listlist A) : bool :=
let compare_listElm_and_col := 
  (fix sub (m:listlist A)(first_list_count:nat)(acc:nat) : bool := 
    match m with
    | lnil => if Nat.eqb first_list_count acc then
                true
              else
                false
    | lcons l' m' => if andb (Nat.eqb first_list_count (list_count l')) (acc <? first_list_count)  then
                        sub m' first_list_count (acc+1)
                    else
                        false
    end) in
  match m with
  | lnil => true
  | lcons l' m' => compare_listElm_and_col m' (list_count l') 1
  end.  *)

(* Permet de récupérer la n ième colonne d'une [listlist]  *)
Fixpoint get_col {A:Type}(m:listlist A)(n:nat): clist A :=
  match m, n with
  | lnil, _ => nil
  | lcons l m', 0 => l
  | lcons l m', S n' => get_col m' (n')
  end.

(* Permet de récupérer un élément situé à la ligne row et la colonne nat d'une [listlist] *)
Fixpoint get_mat_elm {A:Type}(m:listlist A)(row:nat)(col:nat): option :=
  get_list_elm (get_col m col) row.
End listlist.

Implicit Arguments lnil [A].
Implicit Arguments lcons [A].

(* Permet d'alléger le code lorsqu'on récupère une région à partir d'une option *)
Definition get_mat_reg (m:listlist region)(row:nat)(col:nat): region :=
  option_elim Z (get_mat_elm m row col). 

Definition mylistlist := lcons [0] (lcons [1] lnil ).
Eval compute in mylistlist.
Definition mylistlist2 := lcons [OO Z,OI Z] (lcons [II Z,IO Z] lnil ).
Eval compute in mylistlist2.

Notation "'{ }" := lnil : type_scope.
Notation "'{ x , .. , y }" := (lcons x .. (lcons y lnil) ..) : type_scope.

(* Permet de vérifier qu'une région est dans une matrice. *)
Fixpoint is_in_mat (m:listlist region)(x:region): bool :=
  match m with
  | lnil => false
  | lcons l m' => if is_in_list l x then
                    true
                  else
                    is_in_mat m' x
  end.

(* Permet de récupérer le numéro de la colonne dans laquelle se trouve 
   une region contenue dans une liste de listes de regions.
   Chaque region etant unique dans un partitionnement du plan on a 
   jamais de doublons de region. 
   Donc get_col_region est unique pour un x dans une partition. 
   Potentiellement prouver que toute region est unique dans le plan. *)
Fixpoint get_col_region (m:listlist region)(r:region): option :=
  match m with
  | lnil => None (* r n'est pas dans m *)
  | lcons l m' => if is_in_list l r then
                    Some 0
                  else
                    add_opt (Some 1) (get_col_region m' r)
  end.

Fixpoint get_col_row_region(m:listlist region)(r:region): option * option := 
let col := get_col_region m r in ((col, get_row_region (get_col m (option_elim 0 col)) r)).

Eval compute in get_col_region '{[OO Z,OI Z],[IO Z,IO Z]} (IO Z).

Eval compute in is_in_mat '{[OO Z,OI Z],[IO Z,IO Z]} (II Z).
Eval compute in is_in_mat '{[OO Z,OI Z],[IO Z,IO Z]} (OI Z).

Eval compute in '{[0,1],[3,4]}.
Eval compute in '{[OO Z,OI Z],[II Z]}.
(* Probleme d'homogeneité des listlist *)
Eval compute in get_col '{[0,1],[3,4]} 1.
Eval compute in get_col '{[OO Z],[II Z],[OO Z,OI Z]} 2.

Eval compute in get_mat_elm '{[OO Z, OI Z],[IO Z, II Z],[OO Z,OI Z]} 1 2.
(* Eval compute in get_mat_reg {[OO Z, OI Z],[IO Z, II Z],[OO Z,OI Z]} 1 2. *)

Eval compute in horcat '{[OO Z,OI Z],[II Z]} '{[IO Z]}.
Eval compute in vertcat '{[OO Z,OI Z],[II Z]} '{[IO Z],[II Z]}.
Eval compute in vertcat '{[OO Z,OI Z],[II Z]} '{[IO Z]}.

(* Fixpoint compare_list_count (m:listlist)(n:nat) : bool := 
    match m with
    | lnil => true
    | lcons l' m' => if Nat.eqb n (list_count l') then
                        compare_list_count m' n
                    else
                        false
    end. *)

Eval compute in is_matrix '{[OO Z,II Z],[OO Z, II Z]}.
Eval compute in is_square_matrix '{[]}.
Eval compute in is_square_matrix '{[1,2]}.
Eval compute in is_square_matrix '{[OO Z]}.
Eval compute in is_square_matrix '{[OO Z,OI Z]}.
Eval compute in is_square_matrix '{[OO Z,II Z],[IO Z,OO Z]}.
Eval compute in is_square_matrix '{[1,2],[3,4]}.
Eval compute in is_square_matrix '{[1,2,3],[4,5,6],[7,8,9]}.

(* Essayer de généraliser la construction des fonctions de même structure mais de type different, ie: equal_list et equal_listlist par exemple. 
   Trouver un moyen d'exprimer les cas du match en général. *)
Fixpoint equal_listlist_region (m1 m2:listlist region): bool :=
match m1, m2 with 
| lnil, lnil => true
| lcons l1 m1', lcons l2 m2' => if(equal_list_region l1 l2) then equal_listlist_region m1' m2' else false
| _, _ => false
end.

Eval compute in equal_listlist_region '{[OO Z, IO Z], [II Z, OI Z]} '{[OO Z, IO Z], [IO Z, OI Z]}.

(* ### Preuves ### *)

Theorem horcat_count {A:Type}(m1 m2:listlist A): 
mat_count (horcat m1 m2) = mat_count m1 + mat_count m2 .
Proof. 
  induction m1.
  reflexivity.
  simpl. 
  rewrite IHm1. 
  reflexivity.
Qed.

Theorem vertcat_count {A:Type}(m1 m2:listlist A): 
mat_count (vertcat m1 m2) = min (mat_count m1) (mat_count m2).
Proof.
Admitted.

Theorem rel_vertcat_lcons {A:Type}(m1 m2:listlist A)(l1 l2:clist A):
vertcat (lcons l1 m1) (lcons l2 m2) = lcons (l1 ++ l2) (vertcat m1 m2) .
Proof.
  reflexivity.
Qed.

Theorem rel_vertcat_concatlist {A:Type}(m1 m2:listlist A)(col:nat): 
get_col (vertcat m1 m2) col = get_col m1 col ++ get_col m2 col .
Proof.
Admitted.

Theorem getcol_vertcat_count {A:Type}(m1 m2:listlist A)(col:nat): 
list_count (get_col (vertcat m1 m2) col) = list_count (get_col m1 col) + list_count (get_col m2 col).
Proof.
  rewrite <- concat_list_count. 
  rewrite rel_vertcat_concatlist. 
  reflexivity.
Qed. 

Theorem double_square_concat_is_square {A:Type}(m1 m2 m3 m4:listlist A): 
is_square_matrix m1 = true -> is_square_matrix m2 = true -> is_square_matrix m3 = true -> is_square_matrix m4 = true ->
is_square_matrix (vertcat (horcat m1 m2) (horcat m3 m4)) = true.
Proof.
  Admitted.
(* intros.
  unfold is_square_matrix.
  rewrite vertcat_count.
  rewrite ?horcat_count. *)

Theorem is_matrix_homogeneous {A:Type}(a b:nat)(m:listlist A):
is_matrix m = true -> list_count (get_col m a) = list_count (get_col m b).
Proof.
  Admitted.
 (* unfold is_matrix. 
  destruct m. 
  trivial.
  simpl. *)