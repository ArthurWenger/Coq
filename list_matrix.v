(* lundi 5/06 9h: rendre code + rapport/presentation orale latex (10-15 pages rapport + 15 pages presentation)
style pour les transparent latex: beamer (preparer une quinzaine de transparents)
soutenance le 5 6 ou 7 juin l'aprem *)
Require Import Arith.
Require Import Arith Omega.
Require Import NAxioms NSub NZDiv.

Set Implicit Arguments.

Inductive region : Type :=
| Z : region
| OO : region -> region
| OI : region -> region
| IO : region -> region
| II : region -> region.

hello

Fixpoint equal_region (n m : region) : bool :=
    match n, m with
    | Z , Z => true
    | Z , _ => false
    | OO n' , OO m' => equal_region n' m'
    | OO n' , _ => false
    | OI n' , OI m' => equal_region n' m'
    | OI n' , _ => false
    | IO n' , IO m' => equal_region n' m'
    | IO n' , _ => false
    | II n' , II m' => equal_region n' m'
    | II n' , _ => false
    end.


Section customlist.
Variable A:Type.
Inductive clist : Type :=
  | nil : clist
  | cons : A -> clist -> clist.

Fixpoint list_count (l:clist) : nat := 
  match l with
  | nil => 0
  | cons n l' =>  1 + list_count l'
  end.

Fixpoint concat_list (l1 l2:clist): clist :=
match l1 with
| nil => l2
| cons n l' => cons n (concat_list l' l2)
end.

Fixpoint get_list_elm (l:clist)(n:nat)(zero:A): A :=
  match l with
  | nil => zero
  | cons x l' => if (0 <? n) then 
                      get_list_elm l' (n-1) zero
                 else x
  end.
End customlist.
Implicit Arguments nil [A].

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).
Notation "x ++ y" := (concat_list x y) (at level 60, right associativity).

Fixpoint is_in_list (l:clist region)(x:region): bool :=
match l with
| nil => false
| cons n l' => if equal_region x n then
                true
               else
                is_in_list l' x
end.

Fixpoint get_row_region (l:clist region)(x:region):nat :=
match l with
| nil => 0 (* ce cas n'est jamais utilisé si on verifie que x est dans l *)
| cons n l' => if equal_region x n then
                0
               else
                1 + get_row_region l' x
end.

Eval compute in [1].
Eval compute in [OO Z].

Eval compute in list_count [OO Z, IO(II Z), OO Z, IO Z].
Eval compute in list_count [0, 1, 2].
Eval compute in list_count [].

Eval compute in concat_list [1,2] [3,4].
Eval compute in concat_list [OO Z,IO Z] [OI Z,II Z].

Eval compute in get_list_elm [1,2,3] 1 0.

Eval compute in is_in_list [OO Z,OI Z,IO Z] (II Z).  
Eval compute in is_in_list [OO Z,OI Z,IO Z] (IO Z). 


Definition get_list_reg (l:clist region)(n:nat): region := get_list_elm l n Z.

Eval compute in get_list_reg [OO Z,IO Z,II Z] 2.
Eval compute in get_row_region [OO Z, IO Z, II Z] (II Z).

Section listlist.
Variable A:Type.
Inductive listlist : Type :=
  | lnil : listlist
  | lcons : clist A -> listlist -> listlist.

Fixpoint conc_mat_horizontal (l1 l2:listlist): listlist :=
match l1 with
| lnil => l2
| lcons v l' => lcons v (conc_mat_horizontal l' l2)
end.

Fixpoint conc_mat_vertical (l1 l2:listlist): listlist :=
match l1 with
| lnil => l2
| lcons v1 l1' => match l2 with
                | lnil => l1
                | lcons v2 l2' => lcons (concat_list v1 v2) (conc_mat_vertical l1' l2')
                end
end.

(* Permet de vérifier qu'une liste de liste est une matrice *)
Definition is_matrix(m:listlist) : bool :=
  let compare_first_list_count := 
  (fix sub (m:listlist)(n:nat) : bool := 
    match m with
    | lnil => true
    | lcons l' m' => if Nat.eqb n (list_count l') then
                        sub m' n
                    else
                        false
    end) in
  match m with
  | lnil => true
  | lcons l' m' => compare_first_list_count m' (list_count l')
  end.

(* Potentiellement remplacer les fonctions imbriquées par une fonction generale *)
Definition is_square_matrix(m:listlist) : bool :=
let compare_listElm_and_col := 
  (fix sub (m:listlist)(n:nat)(acc:nat) : bool := 
    match m with
    | lnil => if Nat.eqb n acc then
                true
              else
                false
    | lcons l' m' => if andb (Nat.eqb n (list_count l')) (acc <? n)  then
                        sub m' n (acc+1)
                    else
                        false
    end) in
  match m with
  | lnil => true
  | lcons l' m' => if Nat.eqb (list_count l') 0 then
                      true
                   else
                      compare_listElm_and_col m' (list_count l') 1
  end.

Fixpoint get_col (m:listlist)(n:nat): clist A :=
  match m with
  | lnil => nil
  | lcons l' m' => if (0 <? n) then 
                      get_col m' (n-1)
                   else l'
  end.

Fixpoint get_mat_elm (m:listlist)(row:nat)(col:nat)(zero:A): A :=
  let target_col := get_col m col in
  get_list_elm target_col row zero.

(* nombre de colonnes dans une matrice *)
Fixpoint mat_count (m:listlist): nat :=
match m with
| lnil => 0
| lcons l m' => 1 + mat_count m'
end.

End listlist.

Implicit Arguments lnil [A].

Fixpoint get_mat_reg (m:listlist region)(row:nat)(col:nat): region :=
  get_mat_elm m row col Z.

Definition mylistlist := lcons [0] (lcons [1] lnil ).
Eval compute in mylistlist.
Definition mylistlist2 := lcons [OO Z,OI Z] (lcons [II Z,IO Z] lnil ).
Eval compute in mylistlist2.

Notation "{ }" := lnil.
Notation "{ x , .. , y }" := (lcons x .. (lcons y lnil) ..).

Fixpoint is_in_mat (m:listlist region)(x:region): bool :=
  match m with
  | lnil => false
  | lcons l m' => if is_in_list l x then
                    true
                  else
                    is_in_mat m' x
  end.

(* Chaque region etant unique dans un partitionnement du plan on a jamais de doublons de region. 
   Donc get_col_region est unique pour un x dans une partition. 
   Potentiellement prouver que toute region est unique dans le plan. *)
Fixpoint get_col_region (m:listlist region)(x:region): nat :=
  match m with
  | lnil => 0 (* ce cas n'est jamais utilisé si on verifie que x est dans m *)
  | lcons l m' => if is_in_list l x then
                    0
                  else
                    1 + get_col_region m' x
  end.

 Eval compute in get_col_region {[OO Z,OI Z],[IO Z,IO Z]} (OI Z).

Eval compute in is_in_mat {[OO Z,OI Z],[IO Z,IO Z]} (II Z).
Eval compute in is_in_mat {[OO Z,OI Z],[IO Z,IO Z]} (OI Z).

Eval compute in {[0,1],[3,4]}.
Eval compute in {[OO Z,OI Z],[II Z]}.
(* Probleme d'homogeneité des listlist *)
Eval compute in get_col {[0,1],[3,4]} 2.
Eval compute in get_col {[OO Z],[II Z],[OO Z,OI Z]} 3.

Eval compute in get_mat_reg {[OO Z, OI Z],[IO Z, II Z],[OO Z,OI Z]} 2 3.

Eval compute in conc_mat_horizontal {[OO Z,OI Z],[II Z]} {[IO Z]}.
Eval compute in conc_mat_vertical {[OO Z,OI Z],[II Z]} {[IO Z],[II Z]}.

(* Fixpoint compare_list_count (m:listlist)(n:nat) : bool := 
    match m with
    | lnil => true
    | lcons l' m' => if Nat.eqb n (list_count l') then
                        compare_list_count m' n
                    else
                        false
    end. *)



Eval compute in is_matrix {[OO Z,II Z],[OO Z]}.
Eval compute in is_square_matrix {[]}.
Eval compute in is_square_matrix {[1,2]}.
Eval compute in is_square_matrix {[OO Z]}.
Eval compute in is_square_matrix {[OO Z,OI Z]}.
Eval compute in is_square_matrix {[OO Z,II Z],[IO Z,OO Z]}.
Eval compute in is_square_matrix {[1,2],[3,4]}.
Eval compute in is_square_matrix {[1,2,3],[4,5,6],[7,8,9]}.

Fixpoint concat_region(p:region)(s:region):region := 
  match p with
  | Z => s
  | OO p' => OO(concat_region p' s)
  | OI p' => OI(concat_region p' s)
  | IO p' => IO(concat_region p' s)
  | II p' => II(concat_region p' s)
  end.

Fixpoint prefix_list(r: region)(l:clist region): clist region :=
match l with
| nil => l
| cons n l' => cons (concat_region r n) (prefix_list r l')  
end.

(* Fixpoint prefix_list_bis(r: region -> region)(l:clist region): clist region :=
match l with
| nil => l
| cons n l' => cons (r n) (prefix_list_bis r l')  
end. *)

Eval compute in prefix_list (II Z) [OO Z, IO Z].

Fixpoint prefix_listlist(r: region)(m:listlist region): listlist region :=
match m with
| lnil => m
| lcons v m' => lcons (prefix_list r v) (prefix_listlist r m')
end.

Eval compute in prefix_listlist (II Z) {[OO Z, IO Z],[OI Z]}.

(* Fixpoint prefix_listlist_bis(r: region -> region)(m:listlist region): listlist region :=
match m with
| lnil => m
| lcons v m' => lcons (prefix_list_bis r v) (prefix_listlist_bis r m')
end. *)

Definition rot_nat (n : nat) : region -> region :=
    match n mod 4 with
    | 0 => OO
    | 1 => OI
    | 2 => II
    | 3 => IO
    | _ => OO
    end.

Definition get_base_matrix(n:nat) : listlist region := 
(conc_mat_vertical   
           (conc_mat_horizontal {[((rot_nat n) Z)]}
                                        {[(rot_nat (n+1)) Z ]} )
           (conc_mat_horizontal {[(rot_nat (n+3) Z)]}
                                      {[(rot_nat (n+2)) Z]} ) ).

Eval compute in get_base_matrix 0.

Fixpoint parse_list (l:clist region)(n:nat): listlist region :=
match l with
| nil => lnil
| cons r l' => conc_mat_vertical (prefix_listlist r (get_base_matrix n)) (parse_list l' n)
end.

Eval compute in get_base_matrix 0.
Eval compute in parse_list [OO (OO Z)] 0.

Fixpoint parse_mat (m:listlist region)(n:nat): listlist region :=
match m with
| lnil => lnil
| lcons v m' => conc_mat_horizontal (parse_list v n) (parse_mat m' n)
end.

Eval compute in parse_mat {[OO Z, OI Z],[IO Z, II Z]} 0.

Eval compute in parse_list [OO Z] 0.
Eval compute in parse_mat {[OO Z]} 0.

Definition mat_partition (n:nat)(m:listlist region):listlist region :=
let sub := 
(fix sub(n acc:nat)(m:listlist region):listlist region :=
match n with
| O => m
| S n' => sub n' (acc+1) (parse_mat m acc) 
end) in 
sub n 0 m.
Eval compute in mat_partition 1 {[OO Z]}. 
Eval compute in mat_partition 2 {[OO Z]}.

Definition voisins_list (l:clist region)(r:region):clist region :=
if is_in_list l r then
  let row := get_row_region l r in (
            if andb (0 <? row) (row <? ((list_count l)-1)) then
              get_list_reg l (row-1) :: get_list_reg l (row+1) :: nil
            else if 0 <? row then
              [ get_list_reg l (row-1) ]
            else if row <? ((list_count l)-1) then
              [ get_list_reg l (row+1) ]
            else
              nil )
else
  nil.

Definition voisins_list_row (l:clist region)(row:nat):clist region :=
if row <? (list_count l)  then
            if andb (0 <? row) (row <? ((list_count l)-1)) then
              get_list_reg l (row-1) :: get_list_reg l row :: get_list_reg l (row+1) :: nil
            else if 0 <? row then
              get_list_reg l (row-1) :: get_list_reg l row :: nil
            else if row <? ((list_count l)-1) then
              get_list_reg l row :: get_list_reg l (row+1) :: nil
            else
              nil
else
  nil.

Eval compute in voisins_list [OO Z, OI Z, II Z, IO Z] (II Z). 
Eval compute in voisins_list [OO Z, OI Z, II Z, IO Z] (IO Z).  
Eval compute in voisins_list_row [OO Z, OI Z, II Z, IO Z] 3.              


Fixpoint voisins_mat (m:listlist region)(r:region):clist region :=
if is_in_mat m r then
  let col := get_col_region m r in (
    let row := get_row_region (get_col m col) r in (
    if andb (0 <? col) (col <? ((mat_count m)-1)) then
      voisins_list_row (get_col m (col-1)) row ++ voisins_list (get_col m col) r ++ voisins_list_row (get_col m (col+1)) row
    else if 0 <? col then
              voisins_list_row (get_col m (col-1)) row ++ voisins_list (get_col m col) r
    else if col <? ((mat_count m)-1) then
              voisins_list (get_col m col) r ++ voisins_list_row (get_col m (col+1)) row
    else
              voisins_list (get_col m col) r ))
else nil.

Eval compute in voisins_mat {[OO Z, II Z, OO Z],[II Z, OI Z, OO Z], [II Z, OO Z, II Z]} (OI Z).