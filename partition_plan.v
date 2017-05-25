(* lundi 5/06 9h: rendre code + rapport/presentation orale latex (10-15 pages rapport + 15 pages presentation)
style pour les transparent latex: beamer (preparer une quinzaine de transparents)
soutenance le 5 6 ou 7 juin l'aprem *)
Require Import Arith.
Require Import Arith Omega.
Require Import NAxioms NSub NZDiv.
Require Import region.
Require Import option.
Require Import clist.
Require Import listlist.

(* Permet d'ajouter le prefixe d'une region à l'ensemble des élements d'une liste de region.
   Exemple: prefix_list (II Z) [OO Z, IO Z] => [ II OO Z, II IO Z] *)
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

(* Permet d'effectuer la rotation des régions à chaque partitionnement du plan.
   Voir la fonction f(x) du poly. *)
Definition rot_nat (n : nat) : region -> region :=
    match n mod 4 with
    | 0 => OO
    | 1 => OI
    | 2 => II
    | 3 => IO
    | _ => OO
    end.

(* Quel que soit le niveau de partionnement, on peut récupérer la plus petite matrice
   contenant 4 regions élementaires. Cette matrice à donc 2 lignes et 2 colonnes.
   On a deux possibilités pour partionner le plan:
   - on peut partir de cette matrice pour partionner le plan (approche bottom-up).
   - on peut partir du partionnement de niveau n et construire le partionnement n+1 en concatenant
   le préfixe de chaque région élémentaire à la matrice base_matrix (approche top-down). *)
Definition get_base_matrix(n:nat) : listlist region := 
(vertcat   
           (horcat {[((rot_nat n) Z)]}
                                        {[(rot_nat (n+1)) Z ]} )
           (horcat {[(rot_nat (n+3) Z)]}
                                      {[(rot_nat (n+2)) Z]} ) ).

Eval compute in get_base_matrix 0.

(* On met en place le partitionnement top-down.
   On commence par définir une fonction qui transforme une liste en une matrice 
   en concatenant le prefixe de chaque élement de la liste à la matrice base_matrix. *)
Fixpoint parse_list (l:clist region)(n:nat): listlist region :=
match l with
| nil => lnil
| cons r l' => vertcat (prefix_listlist r (get_base_matrix n)) (parse_list l' n)
end.

Eval compute in parse_list [OO (OO Z)] 0.
Eval compute in parse_list [OO Z] 0.

(* On définit une fonction qui transforme la matrice correspondant à un partionnement 
   de niveau n, en une matrice correspondant à un partionnement de niveau n+1.  *)
Fixpoint parse_mat (m:listlist region)(n:nat): listlist region :=
match m with
| lnil => lnil
| lcons v m' => horcat (parse_list v n) (parse_mat m' n)
end.

Eval compute in parse_mat {[OO Z, OI Z],[IO Z, II Z]} 0.
Eval compute in parse_mat {[OO Z]} 0.

(* Enfin, on définit la fonction inductive de partionnement du plan *)
Definition mat_partition (n:nat)(m:listlist region):listlist region :=
(* La fonction sub sert uniquement à cacher le compteur dans les paramètres de mat_partition *)
(fix sub(n acc:nat)(m:listlist region):listlist region :=
match n with
| O => m
| S n' => sub n' (acc+1) (parse_mat m acc) 
end) n 0 m.

Eval compute in mat_partition 1 {[OO Z]}. 
Eval compute in mat_partition 2 {[OO Z]}.

(* Implementation de l'algo du poly. Probleme à détailler. *)
Definition mat_partition_poly (n:nat)(m:listlist region):listlist region :=
  let sub := (fix sub(n acc:nat)(m:listlist region):listlist region :=
    match n with
    | O => m
    | S n' => let upright := (prefix_listlist ((rot_nat (acc+3)) Z) m) in (
              let upleft := (prefix_listlist ((rot_nat (acc)) Z) m) in (
              let downright := (prefix_listlist ((rot_nat (acc+2)) Z) m) in(
              let downleft := (prefix_listlist ((rot_nat (acc+1)) Z) m) in (
                sub (n') (acc+1) (vertcat (horcat upleft upright) (horcat downleft downright))
              ) ) ) )
    end ) 
    in sub n 0 m.

Eval compute in mat_partition_poly 2 {[OO Z]}.

(* Liste des regions voisines d'une région contenue dans une liste de regions. *)
Definition voisins_list (l:clist region)(r:region):clist region :=
if is_in_list l r then 
(* on peut se permettre de mettre une valeur par défaut de 0 puisqu'on a vérifié 
   que r était dans l. La valeur par défaut ne sera donc jamais utilisée. *)
  let row := option_elim 0 (get_row_region l r) in ( 
            match (0 <? row), (row+1 <? list_count l) with
            | true, true => [ get_list_reg l (row-1), get_list_reg l (row+1) ]
            | true, false => [ get_list_reg l (row-1) ]
            | false, true => [ get_list_reg l (row+1) ]
            | false, false => nil
            end)
else
  nil.

(* le match est equivalent à:
            if andb (0 <? row) (row <? ((list_count l)-1)) then
              get_list_reg l (row-1) :: get_list_reg l (row+1) :: nil
            else if 0 <? row then
              [ get_list_reg l (row-1) ]
            else if row <? ((list_count l)-1) then
              [ get_list_reg l (row+1) ]
            else
              nil )
*)

(* Liste des regions voisines de l'élement situé à la position row d'une liste de regions.
   La différence avec la fonction ci-dessus est que l'élement à la postion row est inclus 
   dans la liste de regions voisines.
   Cette distinction est utile pour la fonction ci-après. *)
Definition voisins_list_row (l:clist region)(row:nat):clist region :=
if row <? (list_count l)  then
           match (0 <? row), (row+1 <? list_count l) with
            | true, true => [ get_list_reg l (row-1), get_list_reg l row, get_list_reg l (row+1) ]
            | true, false => [ get_list_reg l (row-1), get_list_reg l row ]
            | false, true => [ get_list_reg l row, get_list_reg l (row+1) ]
            | false, false => [ get_list_reg l row ]
            end
else
  nil.

(* le match equivaut à:
            if andb (0 <? row) (row <? ((list_count l)-1)) then
              get_list_reg l (row-1) :: get_list_reg l row :: get_list_reg l (row+1) :: nil
            else if 0 <? row then
              get_list_reg l (row-1) :: get_list_reg l row :: nil
            else if row <? ((list_count l)-1) then
              get_list_reg l row :: get_list_reg l (row+1) :: nil
            else
              get_list_reg l row
  *)

Eval compute in voisins_list [OO Z, OI Z, II Z, IO Z] (II Z). 
Eval compute in voisins_list [OO Z, OI Z, II Z, IO Z] (IO Z).  
Eval compute in voisins_list_row [OO Z, OI Z, II Z, IO Z] 3.              

(* Liste des regions voisines d'une région contenue dans le plan. *)
Fixpoint voisins_mat (m:listlist region)(r:region):clist region :=
if is_in_mat m r then
  let col := option_elim 0 (get_col_region m r) in (
    let row := option_elim 0 (get_row_region (get_col m col) r) in (
      match (0 <? col), (col+1 <? mat_count m) with
      | true, true => voisins_list_row (get_col m (col-1)) row ++ voisins_list (get_col m col) r ++ voisins_list_row (get_col m (col+1)) row
      | true, false => voisins_list_row (get_col m (col-1)) row ++ voisins_list (get_col m col) r
      | false, true => voisins_list (get_col m col) r ++ voisins_list_row (get_col m (col+1)) row
      | false, false => voisins_list (get_col m col) r 
      end ) )
else nil.

(* le match equivaut à :
    if andb (0 <? col) (col <? ((mat_count m)-1)) then
      voisins_list_row (get_col m (col-1)) row ++ voisins_list (get_col m col) r ++ voisins_list_row (get_col m (col+1)) row
    else if 0 <? col then
              voisins_list_row (get_col m (col-1)) row ++ voisins_list (get_col m col) r
    else if col <? ((mat_count m)-1) then
              voisins_list (get_col m col) r ++ voisins_list_row (get_col m (col+1)) row
    else
              voisins_list (get_col m col) r ))
  *)

Eval compute in voisins_mat {[OO Z, II Z, OO Z],[II Z, OI Z, OO Z], [II Z, OO Z, II Z]} (OI Z).


Definition diff (n m:nat): nat :=
if (n<?m) then m-n
else n-m.

Eval compute in diff 2 5.

(* Calcul du nombre de regions élementaires maximum qui séparent 2 régions appartenant à la matrice des régions.
   Ce maximum est calculé selon l'axe vertical et l'axe horizontal de la matrice.
   L'interêt de cette fonction est de calculer la largeur minimum du carré contenant 2 régions du plan.
   La largeur de ce carré permettra de déterminer si une region r1 est dans A0 par rapport à une autre region r2. *)
Fixpoint distance_regions_elem (r1 r2:region)(m: listlist region): option :=
  let (col1, row1) := get_col_row_region m r1 in (
  let (col2, row2) := get_col_row_region m r2 in (
    match col1, col2, row1, row2 with
    | Some c1, Some c2, Some r1, Some r2 => Some (Nat.max (diff c1 c2) (diff r1 r2))
    | _, _, _, _ => None 
    end
  )).

Eval compute in (mat_partition 2 {[OO Z]}).
Eval compute in distance_regions_elem (OO(OO(OI Z))) (OO(OI(IO Z))) (mat_partition 2 {[OO Z]}).

(* ############# Preuves diverses ############### *)

Check plus_comm.
Check plus_assoc.

Lemma mod_exhaustive (n m:nat): 
m <> 0 -> ((n + m) mod m) = (n mod m).
intros.
rewrite Nat.add_mod.
rewrite Nat.mod_same.
rewrite plus_0_r.
rewrite Nat.mod_mod.
reflexivity.
assumption.
assumption.
assumption.
Qed.

Theorem rot_nat_mod_4 (n:nat): 
rot_nat (4+n) = rot_nat n.
Proof. 
  unfold rot_nat. 
  rewrite plus_comm. 
  rewrite mod_exhaustive. 
  reflexivity. 
  discriminate. 
Qed.

(* Preuve de l'auto-similarité de la disposition des numéros : toutes les quatre itérations du processus
de partitionnement, on obtient la même disposition des numéros pour les regions élementaires. *)
Theorem base_matrix_mod_4 (n:nat): 
get_base_matrix n = get_base_matrix (n+4).
Proof. 
  unfold get_base_matrix. 
  simpl. 
  rewrite <- (plus_comm 4). 
  rewrite <- ?plus_assoc. 
  rewrite ?rot_nat_mod_4. 
  reflexivity.
Qed.
(* TODO: Montrer qu'une partition est formée à partir de base_matrix ? evident ? *)
 
Check nat_ind.

(*
Theorem foo {A:Type}(m1 m2:listlist A): 
vertcat m1 m2 = { } -> (m1 = lnil) /\ (m2 = lnil) .
Proof.
  Admitted. *)

Theorem base_matrix_is_square (n:nat): 
is_square_matrix (get_base_matrix n) = true.
Proof. 
  reflexivity.
Qed.

(* TODO: Preuve que le partionnement est une matrice carré si on commence par OO Z ou n'importe qu'elle matrice carré *)
Theorem is_partition_square (n:nat)(m:listlist region): is_square_matrix m = true -> is_square_matrix (mat_partition n m) = true .
Proof.
   Admitted.

(* Check Nat.sub_0_r. 
  
Theorem get_col_lcons {A:Type}(m:listlist A)(l:clist A)(col:nat): 
get_col (lcons l m)  (S col) = get_col m col .
Proof.
  simpl.
  reflexivity. 
Qed.

Theorem get_col_0_lcons {A:Type}(m:listlist A)(l:clist A): 
get_col (lcons l m) 0 = l .
Proof.
  reflexivity.
Qed. 

Lemma add_l_0 n : n + 0 = n.
  rewrite plus_comm.
  apply Nat.add_0_l.
Qed.

Lemma O_lt_Sn (n:nat): 0 < S n.
Proof.
  rewrite Nat.lt_succ_r. 
  apply Nat.le_0_l.
Qed.

Lemma O_lt_Sn_bis (n:nat): 0 <? S n = true.
  rewrite Nat.ltb_lt. 
  apply O_lt_Sn.
Qed. *)


(*  TESTS INUTILES
 
  case_eq (vertcat m1 m2). intro. simpl. 

  decompose H.
  lapply bar A m1 m2.
  simpl. unfold vertcat. 

(*
  induction col.
  destruct m1. simpl. reflexivity.
  simpl. destruct m2. simpl. rewrite concat_list_nil. reflexivity.
  simpl. reflexivity.
  destruct (vertcat m1 m2).
  destruct m1. destruct m2. simpl. reflexivity.
  simpl. reflexivity. *)

  destruct m1. simpl. reflexivity.
  destruct m2. simpl. rewrite concat_list_nil. reflexivity.
  induction col. simpl. reflexivity.
  simpl. rewrite Nat.sub_0_r.

  induction col.
  case m1. reflexivity.
  intros. case m2. simpl. rewrite concat_list_nil. reflexivity.
  intros. simpl. reflexivity.
  unfold get_col. unfold vertcat. 

  induction col.
  case m1. reflexivity.
  intros. case m2. simpl. rewrite concat_list_nil. reflexivity.
  intros. simpl. reflexivity.
  case m1. simpl. reflexivity.
  intros. case m2. simpl. rewrite Nat.sub_0_r. rewrite concat_list_nil. reflexivity.
  intros. simpl. rewrite Nat.sub_0_r.
  rewrite IHcol.
  
  rewrite get_col_lcons.
  
   reflexivity.
  case col. rewrite get_col_0_lcons.

  case m2. simpl. rewrite concat_list_nil. reflexivity.
  intros. simpl. reflexivity.
  intros.
  rewrite get_col_lcons.

  simpl. rewrite Nat.sub_0_r.
  
  induction m1. reflexivity.
  case col. rewrite get_col_0_lcons.
  case m2. simpl. rewrite concat_list_nil. reflexivity.
  intros.
  rewrite foo. case col.
  simpl. reflexivity.
  intros.
  simpl. rewrite Nat.sub_0_r.

  unfold vertcat.
  induction m1 . reflexivity.
  case_eq m2 . simpl. rewrite concat_list_nil. reflexivity.
  simpl. case_eq col. simpl. reflexivity.
  simpl. intros. rewrite Nat.sub_0_r.
  unfold get_col.
  rewrite concat_list_nil. reflexivity.

  induction m2 as [|l2 m2']. simpl. rewrite concat_list_nil. reflexivity.
  simpl. 
  destruct col. reflexivity. 
  rewrite O_lt_Sn_bis. simpl. rewrite Nat.sub_0_r.
   reflexivity.

  unfold vertcat.
  destruct m1 as [|l1 m1']. simpl. reflexivity. destruct m2 as [|l2 m2']. 
  simpl. rewrite concat_list_nil. reflexivity.
  simpl. destruct col. simpl. reflexivity. rewrite O_lt_Sn_bis. reflexivity. *)