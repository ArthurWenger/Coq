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

Fixpoint equal_region (n m : region) : bool :=
    match n, m with
    | Z , Z => true
    | OO n' , OO m' => equal_region n' m'
    | OI n' , OI m' => equal_region n' m'
    | IO n' , IO m' => equal_region n' m'
    | II n' , II m' => equal_region n' m'
    | _, _ => false
    end.

Fixpoint concat_region(p:region)(s:region):region := 
  match p with
  | Z => s
  | OO p' => OO(concat_region p' s)
  | OI p' => OI(concat_region p' s)
  | IO p' => IO(concat_region p' s)
  | II p' => II(concat_region p' s)
  end.

(* Notation "x =? y" := (equal_region x y) : region_scope.
  Locate "=?".
  Open Scope region_scope.
  Eval compute in (OO Z) =? (OO Z). *)

(* Permet d'éliminer les paramètres par défaut dans les définitions sur des types polymorphes.
   Par exemple si un élement n'est pas dans une liste de region on pourra renvoyer None plutot qu'une valeur par défaut comme Z.
   Voir [natoption] pour plus d'infos. *)
Inductive options {A:Type}: Type :=
  | Some : A -> options
  | None : options. 

(* Permet d'additioner des options de type nat sans passer par des fonctions auxiliaires. *)
Definition add_opt (a b:@options nat):@options nat :=
match a, b with
| Some a', Some b' => Some (a'+b')
| _, _ => None
end.
(* Permet d'extraire l'élement d'un type [options] et de renvoyer 
   une valeur par défaut fournie en argument dans le cas [None]. *)
Definition option_elim {A:Type} (d: A) (o: options): A :=
  match o with
  | Some n' => n'
  | None => d
  end.

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
Fixpoint get_list_elm {A:Type}(l:clist A)(n:nat): options :=
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
Fixpoint get_row_region (l:clist region)(x:region): options :=
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

(* Permet d'alléger le code lorsqu'on récupère des region à partir d'options *)
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

Fixpoint is_matrix_bis {A:Type}(m:listlist A) : bool.
case_eq m. intro H. exact true.
intros. pose (e := list_count c).
case_eq l. intro H0. exact true.
intros. exact (Nat.eqb e (list_count c0) && (is_matrix_bis A l0)).
Qed. 

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
| lcons l' m' => andb (is_matrix m) (list_count l' =? mat_count m)
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
Fixpoint get_mat_elm {A:Type}(m:listlist A)(row:nat)(col:nat): options :=
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

Notation "{ }" := lnil.
Notation "{ x , .. , y }" := (lcons x .. (lcons y lnil) ..).

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
Fixpoint get_col_region (m:listlist region)(x:region): options :=
  match m with
  | lnil => None (* x n'est pas dans m *)
  | lcons l m' => if is_in_list l x then
                    Some 0
                  else
                    add_opt (Some 1) (get_col_region m' x)
  end.

 Eval compute in get_col_region {[OO Z,OI Z],[IO Z,IO Z]} (OI Z).

Eval compute in is_in_mat {[OO Z,OI Z],[IO Z,IO Z]} (II Z).
Eval compute in is_in_mat {[OO Z,OI Z],[IO Z,IO Z]} (OI Z).

Eval compute in {[0,1],[3,4]}.
Eval compute in {[OO Z,OI Z],[II Z]}.
(* Probleme d'homogeneité des listlist *)
Eval compute in get_col {[0,1],[3,4]} 1.
Eval compute in get_col {[OO Z],[II Z],[OO Z,OI Z]} 2.

Eval compute in get_mat_elm {[OO Z, OI Z],[IO Z, II Z],[OO Z,OI Z]} 1 2.
(* Eval compute in get_mat_reg {[OO Z, OI Z],[IO Z, II Z],[OO Z,OI Z]} 1 2. *)

Eval compute in horcat {[OO Z,OI Z],[II Z]} {[IO Z]}.
Eval compute in vertcat {[OO Z,OI Z],[II Z]} {[IO Z],[II Z]}.
Eval compute in vertcat {[OO Z,OI Z],[II Z]} {[IO Z]}.

(* Fixpoint compare_list_count (m:listlist)(n:nat) : bool := 
    match m with
    | lnil => true
    | lcons l' m' => if Nat.eqb n (list_count l') then
                        compare_list_count m' n
                    else
                        false
    end. *)

Eval compute in is_matrix_bis {[OO Z,II Z],[OO Z]}.
Eval compute in is_matrix {[OO Z,II Z],[OO Z, II Z]}.
Eval compute in is_square_matrix {[]}.
Eval compute in is_square_matrix {[1,2]}.
Eval compute in is_square_matrix {[OO Z]}.
Eval compute in is_square_matrix {[OO Z,OI Z]}.
Eval compute in is_square_matrix {[OO Z,II Z],[IO Z,OO Z]}.
Eval compute in is_square_matrix {[1,2],[3,4]}.
Eval compute in is_square_matrix {[1,2,3],[4,5,6],[7,8,9]}.

(* Essayer de généraliser la construction des fonctions de même structure mais de type different, ie: equal_list et equal_listlist par exemple. 
   Trouver un moyen d'exprimer les cas du match en général. *)
Fixpoint equal_listlist_region (m1 m2:listlist region): bool :=
match m1, m2 with 
| lnil, lnil => true
| lcons l1 m1', lcons l2 m2' => if(equal_list_region l1 l2) then equal_listlist_region m1' m2' else false
| _, _ => false
end.

Eval compute in equal_listlist_region {[OO Z, IO Z], [II Z, OI Z]} {[OO Z, IO Z], [IO Z, OI Z]}.

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

Lemma plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [| n'].
  simpl. rewrite -> plus_0_r. reflexivity.
  simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Lemma plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n'].
  reflexivity.
  simpl. rewrite -> IHn'. reflexivity.
Qed.

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
 
Check nat_ind.

Theorem rel_vertcat_lcons {A:Type}(m1 m2:listlist A)(l1 l2:clist A):
vertcat (lcons l1 m1) (lcons l2 m2) = lcons (l1 ++ l2) (vertcat m1 m2) .
Proof.
  reflexivity.
Qed.

(*
Theorem foo {A:Type}(m1 m2:listlist A): 
vertcat m1 m2 = { } -> (m1 = lnil) /\ (m2 = lnil) .
Proof.
  Admitted. *)

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

Theorem base_matrix_is_square (n:nat): 
is_square_matrix (get_base_matrix n) = true.
Proof. 
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

(* TODO: Preuve que le partionnement est une matrice carré si on commence par OO Z ou n'importe qu'elle matrice carré *)
Theorem partition_is_square (n:nat)(m:listlist region): is_square_matrix m = true -> is_square_matrix (mat_partition n m) = true .
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