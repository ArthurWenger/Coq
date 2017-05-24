Require Import Arith.
Require Import NAxioms NSub NZDiv.

(**########################################################################**)


(* Une region est repérée par un code.
   Equivaut à un codage en base 4. *)
Inductive region : Type :=
| Z : region
| OO : region -> region
| OI : region -> region
| IO : region -> region
| II : region -> region.
(* Ici on a pas de probleme d'unicité car il n'y pas de réelle conversion en base 4
   On a donc pas:  OI Z <=> OI OO Z  *)

Fixpoint inc_region (n : region) : region :=
    match n with
    | Z => OI Z
    | OO n' => OI n'
    | OI n' => IO n'
    | IO n' => II n'
    | II n' => OO (inc_region n')
    end.

Example test1 : inc_region (OI (II Z)) = IO (II Z).
Proof. simpl. reflexivity. Qed.

Fixpoint mult4 (n:nat) : nat :=
    match n with
    | O => O
    | S n' => 4 + mult4 n'
    end.

Fixpoint region2nat (n:region) : nat :=
    match n with
    | Z => O
    | OO n' => mult4 (region2nat n')
    | OI n' => mult4 (region2nat n') + 1
    | IO n' => mult4 (region2nat n') + 2
    | II n' => mult4 (region2nat n') + 3
    end.

(* Le codage d'une region se lit donc de droite a gauche *)
Example test2 : region2nat (IO (II (OI Z))) = 30. (* 1x4² + 3x4 + 2 *)
Proof. simpl. reflexivity. Qed.

(* Niveau d'une region *)
Fixpoint rank (n:region) : nat :=
    match n with
    | Z => 0
    | OO n' | OI n' | IO n' | II n' => 1 + rank n'
    end.

Eval compute in rank (II (OI Z)).

(* permet d'obtenir les regions de niveau n contenant une region r <=> An *)
Fixpoint region_at_rank (r:region) (n:nat) : region :=
    if Nat.eqb (rank r) n || Nat.eqb (rank r) 1 then
        r
    else
        match r with 
            | Z => Z
            | OO r' | OI r' | IO r' | II r' => region_at_rank r' n 
        end.

Eval compute in region_at_rank (OO (II (OI Z))) 2.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Notation "x == y" := (beq_nat x y) (at level 40, left associativity) : nat_scope.

Fixpoint same_rank (n1 n2 : region) : bool :=
    rank (n1) == rank (n2).

Eval compute in same_rank (II(OI(OO Z))) (OO(II(II Z))).


Fixpoint equal_region (n m : region) : bool :=
    match n, m with
    | Z , Z => true
    | OO n' , OO m' => equal_region n' m'
    | OI n' , OI m' => equal_region n' m'
    | IO n' , IO m' => equal_region n' m'
    | II n' , II m' => equal_region n' m'
    | _, _ => false
    end.
(* Notation "x =? y" := (equal_region x y) : region_scope.*)

Eval compute in equal_region (II(OI(OO Z))) (OO(II(II Z))).
Eval compute in equal_region (II(OI(OO Z))) (II(OI(OO Z))).

Fixpoint first_region (n : region) : region :=
    match rank n with
    | 1 => n
    | _ => match n with 
           | Z => Z
           | OO n' => first_region n'
           | OI n' => first_region n'
           | IO n' => first_region n'
           | II n' => first_region n'
           end
    end.

Eval compute in first_region (II(OI(OO Z))).

Fixpoint last_region (n : region) : region :=
    match n with 
    | Z => Z
    | OO n' => OO Z
    | OI n' => OI Z
    | IO n' => IO Z
    | II n' => II Z
    end.

Eval compute in last_region (II(OI(OO Z))).

(* region en commun <=> relation d'inclusion entre les régions *)

Definition reverse (r : region) : region :=
    (fix _reverse (rem res:region): region :=
        match rem with 
        | Z => res
        | OO rem' => _reverse rem' (OO(res))
        | OI rem' => _reverse rem' (OI(res))
        | IO rem' => _reverse rem' (IO(res))
        | II rem' => _reverse rem' (II(res))
        end ) r Z.

Eval compute in reverse (II(OI(OO Z))).

Fixpoint shared_region (n m : region) : region :=   
    let rev_n := reverse n in(
    let rev_m := reverse m in(
        (fix _shared_region (n m res: region) : region :=
            match n, m with
            | OO n' , OO m' => _shared_region n' m' (OO(res))
            | OI n' , OI m' => _shared_region n' m' (OI(res))
            | IO n' , IO m' => _shared_region n' m' (IO(res))
            | II n' , II m' => _shared_region n' m' (II(res))
            | _, _  => res
            end ) rev_n rev_m Z
    )).

Eval compute in shared_region (IO(OI(OO Z))) (II(OI(OO Z))) .

(* regions disjointes *)
Fixpoint has_shared_region (n m : region) : bool :=
    match shared_region n m with
    | Z => false
    | _ => true
    end.

Eval compute in has_shared_region (II(OI(II Z))) (II(OI(OO Z))) .
Eval compute in has_shared_region (IO(OI(II Z))) (II(OI(OO Z))) .

(* Hiérarchie des régions*)
Inductive treeRegion :=
  | Leaf : region -> treeRegion
  | Node : region -> treeRegion -> treeRegion -> treeRegion -> treeRegion -> treeRegion.

Notation t := treeRegion.

Check Node (OO Z) (Leaf (OO Z)) (Leaf (OO Z)) (Leaf (OO Z)) (Leaf (OO Z)).
Definition testTree : treeRegion :=  Node (OO Z) (Leaf (OO (OO Z))) 
                                    (Leaf (OI (OO Z))) 
                                    (Leaf (IO (OO Z))) 
                                    (Leaf (II (OO Z))).
Check testTree.

(* Hauteur de l'arbre <=> niveau du partitionnement *)
Fixpoint height (m : t) : nat :=
  match m with
  | Leaf _ => 0
  | Node _ l _ _ _ => 1 + height l
  end.

Eval compute in height testTree.

(* Nombre de regions total (tous niveaux confondus = Node + Leaf) *)
Fixpoint cardinal (m : t) : nat :=
  match m with
   | Leaf _ => 1
   | Node _ l _ _ _ => 1 + 4 * cardinal l (* on ajoute 1 pour compter les noeuds ainsi que la racine de l'arbre 
                                             par exemple avec un abre de niveau 2 on aurait: 1+4x(1+4x1) = 1+4+4² *)
  end.

Eval compute in cardinal testTree.

(* Nombre de feuille dans l'arbre <=> nombre de regions de niveau max *)
Fixpoint cardinal_leaf (m : t) : nat :=
  match m with
   | Leaf _ => 1
   | Node _ l _ _ _ => 4 * cardinal_leaf l
  end.

Eval compute in cardinal_leaf testTree.

(* Rotation anti-horaire des regions pour chaque niveau de partitionnement *)
Definition rotation (n : nat) : region -> region :=
    match n mod 4 with
    | 0 => OO
    | 1 => OI
    | 2 => II
    | 3 => IO
    | _ => OO
    end.
(* TODO: Supprimer le cas superflu en utilisant (h : (n mod 4) < 4) OU
Lemma mod_exhaustive: forall n m : nat, m <> 0 -> ((n + m) mod m) = (n mod m).
intros.
rewrite Nat.add_mod.
rewrite Nat.mod_same.
rewrite plus_0_r.
rewrite Nat.mod_mod.
reflexivity.
assumption.
assumption.
assumption.
Qed. *)

(* Hiérarchie des partitions du plan *)
(* part permet de compter les iterations avec un parametre supplémentaire. 
   Permet d'éviter d'utiliser "ranq q" sur chaque feuille *)
Fixpoint part (m:t)(n:nat)(acc:nat):t:=
        match n with 
        | 0 => m
        | S n' => match m with
                | Leaf q => Node q (part (Leaf (rotation acc q)) n' (acc+1)) 
                                   (part (Leaf (rotation (acc+1) q)) n' (acc+1)) 
                                   (part (Leaf (rotation (acc+2) q)) n' (acc+1)) 
                                   (part (Leaf (rotation (acc+3) q)) n' (acc+1))
                | Node q l ml mr r => Node q (part l n' (acc+1)) 
                                            (part ml n' (acc+1)) 
                                            (part mr n' (acc+1)) 
                                            (part r n' (acc+1))
                end  
        end.

Fixpoint partition (m : t) (n : nat) : t :=
    part m n 0.

(* OLD sans rotation
Fixpoint partition (m : t) (n : nat) : t :=
    match n with 
    | 0 => m
    | S n' => match m with
              | Leaf q => Node q (partition (Leaf (OO(q))) n') 
                                 (partition (Leaf (OI(q))) n') 
                                 (partition (Leaf (IO(q))) n') 
                                 (partition (Leaf (II(q))) n')
              | Node q l ml mr r => Node q (partition l n') 
                                           (partition ml n') 
                                           (partition mr n') 
                                           (partition r n')
              end  
    end.
*)

Definition init_tree : treeRegion := Leaf (OO Z).

Definition is_empty_tree m := 
    match m with 
    | Leaf _ => true 
    | _ => false 
    end.

Eval compute in partition init_tree 0.
Eval compute in partition init_tree 1.
Eval compute in partition init_tree 2.
Eval compute in cardinal_leaf (partition init_tree 2).

(* utile pour obtenir le code des regions voisines *)
Definition getCode (m : t) : region :=
    match m with
    | Leaf q | Node q _ _ _ _ => q
    end.

Eval compute in getCode (Leaf (OI Z)).
Eval compute in getCode (Node (II Z) (Leaf (OO Z)) (Leaf (OO Z)) (Leaf (OO Z)) (Leaf (OO Z))).

(* TODO: trouver un moyen de définir une region voisine
         soit en partant de la hierarchie soit en creant la matrice des régions *)

(* ########## Modélisation du réseau (noeud / graphe / chemin / route ...) ###########*)
Section network.
(* k = rayon de A0 en terme de regions elementaires *)
Variable k : nat.

(* max_lvl = niveau maximum des regions voisines d'un noeud du reseau *)
Variable max_lvl : nat.

(* netnode = noeud du reseau. On les numerote avec des entiers. *)
Definition netnode := nat.

(* graph = representation des liens entre les noeuds du reseau. On représente chaque lien
   par une fonction booléenne entre chaque paire de noeuds. *)
Definition graph:= netnode -> netnode -> bool.

(* Le reseau contient des noeuds repartis par region.
   L'appartenance d'un noeud à une region est representé par une fonction booléenne. *)
Definition loc_geo := region -> netnode -> bool.

(* Chaque region contient au moins un noeud *)
Axiom no_empty_region :
  forall (q : region) (l:loc_geo), rank q <= max_lvl -> { x : netnode | l q x = true }.

(* On suppose que chaque node appartient à au moins une région du plan de rang minimum (A1) *)
Axiom no_single_node :
  forall (x:netnode) (l:loc_geo), { q : region | l q x = true /\ rank q = max_lvl }.

(* Les regions sont soit disjointes soit imbriquées *)
Definition no_intersect_region (l:loc_geo) : Prop :=
  forall q1 q2 : region, equal_region q1 q2 = false -> 
  equal_region (shared_region q1 q2) q1 = true \/ (* q2 est inclus dans q1 *)
  equal_region (shared_region q1 q2) q2 = true \/ (* q1 est inclus dans q2 *)
  has_shared_region q1 q2 = false. (* q1 et q2 sont disjoints *)

(* has_path g n x y: Le graphe g a un chemin de longueur n du noeud x vers le noeud y. 
                     La relation has_path est reflexive et transitive. *)
Inductive has_path (g:graph) : nat -> netnode -> netnode -> Prop :=
| HP_Self (x:netnode): has_path g O x x
| HP_Step (n:nat) (x y z:netnode) (ST: g x y = true) (HP: has_path g n y z): has_path g (S n) x z.

(* Region de niveau n contenant le noeud x *)
Definition getAn (l:loc_geo)(x:netnode)(n:nat) : region.
    destruct (no_single_node x l) as [r _].
    exact (region_at_rank r n).
Qed.

Definition test_x : netnode := 10 .






Definition test_loc (r:region) (x:netnode) :  := 
  if x == test_x then
    match r with
    | (OO Z) => true
    | _ => false
    end
  else
    false.

Eval compute in getAn test_loc test_x 1.


(* TODO: Modéliser une route *)
(* TODO: Prouver la propriété: 
         s'il existe un chemin partant d'une source S vers une destination D donnee,
         il existe toujours des valeurs de k et de max_lvl qui permettent de trouver la 
         route menant vers D *)


End network.






(**
Definition netgraph (x y:nat):bool:=
(Nat.eqb y (x+1) || Nat.eqb y (x-1)).



Structure M2 : Type := {c00 : region;  c01 : region;
c10 : region;  c11 : region}.

Definition Id2 : M2 := Build_M2 1 0 0 1.




Definition negb (b:bool) : bool := 
  match b with
  | true => false
  | false => true
  end.

Notation "! x" := (negb x) (at level 50, left associativity) : bool_scope.
**)