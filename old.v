Require Import region.

(**########################################################################**)

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
Theorem no_empty_region :
  forall (r : region) (l:loc_geo), rank r <= max_lvl -> { x : netnode | l r x = true }.
Admitted.

(* On suppose que chaque node appartient à au moins une région du plan de rang minimum (A1) *)
Theorem no_single_node :
  forall (x:netnode) (l:loc_geo), { r : region | l r x = true /\ rank r = max_lvl }.
Admitted.

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

Inductive route (x:netnode): Prop :=
| rA0 (gw: netnode) (HP: gw)
| rAn : x -> region -> route.









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