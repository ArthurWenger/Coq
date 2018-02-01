Require Import option.
Require Import region.
Require Import clist.
Require Import listlist.
Require Import partition_plan.

(* ########## Modélisation du réseau (noeud / graphe / chemin / route ...) ###########*)
Section network.
(* k = rayon de A0 en terme de regions elementaires *)
Parameter k : nat.

(* max_lvl = niveau maximum des regions voisines d'un noeud du reseau *)
Parameter max_lvl : nat.

(* netnode = noeud du reseau. On les numerote avec des entiers. *)
Definition netnode := nat.

(* graph = representation des liens entre les noeuds du reseau. On représente chaque lien
   par une fonction booléenne entre chaque paire de noeuds. *)
Definition graph:= netnode -> netnode -> bool.

(* Le reseau contient des noeuds repartis par region.
   L'appartenance d'un noeud à une region est representé par une fonction booléenne. *)
Definition loc_geo := region -> netnode -> bool.

(* Notation "{ x : A  |  P }" := (sig A (fun x => P)) (at level 0, x at level 99). *)

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

Check distance_regions_elem.

Definition region_in_A0 (r1 r2:region)(m: listlist region): bool := 
match distance_regions_elem r1 r2 m with
| None => false
| Some d => d <? k
end.

(* Region de niveau n contenant le noeud x *)
Definition getAn (l:loc_geo)(x:netnode)(n:nat) : region.
    destruct (no_single_node x l) as [r _].
    exact (region_at_rank r n).
Qed.

Definition netnode_in_A0 (x y:netnode)(l:loc_geo)(m: listlist region): bool := 
region_in_A0 (getAn l x max_lvl) (getAn l y max_lvl) m.

Definition min_reg_to_dest (src dest:netnode)(l:loc_geo)(m:listlist region): region :=
match (voisins_mat m (getAn l src max_lvl)) with
| nil => Z
| h::t => (fix sub (d minR:region)(l:clist region)(m:listlist region)(min:nat): region :=
            match l with 
            | nil => minR
            | h::t => if (min <=? option_elim min (distance_regions_elem h d m)) then 
                        sub d minR t m min
                      else 
                        sub d h t m (option_elim min (distance_regions_elem h d m))
            end) (getAn l dest max_lvl) h t m (option_elim 0 (distance_regions_elem h (getAn l dest max_lvl) m))
end.


(* NON TERMINE *)


(*
Inductive route : Type :=
| rA0: netnode -> netnode -> route
| rAn: netnode -> region -> route.

Definition table (x:netnode)(l:loc_geo)(m: listlist region): clist netnode.

Inductive table2 (x:netnode)(l:loc_geo)(m: listlist region): Set :=
(* l'ensemble des noeuds du réseau situés dans A0 par rapport à x *)
| tA0 (gw:netnode)(HP: netnode_in_A0 x gw l m = true): table2 x l m
(* l'ensemble des régions voisines de la region élémentaire contenant x *)
| tAn (r:region)(HP: is_in_list (voisins_mat m (getAn l x max_lvl)) r = true): table2 x l m.

Definition table3 : Type := clist route.
*)

(* Definition rAn: netnode -> region -> netnode . *)

(* Theoreme nécessaire pour determiner si une region contient un noeud ou non *)
Theorem region_can_be_empty(x:netnode)(r:region)(l:loc_geo)(m:listlist region): 
est_voisin (getAn l x max_lvl) r m = true ->
exists (gw:netnode), l r gw = true \/ 
forall (gw:netnode), l r gw = false.
Admitted. (* Litteralement Vrai || Faux *)


(* Definition nexthop (src dest:netnode)(l:loc_geo)(m: listlist region)(g:graph): netnode.
case (netnode_in_A0 src dest l m). exact dest.
else (min_voisins_to_dest src dest l m). *)


(*
Theorem (g:graph)(l:loc_geo)(m:listlist region)(init:region)(x y:netnode): 
m = mat_part_bup max_level init -> (* m correspond au partitionnement du plan *)
exists (d:nat), has_path g d x y -> (* il existe un chemin de longueur d entre x et y *)

Proof.
  
Qed. *)

(*
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
*)

(* TODO: Prouver la propriété:
         Il n'existe pas de boucle réseau. => utiliser les variations de distances vers la destination  *)
(* TODO: Prouver la propriété: 
         s'il existe un chemin partant d'une source S vers une destination D donnee,
         il existe toujours des valeurs de k et de max_lvl qui permettent de trouver la 
         route menant vers D *)


End network.