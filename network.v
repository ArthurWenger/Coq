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

Locate "{".
(* Notation "{ x : A  |  P }" := (sig A (fun x => P)) (at level 0, x at level 99). *)

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

Check distance_regions_elem.

Definition is_in_A0 (r1 r2:region)(m: listlist region): bool := 
match distance_regions_elem r1 r2 m with
| None => false
| Some d => d <? k
end.

(* Region de niveau n contenant le noeud x *)
Definition getAn (l:loc_geo)(x:netnode)(n:nat) : region.
    destruct (no_single_node x l) as [r _].
    exact (region_at_rank r n).
Qed.

Inductive route (l:loc_geo)(m: listlist region)(x:netnode): Set :=
(* l'ensemble des noeuds du réseau situés dans A0 par rapport à x *)
| rA0: forall (gw:netnode) (HP: is_in_A0 (getAn l x max_lvl) (getAn l gw max_lvl) m = true), route l m x 
(* l'ensemble des régions voisines de la region élémentaire contenant x *)
| rAn: forall (r:region)(HP: is_in_list (voisins_mat m (getAn l x max_lvl)) r = true), route l m x. 



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