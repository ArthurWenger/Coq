Require Import region.
Require Import partition_plan.

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