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
