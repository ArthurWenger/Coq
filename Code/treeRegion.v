Require Import region.
Require Import Arith.

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
  | Node _ l ml mr r => 1 + Nat.max (Nat.max (height l) (height ml))
                                    (Nat.max (height mr) (height r))
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

Definition init_tree : treeRegion := Leaf (OO Z).

(* si on considere que l'arbe est équilibré (ie les branches ont toute la meme taille)
   alors on peut définir une fonction plus simple que la précedente.  *)
Fixpoint partition (m : t) (n : nat) : t :=
    let h := height m in ( 
    match n with 
        | 0 => m
        | S n' => match m with
                | Leaf q => Node q (partition (Leaf (rotation h q)) n') 
                                   (partition (Leaf (rotation (h+1) q)) n') 
                                   (partition (Leaf (rotation (h+2) q)) n') 
                                   (partition (Leaf (rotation (h+3) q)) n')
                | Node q l ml mr r => Node q (partition l n') 
                                             (partition ml n') 
                                             (partition mr n') 
                                             (partition r n')
                end  
        end ).

Eval compute in partition init_tree 2.


(* Autre méthode qui onctionne quel que soit l'arbre. 
   La fonction auxiliaire permet de compter les iterations avec un parametre supplémentaire *)
Definition partition_bis (m : t) (n : nat) : t :=
    (fix _partition_bis (m:t)(n:nat)(acc:nat):t:=
    match n with 
        | 0 => m
        | S n' => match m with
                | Leaf q => Node q (_partition_bis (Leaf (rotation acc q)) n' (acc+1)) 
                                   (_partition_bis (Leaf (rotation (acc+1) q)) n' (acc+1)) 
                                   (_partition_bis (Leaf (rotation (acc+2) q)) n' (acc+1)) 
                                   (_partition_bis (Leaf (rotation (acc+3) q)) n' (acc+1))
                | Node q l ml mr r => Node q (_partition_bis l n' (acc+1)) 
                                             (_partition_bis ml n' (acc+1)) 
                                             (_partition_bis mr n' (acc+1)) 
                                             (_partition_bis r n' (acc+1))
                end  
        end ) m n 0.

Eval compute in partition_bis init_tree 0.
Eval compute in partition_bis init_tree 1.
Eval compute in partition_bis init_tree 2.

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

Definition is_empty_tree m := 
    match m with 
    | Leaf _ => true 
    | _ => false 
    end.

(* utile pour obtenir le code des regions voisines *)
Definition getCode (m : t) : region :=
    match m with
    | Leaf q | Node q _ _ _ _ => q
    end.

Eval compute in getCode (Leaf (OI Z)).
Eval compute in getCode (Node (II Z) (Leaf (OO Z)) (Leaf (OO Z)) (Leaf (OO Z)) (Leaf (OO Z))).


(* #### Preuves  #### *)
Eval compute in Nat.sqrt 10.

Fixpoint is_square (n:nat): bool :=
let sqrt := Nat.sqrt n in (Nat.eqb (sqrt*sqrt) n ).

Eval compute in is_square 9.

Theorem card_leaf_partition_is_square (m : t) (n : nat):
is_square (cardinal_leaf m) = true -> is_square (cardinal_leaf (partition m n)) = true .
Proof.
    Admitted.

Lemma le_0_0_false : 
O < O -> False. 
Proof. 
intro H.
inversion H.
(* apply leb_correct_conv in H. 
   inversion H. *)
Qed.

Eval compute in height (Leaf (OO Z)).

Theorem height_0_tree (m:t):  
height m = 0 -> exists (q : region), m = Leaf q.
Proof.
    destruct m. 
    exists r. 
    reflexivity.
    intro H.
    inversion H.
Qed.

Theorem height_1_tree (m:t):  
0 < height m -> exists (q : region) (l ml mr r0 : t), m = Node q l ml mr r0.
Proof.
    case_eq m. 
    intros. 
    apply le_0_0_false in H0. 
    exfalso. 
    exact H0.
    simpl.
    intros.
    exists r. exists t. exists t0. exists t1. exists t2.
    reflexivity.  
Qed.

Lemma max_n_m_0 (n m:nat): 
Nat.max n m = 0 -> n = 0 /\ m = 0. 
Proof.
    pose (le_ge_dec n m).
    unfold ge in s.
    case s.

    intro H; assert (H1 := H).
    pose Nat.max_r.
    apply e in H.
    intro H2.
    rewrite H2 in H.
    apply eq_sym in H.
    rewrite H in H1. 
    apply Nat.le_0_r in H1.
    split.
    exact H1.
    exact H.

    intro H; assert (H1 := H).
    pose Nat.max_l.
    apply e in H.
    intro H2.
    rewrite H2 in H.
    apply eq_sym in H.
    rewrite H in H1. 
    apply Nat.le_0_r in H1.
    split.
    exact H.
    exact H1.
Qed.

Theorem height_1_node (m : t) (n : nat):
(height m) = 1 -> exists (q  x0 x1 x2 x3: region), m = Node q (Leaf x0) (Leaf x1) (Leaf x2) (Leaf x3).
Proof.
    destruct m.
    simpl. 
    discriminate.
    intro H. 
    inversion H.
    apply max_n_m_0 in H1.
    inversion_clear H1. 
    apply max_n_m_0 in H0.
    apply max_n_m_0 in H2.
    inversion_clear H0.
    inversion_clear H2.
    apply height_0_tree in H0.
    apply height_0_tree in H1.
    apply height_0_tree in H3.
    apply height_0_tree in H4.
    inversion H0.
    inversion H1.
    inversion H3.
    inversion H4.
    subst.
    exists r. exists x0. exists x1. exists x. exists x2.
    reflexivity.
Qed.

Theorem part_Sn (m : t) (n : nat):
partition m (S n) = partition (partition m n) 1.
Proof.
    Admitted.

Theorem partbis_Sn (m : t) (n : nat):
partition_bis m (S n) = partition_bis (partition_bis m n) 1.
Proof.
    Admitted.

Theorem part_partbis_idem (m : t) (n : nat):
partition m n = partition_bis m n.
Proof.
    induction n. 
    reflexivity.
    rewrite part_Sn.
    rewrite partbis_Sn.
    rewrite IHn.
    destruct (partition_bis m n).
    reflexivity.
    reflexivity.
Qed.

(* Lemma S_trivial (n:nat): 
S n = 1 -> n = O. 
Proof.
    intro H.
    inversion H. 
    reflexivity.
Qed. *)


