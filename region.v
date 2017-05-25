Require Import Arith.
Require Import Arith Omega.
Require Import NAxioms NSub NZDiv.

Infix "||" := orb : bool_scope.
Infix "&&" := andb : bool_scope.
Infix "=?" := eqb : bool_scope.
Infix "mod" := Nat.modulo : nat_scope.
Infix "<=?" := Nat.leb : nat_scope.
Infix "<?" := Nat.ltb : nat_scope.
Infix "^" := Nat.pow : nat_scope.
Infix "/" := Nat.div : nat_scope.

Set Implicit Arguments.

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

Fixpoint equal_region (n m : region) : bool :=
    match n, m with
    | Z , Z => true
    | OO n' , OO m' => equal_region n' m'
    | OI n' , OI m' => equal_region n' m'
    | IO n' , IO m' => equal_region n' m'
    | II n' , II m' => equal_region n' m'
    | _, _ => false
    end.

Eval compute in equal_region (II(OI(OO Z))) (OO(II(II Z))).
Eval compute in equal_region (II(OI(OO Z))) (II(OI(OO Z))).

(* Notation "x =? y" := (equal_region x y) : region_scope.
   Open Scope region_scope. *)

Eval compute in equal_region (II(OI(OO Z))) (OO(II(II Z))).
Eval compute in equal_region (II(OI(OO Z))) (II(OI(OO Z))).

Fixpoint concat_region(p:region)(s:region):region := 
  match p with
  | Z => s
  | OO p' => OO(concat_region p' s)
  | OI p' => OI(concat_region p' s)
  | IO p' => IO(concat_region p' s)
  | II p' => II(concat_region p' s)
  end.

Definition reverse (r : region) : region :=
    (fix _reverse (rem res:region): region :=
        match rem with 
        | Z => res
        | OO rem' => _reverse rem' (OO(res))
        | OI rem' => _reverse rem' (OI(res))
        | IO rem' => _reverse rem' (IO(res))
        | II rem' => _reverse rem' (II(res))
        end ) r Z.

(* region en commun <=> relation d'inclusion entre les régions *)
Definition shared_region (n m : region) : region :=   
    (fix _shared_region (n m res: region) : region :=
        match n, m with
        | OO n' , OO m' => _shared_region n' m' (OO(res))
        | OI n' , OI m' => _shared_region n' m' (OI(res))
        | IO n' , IO m' => _shared_region n' m' (IO(res))
        | II n' , II m' => _shared_region n' m' (II(res))
        | _, _  => res
        end ) (reverse n) (reverse m) Z.

Eval compute in shared_region (IO(OI(OO Z))) (II(OI(OO Z))) .

(* regions disjointes *)
Fixpoint has_shared_region (n m : region) : bool :=
    match shared_region n m with
    | Z => false
    | _ => true
    end.

Eval compute in has_shared_region (II(OI(II Z))) (II(OI(OO Z))).
Eval compute in has_shared_region (IO(OI(II Z))) (II(II(II Z))).

(* Niveau d'une region *)
Fixpoint rank (n:region) : nat :=
    match n with
    | Z => 0
    | OO n' | OI n' | IO n' | II n' => 1 + rank n'
    end.

Eval compute in rank (II (OI Z)).

(* permet d'obtenir les regions de niveau n contenant une region r <=> An *)
Definition region_at_rank (r:region) (n:nat) : region :=
    (fix _region_at_rank (r:region) (n:nat) :=
    match n with
    | O => r
    | S n' => match r with
              | Z => Z
              | OO r' | OI r' | IO r' | II r' => _region_at_rank r' n'
              end
    end
    ) r ((rank r) - n).

Eval compute in region_at_rank (OO (II (OI (II (OO Z))))) 0.

(* ### Preuves ### *)
Theorem region_at_rank_0 (r:region): region_at_rank r 0 = Z.
Proof.
    unfold region_at_rank. rewrite Nat.sub_0_r.
    induction r; simpl; try exact IHr. 
    reflexivity.
Qed.

Theorem region_at_rank_idem (r:region): region_at_rank r (rank r) = r.
Proof.
    unfold region_at_rank. rewrite minus_diag.
    destruct r; reflexivity.
Qed. 



  (* ### Inutile ### *)
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

Fixpoint same_rank (n1 n2 : region) : bool :=
    Nat.eqb (rank (n1)) (rank (n2)).

Eval compute in same_rank (II(OI(OO Z))) (OO(II(II Z))).

Fixpoint first_region (r : region) : region := region_at_rank r 1.

Eval compute in first_region (II(OI(OO Z))).

Fixpoint last_region_elem (n : region) : region :=
    match n with 
    | Z => Z
    | OO n' => OO Z
    | OI n' => OI Z
    | IO n' => IO Z
    | II n' => II Z
    end.

Eval compute in last_region_elem (II(OI(OO Z))).