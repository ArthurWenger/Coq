Require Import notations.
Require Import option.
Require Import String.

Locate sqrt.
Print Nat.sqrt.

Definition computation1 :=
  (fun f h p => f (f (f h)) p)
    (fun g p => g (g p))
    (fun p => match p with (x, y) => (x+1, (x+1) * y) end)
    (0, 1).
Print computation1.   
Compute computation1.

Definition computation2 :=
(fun g k => g (g k))
(fun p => match p with (x, y) => (x+1, (x+1) * y) end)
    (0, 1).
    Compute computation2.
(fun (g : nat * nat -> nat * nat) (p : nat * nat) => g (g p)) (1, 2).

Definition is_prime (n:nat) :=
  2 <= n /\  forall p q, 0 < p -> 0 < q -> n = p * q -> p = n \/ q = n.

Fixpoint is_prime_bis (n:nat) : bool :=
match n with
| O | 1 => false
| _ => (fix sub (n sqrt_n:nat) : bool :=
       match sqrt_n with
       | O | 1 => true
       | S sq' =>  if Nat.eqb (Nat.modulo n sqrt_n) O then false else sub n sq'
       end) n (Nat.sqrt n)
end.

Eval compute in is_prime_bis 7.

Print Nat.div.

(* dec_fix = sqrt n - cpt // cpt ++ => dec_fix -- *)
Fixpoint sub_prime_factor (n cpt dec_fix:nat) : list nat := 
match dec_fix with
| O => nil
| S d' => match n with
          | O | 1 => nil
          | _ => if Nat.eqb (Nat.modulo n cpt) O then n :: sub_prime_factor (Nat.div n cpt) cpt dec_fix 
                 else sub_prime_factor n (cpt+1) d'
          end
end.

Fixpoint sub_prime_factor (n cpt:nat) : list nat := 
if Arith.Compare_dec.le_lt_dec (cpt * cpt) n then (* cpt² <= n *)
    match n with
    | O | 1 => nil
    | _ => if Nat.eqb (Nat.modulo n cpt) O then n :: sub_prime_factor (Nat.div n cpt) cpt else sub_prime_factor n (cpt+1)
    end
else  nil.
