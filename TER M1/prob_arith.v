Require Import notations.
Require Import option.
Require Import String.

Locate sqrt.
Print Nat.sqrt.

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
