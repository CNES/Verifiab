(* DepCompare.v

   Compiled version of a FTA. 

   Copyright Centre national d'études spatiales (CNES), 2023
   see LICENSE file *)

Require Import
  Nat 
  Compare_dec.

(* Very similar to the deprecated Compare type in OrderedType *)
Inductive Compare (x y : nat) :=
| EQ (h: x = y)
| LT (h: x < y)
| GT (h: x > y).

Definition dep_comp (x y : nat) : Compare x y.
Proof.
destruct (compare x y) eqn:h1.
* apply EQ. now apply nat_compare_eq.
* apply LT. now apply nat_compare_lt.
* apply GT. now apply nat_compare_gt.
Defined.
