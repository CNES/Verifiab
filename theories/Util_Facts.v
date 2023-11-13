(* Util_Facts.v

   Copyright Centre national d'études spatiales (CNES), 2023
   see LICENSE file *)

Require Import 
  SetoidList
  Util.

Theorem mem_iff {A} (eqb: A -> A -> bool) (l: list A) (n: A) : 
  (InA (fun x y => eqb x y = true) n l) <-> (list_mem eqb l n = true).
Proof.
induction l; split; intro h1.
* inversion h1.
* now cbn in h1.
* simpl list_mem.
  destruct (eqb n a) eqn:han.
  + reflexivity.
  + apply IHl. 
    inversion h1.
    - rewrite han in H0. inversion H0.
    - apply H0.
* destruct (eqb n a) eqn:han.
  + now constructor.
  + apply InA_cons_tl.
    simpl list_mem in h1.
    rewrite han in h1.
    now apply IHl in h1.
Qed.
    
