(* Util.v

   Copyright Centre national d'études spatiales (CNES), 2023
   see LICENSE file *)

Notation "¬" := negb (at level 40).

Fixpoint list_mem {A} (eqb: A -> A -> bool) (l: list A) (n: A) := match l with
| nil => false
| cons x xs => if eqb n x then true else list_mem eqb xs n
end.

Fixpoint list_nodup {A} (eqb: A -> A -> bool) (l: list A) := match l with
| nil => true
| cons x xs => if list_mem eqb xs x then true else list_nodup eqb xs
end.



(*
Definition list_equiv {A} `{EqDec A} : relation (list A) := list_equiv_decb.

Global Instance string_Setoid : Setoid string := {}.
Global Instance string_EqDec : EqDec string_Setoid := {
  equiv_dec := string_dec;
}.


Global Program Instance list_Setoid {A} `(SA: EqDec A) : Setoid (list A) := { 
  equiv := list_equiv; 
}.
Next Obligation.
constructor.
* intro. apply Bool.andb_true_iff. split.
  + assert (SN: Setoid nat). apply _.
    unfold equiv_dec. unfold nat_eq_eqdec.
    destruct (PeanoNat.Nat.eq_dec (length x) (length x)).
    - reflexivity.
    - unfold not in n.
      assert (Hlen: length x = length x). reflexivity.
      exfalso. now apply n in Hlen.
  + 
    induction x.
    - now cbn.
    - simpl forallb. 
      unfold equiv_dec.
      destruct (SA a a).
      ** cbn.
         unfold forallb.
         unfold forallb in IHx.
         
         unfold list_mem in IHx.
         
         
         ++ 
      
      
   

unfold equiv_dec. unfold nat_eq_eqdec. unfold 
    
    eapply (Reflexive _ (length x)).
    apply Bool.Is_true_eq_true.
    
(*   eapply Equivalence.*)
  + 
 


Global Program Instance list_EqDec {A} `(EA: EqDec A) `(SA: Setoid (list A)) : EqDec SA := {
  equiv_dec := (fun x y => if list_equiv x y then left _ else right _
  );
}.
*)
