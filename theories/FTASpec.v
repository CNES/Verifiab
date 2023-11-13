(* FTASpec.v

   Copyright Centre national d'études spatiales (CNES), 2023
   see LICENSE file *)

Require Import 
  String
  List
  Util
  ssrbool.

Fixpoint remove {A} (eqb: A -> A -> bool) (l: list A) (n: A) := match l with
| nil => nil
| cons x xs => if eqb x n then remove eqb xs n else x :: (remove eqb xs n)
end.

(* Two list are equivalent if they have the same elements in them, no matter the order *)
Definition list_equiv_decb {A} (eqb: A -> A -> bool) (l1 l2 : list A) := 
  (Nat.eqb (length l1) (length l2)) && (forallb (list_mem eqb l2) l1).

(* End of prelude *)
Notation "x ∈ l" := (list_mem string_dec l x) (at level 40).
Infix "\" := (remove string_dec) (at level 40).

Inductive fta := 
| Fcomp (id: string)
| Fand (l r : fta)
| For (l r : fta)
| Fvote (n: nat) (ts: list fta).

Fixpoint eval_fta (f: fta) (v: list string) := match f with
| Fcomp id => id ∈ v
| Fand l r => (eval_fta l v) && (eval_fta r v)
| For l r => (eval_fta l v) || (eval_fta r v)
| Fvote n ts => 
    Nat.leb n (List.fold_left (fun count f => if eval_fta f v then count+1 else count) ts 0)
end.
Infix "↓" := eval_fta (at level 50).

Definition is_mcs (f: fta) (v: list string) := (f↓v) && (forallb (fun id => ¬(f↓v\id)) v).

(* Equivalence of two valuation (a list of string) *)
Definition val_eq := (list_equiv_decb string_dec).

Module Type MCS_Solver.

Parameter foldMCS : forall {A:Type}, (list string -> A -> A) -> fta -> A -> A.

(* The fold function is correct & complete: each element is a mcs, and every mcs is an element *)
Parameter foldMCS_correct : 
forall (f: fta) (v: list string), (is_mcs f v) <-> list_mem val_eq (foldMCS cons f nil) v.

(* There is no duplicate of mcs *)
Parameter foldMCS_nodup : 
forall (f: fta), list_nodup val_eq (foldMCS cons f nil).

Parameter foldMCS_nodup_within : 
forall (f: fta), Forall (list_nodup string_dec) (foldMCS cons f nil).

End MCS_Solver.

(* A fault tree *)

(*
Inductive occurs_in : fta -> string -> Prop :=
| OIcomp (s: string) : occurs_in (Fcomp s) s
| OIand (s: string) (l r : fta) : (occurs_in l s) \/ (occurs_in r s) -> occurs_in (Fand l r) s
| OIor (s: string) (l r : fta) : (occurs_in l s) \/ (occurs_in r s) -> occurs_in (For l r) s.

Record events : Type := { 
  EV_vars :> list string;
  EV_fta : fta;
  EV_prop : IffA eq EV_vars (occurs_in EV_fta)
}.
*)
