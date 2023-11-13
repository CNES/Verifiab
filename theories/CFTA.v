(* CFTA.v

   Compiled version of a FTA. 

   Copyright Centre national d'études spatiales (CNES), 2023
   see LICENSE file *)
Require Import 
  SetoidClass
  SetoidDec
  String
  Util
  MSets
  ssrbool.
From Equations Require Import Equations.

Module S := Make Nat_as_OT.
Module SP := WPropertiesOn Nat_as_OT S.
Module SF := WFactsOn Nat_as_OT S.
Module SD := WDecideOn Nat_as_OT S.

Import S SP SF SD.

(* @TODO fix this, we can't import notation for some reason *)
Notation "s  [=]  t" := (Equal s t) (at level 70, no associativity).
Notation "s  [<=]  t" := (Subset s t) (at level 70, no associativity).

(* A compiled fault tree *)
Inductive fta := 
| Fcomp (id: nat)
| Fand (l r : fta)
| For (l r : fta).
Derive NoConfusion for fta.
Derive Subterm for fta.

Infix "∈" := mem (at level 40).

Fixpoint eval (f: fta) (v: t) : bool := match f with
| Fcomp id => id ∈ v
| Fand l r => (eval l v) && (eval r v)
| For l r => (eval l v) || (eval r v)
end.
Infix "↓" := eval (at level 50).

#[global]
Instance eval_compat (f:fta) : Proper (Equal ==> (@Coq.Init.Logic.eq bool)) (eval f).
Proof.
intros s1 s2 h1.
induction f.
* cbn. now rewrite h1.
* cbn.
  rewrite IHf1.
  rewrite IHf2.
  reflexivity.
* cbn. 
  rewrite IHf1.
  rewrite IHf2.
  reflexivity.
Qed.

Notation "l \ x" := (remove x l) (at level 40).

Definition is_mcs (f: fta) (v: t) := (f↓v) && (for_all (fun id => ¬(f↓v\id)) v).

Definition val_eq (v v': t) := equal v v'.

Module Type MCS_Solver.
Parameter foldMCS : forall {A:Type}, (t -> A -> A) -> fta -> A -> A.

(* The fold function is correct & complete: each element is a mcs, and every mcs is an element *)
Parameter foldMCS_correct : 
forall (f: fta) (v: t), (is_mcs f v) <-> list_mem val_eq (foldMCS cons f nil) v.

(* There is no duplicate of mcs *)
Parameter foldMCS_nodup : 
forall (f: fta), list_nodup val_eq (foldMCS cons f nil).

End MCS_Solver.

Local Fixpoint occuring' (s: t) (f: fta) : t := match f with 
| Fcomp id => add id s
| Fand l r | For l r => occuring' (occuring' s r) l
end.

Definition occuring := occuring' (empty).

Local Lemma occuring'_union (s: t) (f : fta) : occuring' s f [=] union s (occuring f).
Proof.
revert s.
induction f; 
intro s; 
cbn; 
try fsetdec;
specialize (IHf1 (occuring' s f2)) as h1;
rewrite h1;
rewrite IHf2;
specialize (IHf1 (occuring f2)) as h2;
rewrite h2;
fsetdec.
Qed.  

Fixpoint occuring_bis (f: fta) : t := match f with
| Fcomp id => singleton id
| Fand l r | For l r => union (occuring_bis l) (occuring_bis r)
end.

Theorem occuring_bis_spec (f: fta) : occuring f [=] occuring_bis f.
Proof.
induction f; cbn;
try fsetdec;
rewrite occuring'_union; 
fsetdec.
Qed.

Theorem never_empty (f: fta) : f↓empty = false.
Proof.
induction f.
* now cbn.
* cbn. rewrite IHf1. rewrite IHf2. now cbn.
* cbn. rewrite IHf1. rewrite IHf2. now cbn.
Qed.
