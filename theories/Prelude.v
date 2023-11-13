(* Prelude.v

   Copyright Centre national d'études spatiales (CNES), 2023
   see LICENSE file *)

Require 
  Coq.FSets.FMapFullAVL
  Coq.Structures.OrderedTypeEx.

Require Import 
  List
  BDDSolver
  CFTA.

Definition basic (x:nat) := Fcomp x.

Equations n_choose_k {A B:Type} (k:nat) (f: A -> list B -> A) (l: list B) (acc: A) : A by struct l :=
n_choose_k O _ _ acc := acc;
n_choose_k (S O) f l acc := fold_left (fun a e => f a (cons e nil)) l acc;
n_choose_k (S (S k')) _ nil acc => acc;
n_choose_k (S (S k')) f (cons x xs) acc =>
  let acc' := n_choose_k (S k') (fun a e => f a (cons x e)) xs acc in
  n_choose_k (S (S k')) f xs acc'.


Definition vote (k: nat) (top: fta) (rest: list fta) : fta := 
  match rest with
  | nil => top
  | _ => 
    let ret :=
        n_choose_k k 
          (fun acc comb => 
            let comb := fold_left Fand (tl comb) (hd top comb) in
            match acc with
            | None => Some comb
            | Some acc => Some (For acc comb)
            end
          )
          (top :: rest)
          None
      in
      match ret with
      | Some x => x
      | None => top
      end
  end.

Fixpoint leftmost (f:fta) := 
  match f with
  | Fand l r | For l r => leftmost l
  | Fcomp x => x
  end.

Local Definition is_mcs' (f: fta) (chosen: list nat) := 
  let v := fold_left (fun a e => S.add e a) chosen S.empty in
  andb (eval f v) (S.for_all (fun e => negb (eval f (S.remove e v))) v).
Local Definition add_if_mcs (f: fta) (chosen: list nat) (acc: list (list nat)) := if is_mcs' f chosen then chosen::acc else acc.

Equations mcs' (f: fta) (k:nat) (l: list nat) (acc: list (list nat)) (chosen: list nat) : list (list nat) by struct l :=
mcs' _ O _ acc chosen := add_if_mcs f chosen acc;
mcs' _ (S O) l acc chosen := fold_left (fun a e => add_if_mcs f (e::chosen) a) l acc;

mcs' _ (S (S k')) nil acc chosen => add_if_mcs f chosen acc;
mcs' _ (S (S k')) (cons x xs) acc _ => 
  let acc :=
    if is_mcs' f (x::chosen) then
      (x::chosen)::acc
    else
      mcs' f (S k') xs acc (x::chosen) 
  in
  mcs' f (S (S k')) xs acc chosen.
    

Definition mcs (k:nat) (f:fta) : list (list nat) := mcs' f k (S.elements (occuring f)) nil nil.

Import 
  Coq.FSets.FMapFullAVL
  Coq.Structures.OrderedTypeEx.

Module M := FMapFullAVL.Make(Nat_as_OT).

Class Ring (T: Type) := mk_prob {
  r0: T; (* additive identity *)
  r1: T; (* multiplicative identity *)
  radd: T -> T -> T;
  rmul: T -> T -> T;
  rsub: T -> T -> T;
}.

Section ZRing.
Import ZArith.

#[global]
Instance Z_ring : Ring Z := {
  r0 := 0;
  r1 := 1;
  radd := Z.add;
  rmul := Z.mul;
  rsub := Z.sub;
}.
End ZRing.

Section QRing.
Import QArith.
#[global]
Instance Q_ring : Ring Q := {
  r0 := 0;
  r1 := 1;
  radd := Qplus;
  rmul := Qmult;
  rsub := Qminus;
}.
End QRing.

Fixpoint bdd_tep {t: Type} {rt: Ring t} (p:M.t t) (b:bdd) : t :=
  match b with
  | Leaf true => r1
  | Leaf false => r0
  | Node x f t => 
      let px := match M.find x p with
      | None => r0
      | Some x => x 
      end in
      radd (rmul px (bdd_tep p t)) (rmul (rsub r1 px) (bdd_tep p f))
  end.
Definition tep {t:Type} {rt: Ring t} (p:M.t t) (f:fta) : t := bdd_tep p (bdd_of_fta f).

Definition add_pair {t:Type} {rt: Ring t} (kv: fta * t) (r: M.t t) : M.t t := M.add (leftmost (fst kv)) (snd kv) r.
Definition mempty {t:Type} {rt: Ring t} := M.empty t.

Notation "{ a }" := (add_pair a mempty).
Notation "{ a , b , .. , z }" := (add_pair a (add_pair b .. (add_pair z mempty) ..)).

Notation "@( k , [ a , b , c , .. , z ])" := (vote k a (cons b (cons c .. (cons z nil) .. ))).

Declare Scope fault_scope.
Delimit Scope fault_scope with F.

Notation "x && y" := (Fand x y) (at level 40, left associativity).
Notation "x || y" := (For x y) (at level 50, left associativity).
