(* BDDSolver.v

   Copyright Centre national d'études spatiales (CNES), 2023
   see LICENSE file *)

Require Import 
  Bool
  CFTA
  Util
  MSets
  Nat
  DepCompare
  Lia
  ssrbool.

From Equations Require Import Equations.
(*
let rec binop op ord l r = 
  match (l, r) with
  | Leaf b, o | o, Leaf b -> op b o
  | Node (ls, lL, lH), Node (rs, rL, rH) -> 
    if ord ls rs then
      make_valid_node ls (binop op ord lL r) (binop op ord lH r)
    else if ord rs ls then
      make_valid_node rs (binop op ord rL l) (binop op ord rH l)    
    else
      make_valid_node ls (binop op ord lL rL) (binop op ord lH rH)

let bor = binop (fun b o -> if b then Leaf true else o)
let band = binop (fun b o -> if b then o else Leaf false)
*)
Inductive bdd :=
| Leaf (b: bool)
| Node (x: nat) (f t: bdd).
Derive NoConfusion EqDec Subterm for bdd.
Infix "b==" := bdd_eqdec (at level 20).

Equations max_bdd (b:bdd) : nat :=
max_bdd (Leaf _) => 0;
max_bdd (Node x f t) => x.

Inductive valid : bdd -> Prop :=
| vLeaf (b: bool) : valid (Leaf b)
| vNode (x: nat) (f t:bdd) 
    (hxf: max_bdd f < x) (hxt: max_bdd t < x) 
    (hf: valid f) (ht: valid t)    
  : valid (Node x f t).

Definition fop := bool -> bdd -> bdd. (* Final OPerator *) 
Equations binop (op: fop) (l r: bdd) : bdd by wf (l, r) (lexprod _ _ bdd_subterm bdd_subterm) :=
binop op (Node lx lf lt) (Node rx rf rt) with compare lx rx => {
| Eq := Node lx (binop op lf rf) (binop op lt rt)
| Lt := Node rx (binop op (Node lx lf lt) rf) (binop op (Node lx lf lt) rt) 
| Gt := Node lx (binop op lf (Node rx rf rt)) (binop op lt (Node rx rf rt))
};
binop op (Leaf b1) (Leaf b2) => op b1 (Leaf b2); (* Equation bug workaround *) 
binop op o (Leaf b) => op b o;
binop op (Leaf b) o => op b o.

Definition stable (op: fop) := forall b z, (exists b', op b z = (Leaf b')) \/ (op b z = z).

Theorem op_valid {op: fop} (hop: stable op) (b: bool) {z: bdd} (hz: valid z) : valid (op b z).
Proof.
specialize (hop b z).
destruct hop as [hop|hop].
* destruct hop as [b' hop].
  rewrite hop. constructor.
* now rewrite hop. 
Qed.

Theorem op_max {op: fop} (hop: stable op) (b: bool) {z n} (hz: max_bdd z = n) : max_bdd (op b z) <= n.
Proof.
specialize (hop b z).
destruct hop as [hop|hop].
* destruct hop as [b' hop].
  rewrite hop. cbn. apply le_0_n.
* rewrite hop. rewrite hz. reflexivity.
Qed.

(* Try to automatically solve a lexical product by trying every possible combination *)
Ltac autolex'' := try (apply bdd_direct_subterm_1_1); apply bdd_direct_subterm_1_2.
Ltac autolex' := try (apply t_step; autolex''); apply t_trans; autolex''.
Ltac autolex := try (apply left_lex; autolex'); apply right_lex; autolex'.

Ltac rec H := lapply H; [clear H; intro H | autolex].

Import Nat_as_OT.

Equations? 
  binop_valid op (hop: stable op) l r (hl:valid l) (hr:valid r) 
: 
  valid (binop op l r) /\ (max_bdd (binop op l r) <= (max (max_bdd l) (max_bdd r)))
        
by wf (l, r) (lexprod _ _ bdd_subterm bdd_subterm) :=
binop_valid op _ (Node lx lf lt) (Node rx rf rt) _ _ with dep_comp lx rx => {
| EQ heq := _
| LT hlt := _
| GT hgt := _
};
binop_valid op _ (Leaf b1) (Leaf b2) _ _  => _; (* Equation bug workaround *)
binop_valid op _ o (Leaf b) _ _  => _;
binop_valid op _ (Leaf b) o _ _  => _.
Proof.
* simp binop.
  split.
  + apply op_valid. assumption. constructor.
  + apply op_max. assumption. now cbn.
* simp binop.
  split.
  + apply op_valid. assumption. assumption.
  + apply op_max. assumption. now cbn.

* simp binop.
  split.
  + apply op_valid. assumption. assumption.
  + apply op_max. assumption. cbn. now rewrite max_0_r.

* simp binop.
  unfold binop_unfold_clause_1.
  rewrite compare_refl.
  
  inversion hl.
  subst x f t0.
  rename lt0 into lt.

  inversion hr.
  subst x f t0.

  specialize (binop_valid op hop).  
  specialize (binop_valid lf rf hf hf0) as h1. rec h1. destruct h1 as [h1 h2].
  specialize (binop_valid lt rt ht ht0) as h3. rec h3. destruct h3 as [h3 h4].
  simp max_bdd.
  split.
  + constructor; try assumption; lia.
  + now rewrite max_id. 
* simp binop.
  unfold binop_unfold_clause_1.
  apply compare_lt_iff in hlt as hlt'.
  rewrite hlt'.
  
  inversion hl.
  subst x f t0.
  rename lt0 into lt.

  inversion hr.
  subst x f t0.

  specialize (binop_valid op hop).  
  specialize (binop_valid (Node lx lf lt) rf hl hf0) as h1. rec h1. destruct h1 as [h1 h2].
  specialize (binop_valid (Node lx lf lt) rt hl ht0) as h3. rec h3. destruct h3 as [h3 h4].
  simp max_bdd in *.
  split.
  + constructor; try assumption; lia.
  + rewrite max_r; [easy|lia].
* simp binop.
  unfold binop_unfold_clause_1.
  apply compare_gt_iff in hgt as hgt'.
  rewrite hgt'.
  inversion hl.
  subst x f t0.
  rename lt0 into lt.
  inversion hr.
  subst x f t0.
  specialize (binop_valid op hop).  
  specialize (binop_valid lf (Node rx rf rt) hf hr) as h1. rec h1. destruct h1 as [h1 h2].
  specialize (binop_valid lt (Node rx rf rt) ht hr) as h3. rec h3. destruct h3 as [h3 h4].
  simp max_bdd in *.
  split.
  + constructor; try assumption; lia.
  + now rewrite max_l; [|lia].
Qed.

Definition op_or (b: bool) (o: bdd) := if b then Leaf true else o.
Theorem stable_op_or : stable op_or.
Proof.
unfold op_or.
intros b z.
destruct b.
* left. now exists true.
* now right.
Qed.

Definition bor := binop op_or.

Definition op_and (b: bool) (o: bdd) := if b then o else Leaf false.
Theorem stable_op_and : stable op_and.
Proof.
unfold op_and.
intros b z.
destruct b.
* now right.
* left. now exists false.
Qed.

Definition band := binop op_and.

Equations bdd_of_fta (f: fta) : bdd :=
bdd_of_fta (Fcomp id) => (Node id (Leaf false) (Leaf true));
bdd_of_fta (Fand l r) => band (bdd_of_fta l) (bdd_of_fta r);
bdd_of_fta (For l r) => bor (bdd_of_fta l) (bdd_of_fta r).

Definition mknode (x: nat) (l r: bdd) : bdd :=
  if l b== (Leaf true) && r b== (Leaf true) then
    Leaf true
  else if l b== (Leaf false) && r b== (Leaf false) then
    Leaf false
  else
    Node x l r.

Lemma mknode_disjunction (x: nat) (l r : bdd) : 
(exists b, ((mknode x l r) = Leaf b) /\ bdd_subterm (Leaf b) (Node x l r)) \/ 
(mknode x l r = Node x l r).
Proof.
unfold mknode.
destruct (l b== (Leaf true)).
* destruct (r b== Leaf true). 
  + left. exists true.
    split; [reflexivity|].
    subst l.
    repeat constructor.
  + subst l. cbn. now right.
* destruct (l b== Leaf false). 
  + destruct (r b== Leaf false).
    - subst l r. cbn.
      left. exists false.
      split; [reflexivity|].
      repeat constructor.
    - subst l. cbn. now right.
  + cbn. now right.
Defined.
 
Fixpoint bnot (z: bdd) := match z with
| Leaf b => Leaf (¬b)
| Node x f t => Node x (bnot f) (bnot t)
end.

Equations without (l r: bdd) : bdd by wf (l, r) (lexprod _ _ bdd_subterm bdd_subterm) :=
without (Leaf false) o => Leaf false;
without o (Leaf true) => Leaf false;
without (Leaf true) o => bnot o; (* possible problem  *)
without o (Leaf false) => o;
without (Node lx lf lt) (Node rx rf rt) with compare lx rx => {
| Eq := mknode lx (without lf rf) (without lt rt)
| Lt := without (Node lx lf lt) rf
| Gt := mknode lx (without lf (Node rx rf rt)) lt 
}.


Lemma mknode_stable (x: nat) (f t: bdd) : max_bdd (mknode x f t) <= max_bdd (Node x f t).
Proof.
unfold mknode.
destruct (f b== (Leaf true)).
* destruct (t b== Leaf true). 
  + cbn. simp max_bdd. lia. 
  + subst f. cbn. lia.
* destruct (f b== Leaf false). 
  + destruct (t b== Leaf false).
    - subst f t. cbn. simp max_bdd. lia.
    - subst f. cbn. simp max_bdd. lia.
  + cbn. lia.
Defined.

Fixpoint minimize (z:bdd) : bdd := match z with 
| Leaf b => Leaf b
| Node x f t => Node x (minimize f) (without (minimize t) (minimize f))
end.
Compute (minimize (bdd_of_fta (For (Fand (Fcomp 1) (Fcomp 2)) (Fcomp 3)))).

Import S SP SF SD CFTA.
Inductive InZ (s: t) : bdd -> Prop :=
| iznil (hs: Empty s) : InZ s (Leaf true)
| iztrue 
    (x: nat) (hsx: In x s)
    (f t: bdd) (ht: InZ (remove x s) t)
  : 
    InZ s (Node x f t)
| izfalse 
    (x: nat) (hsx: ~In x s)
    (f t: bdd) (ht: InZ s f)
  :
    InZ s (Node x f t).

Fixpoint eval_bdd (z: bdd) (s:t) : bool := 
  match z with
  | Leaf b => b
  | Node x f t => if mem x s then eval_bdd t s else eval_bdd f s
  end.

(*
Definition var (x: nat) := Node x (Leaf false) (Leaf true).

Definition va := var 0.
Definition vb := var 1.
Definition vc := var 2.
Definition vd := var 3.

Definition v1 := bor va vb.
Definition v2 := bor vc vd.

Definition v3 := bor va vc.
Definition v4 := bor vb vd.

Definition v5 := band v1 v2.
Definition v6 := band v3 v4.

Compute (band v5 v6).
Compute (minimize (band v5 v6)).

Compute (minimize (band v5 v6)).

Definition test := Node 3 (Node 2 (Leaf false) (Node 1 (Leaf false) (Leaf true)))
         (Node 2 (Node 1 (Node 0 (Leaf false) (Leaf true)) (Node 0 (Leaf false) (Leaf true)))
            (Node 1 (Node 0 (Leaf false) (Leaf true)) (Leaf true))).
Compute test.
Definition test_t := S.add 3 (S.singleton 0).
         
    
Compute (minimize (band v5 v6)).
*)


#[local]
Instance bdd_compat (z:bdd) : Proper (Equal ==> (@Coq.Init.Logic.eq bool)) (eval_bdd z).
Proof.
intros s1 s2 h1.
induction z.
* now cbn.
* cbn.
  destruct (x ∈ s1) eqn:h2.
  + assert (h3: x ∈ s2). now rewrite <- h1.
    now rewrite h3.
  + assert (h3: x ∈ s2 = false). now rewrite <- h1.
    now rewrite h3.
Qed.

Definition monotone (z:bdd) := forall (s:t) (x:nat), eval_bdd z (s\x) -> eval_bdd z s.
Definition comonotone (z:bdd) := forall (s:t) (x:nat), eval_bdd z s -> eval_bdd z (add x s).
Definition contramono (z:bdd) := forall (s:t) (x:nat), eval_bdd z (add x s) = false -> eval_bdd z s = false.
(*
Theorem mono_all (z:bdd) : monotone z.
Proof.
induction z; intros s x' h.
* destruct b.
  + now cbn.
  + now cbn in h.
* destruct (x =? x') eqn:h1.
  + rewrite eqb_eq in h1. subst x'.
    destruct (In_dec x s) as [h2|h2].
    - simpl eval_bdd in *.
      apply mem_iff in h2.
      rewrite h2.
      assert (h3: ~In x (s\x)). fsetdec.
      apply not_mem_iff in h3.
      rewrite h3 in h.
      specialize (IHz1 s x h).
      rewrite IHz1. apply orb_true_r.
    - apply remove_equal in h2.
      now rewrite h2 in h.
  + rewrite eqb_neq in h1.
    destruct (In_dec x s) as [h2|h2].
    - simpl eval_bdd in *.
      assert (h3:In x (s\x')). fsetdec.
      apply mem_spec in h2.
      apply mem_spec in h3.
      rewrite h2.
      rewrite h3 in h.
      apply orb_true_iff in h.
      destruct h as [h4|h4].
      ** specialize (IHz2 s x' h4).
         now rewrite IHz2.
      ** specialize (IHz1 s x' h4).
         rewrite IHz1. apply orb_true_r.
    - simpl eval_bdd in *.
      assert (h3:~In x (s\x')). fsetdec.
      apply not_mem_iff in h3.
      apply not_mem_iff in h2.
      rewrite h2.
      rewrite h3 in h.
      exact (IHz1 s x' h).
Qed.
*)      
Theorem comono_iff (z:bdd) : monotone z <-> comonotone z.
Proof.
split.
* intros hm s x h.
  specialize (hm (add x s) x).
  destruct (In_dec x s) as [h2|h2].
  + apply add_equal in h2.
    now rewrite h2.
  + apply remove_add in h2.
    rewrite h2 in hm.
    now apply hm.
* intros hcm s x h.
  specialize (hcm (s\x) x).
  destruct (In_dec x s) as [h2|h2].
  + apply add_remove in h2.
    rewrite h2 in hcm.
    now apply hcm.
  + apply remove_equal in h2.
    rewrite h2 in h.
    apply h.
Qed.

Theorem contramo_iff (z:bdd) : monotone z <-> contramono z.
Proof.
split.
* intros hm s x h.
  destruct (eval_bdd z s) eqn:h1; [|easy].
  apply comono_iff in hm.
  specialize (hm s x h1).
  now rewrite h in hm.
* intros hm s x h.
  unfold contramono in hm.
  destruct (eval_bdd z s) eqn:h1; [easy|].
  specialize (hm (s\x) x).
  destruct (In_dec x s) as [h2|h2].
  + apply add_remove in h2.
    rewrite h2 in hm.
    specialize (hm h1).
    now rewrite hm in h.
  + apply remove_equal in h2.
    rewrite h2 in h.
    now rewrite h1 in h.
Qed.
  
Lemma insensibility_add
  (z:bdd) (h1: valid z) (n:nat)  (h2: max_bdd z < n) (s: t) 
: eval_bdd z s = eval_bdd z (add n s).
Proof.
revert n h2.
induction z.
* now cbn.
* inversion h1. subst x0 t0 f.
  specialize (IHz1 hf).
  specialize (IHz2 ht).
  intros n hn.
  simp max_bdd in hn.
  simpl.
  destruct (x ∈ s) eqn:h2.
  + apply mem_spec in h2.
    assert (h3: In x (add n s)). fsetdec.
    apply mem_spec in h3. rewrite h3.
    now rewrite (IHz2 n); [|lia].
  + assert (n <> x). lia.
    apply not_mem_iff in h2.
    assert (h3: ~In x (add n s)). fsetdec.
    apply not_mem_iff in h3. rewrite h3.
    apply IHz1. lia.
Qed.

Lemma insensibility_remove
  (z:bdd) (h1: valid z) (n:nat) (h2: max_bdd z < n) (s: t) 
: eval_bdd z s = eval_bdd z (s\n).
Proof.
revert n h2.
induction z.
* now cbn.
* inversion h1. subst x0 t0 f.
  specialize (IHz1 hf).
  specialize (IHz2 ht).
  intros n hn.
  simp max_bdd in hn.
  simpl.
  destruct (x ∈ s) eqn:h2.
  + apply mem_spec in h2.
    assert (n <> x). lia.
    assert (h3: In x (s\n)). fsetdec.
    apply mem_spec in h3. rewrite h3.
    now rewrite (IHz2 n); [|lia].
  + apply not_mem_iff in h2.
    assert (h3: ~In x (s\n)). fsetdec.
    apply not_mem_iff in h3. rewrite h3.
    apply IHz1. lia.
Qed.

Equations? 
  band_correct l r (hl:valid l) (hr:valid r) (s: t)
: 
  (eval_bdd l s) && (eval_bdd r s) = (eval_bdd (band l r) s) 
        
by wf (l, r) (lexprod _ _ bdd_subterm bdd_subterm) :=
band_correct (Node lx lf lt) (Node rx rf rt) _ _ _ with dep_comp lx rx => {
| EQ heq := _
| LT hlt := _
| GT hgt := _
};
band_correct (Leaf b1) (Leaf b2) _ _ _ => _; (* Equation bug workaround *)
band_correct o (Leaf b) _ _ _ => _;
band_correct (Leaf b) o _ _ _ => _.
Proof.
* destruct b1; 
  destruct b2;
  unfold band;
  simp binop;
  now cbn.
* destruct b.
  + rewrite andb_true_l.
    now cbn.
  + unfold band. simp binop.
    now cbn.
* destruct b; 
  unfold band; 
  simp binop; 
  cbn; 
  [ now rewrite andb_true_r | now rewrite andb_false_r ].
* rename lt0 into lt.
  inversion hl. subst x f t0.
  inversion hr. subst x f t0.
  unfold band.
  simp binop.
  unfold binop_unfold_clause_1.
  rewrite compare_refl.
  fold band.
  specialize (band_correct lf rf hf hf0 s) as h1. rec h1.
  specialize (band_correct lt rt ht ht0 s) as h3. rec h3.
  simpl eval_bdd.
  destruct (rx ∈ s) eqn:h11.
  + now rewrite h3.
  + now rewrite h1.
* rename lt0 into lt.
  inversion hl. subst x f t0.
  inversion hr. subst x f t0.
  unfold band.
  simp binop.
  unfold binop_unfold_clause_1.
  apply compare_lt_iff in hlt as hlt'.
  rewrite hlt'.
  fold band.
  specialize (band_correct (Node lx lf lt) rf hl hf0 s) as h1. rec h1.
  specialize (band_correct (Node lx lf lt) rt hl ht0 s) as h3. rec h3.
  simpl eval_bdd.
  rewrite <- h3.
  rewrite <- h1.
  simpl eval_bdd.
  destruct (rx ∈ s) eqn:h11; reflexivity.
* rename lt0 into lt.
  inversion hl. subst x f t0.
  inversion hr. subst x f t0.
  unfold band.
  simp binop.
  unfold binop_unfold_clause_1.
  apply compare_gt_iff in hgt as hgt'.
  rewrite hgt'.
  fold band.
  specialize (band_correct lf (Node rx rf rt) hf hr s) as h3. rec h3.
  specialize (band_correct lt (Node rx rf rt) ht hr s) as h1. rec h1.
  simpl eval_bdd.
  rewrite <- h3.
  rewrite <- h1.
  simpl eval_bdd.
  destruct (lx ∈ s) eqn:h11; reflexivity.
Qed.

Equations? 
  bor_correct l r (hl:valid l) (hr:valid r) (s: t)
: 
  (eval_bdd l s) || (eval_bdd r s) = (eval_bdd (bor l r) s) 
        
by wf (l, r) (lexprod _ _ bdd_subterm bdd_subterm) :=
bor_correct (Node lx lf lt) (Node rx rf rt) _ _ _ with dep_comp lx rx => {
| EQ heq := _
| LT hlt := _
| GT hgt := _
};
bor_correct (Leaf b1) (Leaf b2) _ _ _ => _; (* Equation bug workaround *)
bor_correct o (Leaf b) _ _ _ => _;
bor_correct (Leaf b) o _ _ _ => _.
Proof.
* destruct b1; 
  destruct b2;
  unfold band;
  simp binop;
  now cbn.
* destruct b; easy.
* destruct b.
  + apply orb_true_r.
  + apply orb_false_r. 
* rename lt0 into lt.
  inversion hl. subst x f t0.
  inversion hr. subst x f t0.
  unfold bor. simp binop.
  unfold binop_unfold_clause_1.
  rewrite compare_refl.
  fold bor.
  specialize (bor_correct lf rf hf hf0 s) as h1. rec h1.
  specialize (bor_correct lt rt ht ht0 s) as h3. rec h3.
  simpl eval_bdd.
  destruct (rx ∈ s) eqn:h11.
  + now rewrite h3.
  + now rewrite h1.
* rename lt0 into lt.
  inversion hl. subst x f t0.
  inversion hr. subst x f t0.
  unfold bor. simp binop.
  unfold binop_unfold_clause_1.
  apply compare_lt_iff in hlt as hlt'.
  rewrite hlt'.
  fold bor.
  specialize (bor_correct (Node lx lf lt) rf hl hf0 s) as h1. rec h1.
  specialize (bor_correct (Node lx lf lt) rt hl ht0 s) as h3. rec h3.
  simpl eval_bdd.
  rewrite <- h3.
  rewrite <- h1.
  simpl eval_bdd.
  destruct (rx ∈ s) eqn:h11; reflexivity.
* rename lt0 into lt.
  inversion hl. subst x f t0.
  inversion hr. subst x f t0.
  unfold bor.
  simp binop.
  unfold binop_unfold_clause_1.
  apply compare_gt_iff in hgt as hgt'.
  rewrite hgt'.
  fold bor.
  specialize (bor_correct lf (Node rx rf rt) hf hr s) as h3. rec h3.
  specialize (bor_correct lt (Node rx rf rt) ht hr s) as h1. rec h1.
  simpl eval_bdd.
  rewrite <- h3.
  rewrite <- h1.
  simpl eval_bdd.
  destruct (lx ∈ s) eqn:h11; reflexivity.
Qed.

Theorem bnot_stable (z: bdd) : max_bdd z = max_bdd (bnot z).
Proof.
destruct z; now simp max_bdd.
Qed.

Theorem bnot_valid (z: bdd) (h: valid z) : valid (bnot z).
Proof.
induction z.
* cbn. constructor.
* cbn. 
  inversion h. subst x0 f t0.
  specialize (IHz1 hf).
  specialize (IHz2 ht).
  rewrite (bnot_stable z1) in hxf.
  rewrite (bnot_stable z2) in hxt.
  constructor; assumption.
Qed.

Theorem bnot_correct (z: bdd) (s: t) : ¬(eval_bdd z s) = (eval_bdd (bnot z) s).
Proof.
induction z.
* now cbn.
* cbn.
  destruct (x ∈ s).
  + now rewrite IHz2.
  + now rewrite IHz1.
Qed.


Inductive nzfta : fta -> Prop :=
| nzComp (n: nat) : nzfta (Fcomp (S n))
| nband (l r : fta) : nzfta l -> nzfta r -> nzfta (Fand l r)
| nbor (l r : fta) : nzfta l -> nzfta r -> nzfta (For l r).

Theorem bdd_valid (f: fta) (hf: nzfta f) : valid (bdd_of_fta f).
Proof.
induction f.
* simp bdd_of_fta.
  constructor.
  + inversion hf. subst id.
    simp max_bdd.
    apply lt_0_succ.
  + inversion hf. subst id.
    simp max_bdd.
    apply lt_0_succ.
  + constructor.
  + constructor.
* inversion hf. subst l r.
  apply IHf1 in H1.
  apply IHf2 in H2.
  simp bdd_of_fta.
  unfold band.
  apply binop_valid.
  + exact stable_op_and.
  + assumption.
  + assumption.
* inversion hf. subst l r.
  apply IHf1 in H1.
  apply IHf2 in H2.
  simp bdd_of_fta.
  unfold band.
  apply binop_valid.
  + exact stable_op_or.
  + assumption.
  + assumption.
Qed.

Theorem bdd_correct (f: fta) (hf: nzfta f) (v:t) : f↓v = eval_bdd (bdd_of_fta f) v.
Proof.
induction f.
* simp bdd_of_fta. cbn. now destruct (mem id v).
* simp bdd_of_fta. cbn. 
  inversion hf. subst l r.
  rewrite <- band_correct.
  + rewrite <- IHf1; [|assumption].
    now rewrite <- IHf2; [|assumption].
  + apply bdd_valid. assumption.
  + apply bdd_valid. assumption.
* simp bdd_of_fta. cbn. 
  inversion hf. subst l r.
  rewrite <- bor_correct.
  + rewrite <- IHf1; [|assumption].
    now rewrite <- IHf2; [|assumption].
  + apply bdd_valid. assumption.
  + apply bdd_valid. assumption.
Qed.    

Lemma mknode_correct (x: nat) (l r: bdd) (v:t) : eval_bdd (mknode x l r) v = eval_bdd (Node x l r) v.
Proof.
unfold mknode.
destruct (l b== (Leaf true)).
* destruct (r b== Leaf true). 
  + subst l r. cbn. destruct (x ∈ v); easy.
  + subst l. now cbn.
* destruct (l b== Leaf false). 
  + destruct (r b== Leaf false).
    - subst l r. cbn. destruct (x ∈ v); easy.
    - subst l. now cbn.
  + now cbn.
Qed.

Lemma mknode_valid (x: nat) (l r: bdd) (h: valid (Node x l r)): valid (mknode x l r).
Proof.
inversion h. subst x0 f t0.
unfold mknode.
destruct (l b== (Leaf true)).
* destruct (r b== Leaf true). 
  + subst l r. cbn. constructor. 
  + subst l. cbn. constructor; assumption.
* destruct (l b== Leaf false). 
  + destruct (r b== Leaf false).
    - subst l r. cbn. constructor. 
    - subst l. now cbn.
  + now cbn.
Qed.

Equations? without_valid (l r: bdd) (hl: valid l) (hr: valid r) 
: 
  valid (without l r) /\
  (max_bdd (without l r) <= max (max_bdd l) (max_bdd r))
by wf (l, r) (lexprod _ _ bdd_subterm bdd_subterm) :=
without_valid (Leaf false) o _ _ => _;
without_valid o (Leaf true) _ _ => _;
without_valid (Leaf true) o _ _ => _; (* possible problem  *)
without_valid o (Leaf false) _ _ => _;

without_valid (Node lx lf lt) (Node rx rf rt) _ _ with dep_comp lx rx => {
| EQ heq := _
| LT hlt := _
| GT hgt := _
}.
Proof.
* simp without. split.
  + constructor.
  + now simp max_bdd. 
* simp without. split.
  + now apply bnot_valid.
  + rewrite <- bnot_stable. 
    now simp max_bdd.
* simp without. split.
  + constructor.
  + simp max_bdd. lia.
* simp without. split.
  + constructor.
  + simp max_bdd. lia.
* simp without. split.
  + assumption.
  + simp max_bdd. lia.
* inversion hl. subst x f t0.
  inversion hr. subst x f t0.
  simp without. 
  unfold without_unfold_clause_5.
  rewrite compare_refl.
  specialize (without_valid lf rf hf hf0) as h1. rec h1. destruct h1 as [h1 h2].
  specialize (without_valid lt0 rt ht ht0) as h3. rec h3. destruct h3 as [h3 h4].
  split.
  + apply mknode_valid.
    constructor; try assumption; lia.
  + specialize (mknode_stable rx (without lf rf) (without lt0 rt)) as h5.
    assert (max_bdd (Node rx (without lf rf) (without lt0 rt)) <= max (max_bdd (Node rx lf lt0)) (max_bdd (Node rx rf rt))); [|lia].
    simp max_bdd. lia.
* inversion hl. subst x f t0.
  inversion hr. subst x f t0.
  simp without. 
  unfold without_unfold_clause_5.
  apply compare_lt_iff in hlt as hlt'.
  rewrite hlt'.
  specialize (without_valid (Node lx lf lt0) rf hl hf0) as h1. rec h1. destruct h1 as [h1 h2].
  split.
  + assumption.
  + simp max_bdd in *.
    lia.
* inversion hl. subst x f t0.
  inversion hr. subst x f t0.
  simp without. 
  unfold without_unfold_clause_5.
  apply compare_gt_iff in hgt as hgt'.
  rewrite hgt'.
  specialize (without_valid lf (Node rx rf rt) hf hr) as h1. rec h1. destruct h1 as [h1 h2].
  split.
  + apply mknode_valid. simp max_bdd in *.
    constructor; try assumption. lia.
  + specialize (mknode_stable lx (without lf (Node rx rf rt)) lt0) as h3.
    simp max_bdd in *.
    lia.
Qed.

Fixpoint strict_eval (z: bdd) (v:t) := match z with
| Leaf b => b && is_empty v
| Node x f t => if x ∈ v then strict_eval t (remove x v) else strict_eval f v
end.

Infix "⇊" := (strict_eval) (at level 30).

Theorem strict_to_eval (z: bdd) (hz: valid z) (v:t) (h: strict_eval z v) : eval_bdd z v.
Proof.
revert v h hz.
induction z; intros v h hz.
* simpl in *.
  now apply andb_true_iff in h. 
* inversion hz. subst x0 f t0.
  simpl in *.
  destruct (x ∈ v) eqn:h2.
  + specialize (IHz2 (v\x) h ht).
    specialize (insensibility_remove z2 ht x hxt v) as h3.
    now rewrite h3.
  + exact (IHz1 v h hf).
Qed.

Definition zmcs (z:bdd) (v:t) := (eval_bdd z v) && (for_all (fun id => ¬(eval_bdd z (v\id))) v).

Fixpoint zoccuring (z: bdd) : t := match z with
| Leaf _ => empty
| Node x f t => add x (union (zoccuring f) (zoccuring t))
end.
