/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Evaluation of homogeneous cochains at cumulative products

Source: Stacks Project, Etale Cohomology, Tag 0DVG, displayed differential;
homogeneous change of variables in the parent comparison proof.
(blueprint: def-sc-homogeneous-cochain-evaluation).
-/

@[expose] public section

universe u s

namespace Rep

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Uncurry an iterated continuous map by evaluating the coordinates in order. -/
def resolutionEval (N : TopRep.{max u s} ℤ G) :
    (n : ℕ) → (TopRep.resolutionX N n).V →+ ((Fin n → G) → N.V)
  | 0 =>
    { toFun := fun x _ ↦ x
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  | n + 1 =>
    { toFun := fun f g ↦ resolutionEval N n (f (g 0)) (Fin.tail g)
      map_zero' := by
        funext g
        exact congrFun (resolutionEval N n).map_zero (Fin.tail g)
      map_add' := by
        intro f h
        funext g
        exact congrFun ((resolutionEval N n).map_add (f (g 0)) (h (g 0))) (Fin.tail g) }

/-- Iterated evaluation is jointly continuous when the group is locally compact. -/
theorem continuous_resolutionEval [LocallyCompactSpace G]
    (N : TopRep.{max u s} ℤ G) (n : ℕ) :
    Continuous (fun p : (TopRep.resolutionX N n).V × (Fin n → G) ↦
      resolutionEval N n p.1 p.2) := by
  induction n with
  | zero => exact continuous_fst
  | succ n ih =>
    change Continuous (fun p : C(G, (TopRep.resolutionX N n).V) × (Fin (n + 1) → G) ↦
      resolutionEval N n (p.1 (p.2 0)) (Fin.tail p.2))
    exact ih.comp
      ((continuous_eval.comp
        (continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd))).prodMk
          (continuous_pi fun i ↦ (continuous_apply i.succ).comp continuous_snd))

/-- Taking successive products is continuous; no commutativity is required. -/
theorem continuous_finPartialProd (n : ℕ) :
    Continuous (Fin.partialProd : (Fin n → G) → (Fin (n + 1) → G)) := by
  apply continuous_pi
  intro i
  induction i using Fin.inductionOn with
  | zero => simpa using (continuous_const : Continuous (fun _ : Fin n → G ↦ (1 : G)))
  | succ i hi =>
    convert hi.mul (continuous_apply i) using 1
    funext g
    exact Fin.partialProd_succ g i

/-- The concrete additive coordinate map: uncurry and evaluate at
`(1,g₀,g₀*g₁,...,g₀*...*gₙ₋₁)`. Continuity of joint evaluation and finite products,
followed by discreteness of the coefficient topology, proves local constancy.

Source: Stacks Project, Etale Cohomology, Tag 0DVG; the homogeneous coordinate
conversion in the parent proof, steps 1 and 2.
(blueprint: def-sc-homogeneous-cochain-evaluation). -/
def homogeneousCochainEvaluation [CompactSpace G] [T2Space G]
    (N : TopRep.{max u s} ℤ G) [DiscreteTopology N.V] (n : ℕ) :
    (TopRep.homogeneousCochains N).X n →+ LocallyConstant (Fin n → G) N.V where
  toFun x :=
    { toFun := fun g ↦ resolutionEval N (n + 1) x.val (Fin.partialProd g)
      isLocallyConstant := (IsLocallyConstant.iff_continuous _).2
        ((continuous_resolutionEval N (n + 1)).comp
          (continuous_const.prodMk (continuous_finPartialProd n))) }
  map_zero' := by
    ext g
    exact congrFun (resolutionEval N (n + 1)).map_zero (Fin.partialProd g)
  map_add' x y := by
    ext g
    exact congrFun ((resolutionEval N (n + 1)).map_add x.val y.val) (Fin.partialProd g)

/-- Uncurrying converts the iterated coinduced action into the diagonal action. -/
theorem resolutionEval_action (N : TopRep.{max u s} ℤ G) (n : ℕ)
    (a : G) (x : (TopRep.resolutionX N n).V) (g : Fin n → G) :
    resolutionEval N n ((TopRep.resolutionX N n).ρ a x) g =
      N.ρ a (resolutionEval N n x (fun i ↦ a⁻¹ * g i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change resolutionEval N n
      ((TopRep.resolutionX N n).ρ a (x (a⁻¹ * g 0))) (Fin.tail g) = _
    exact ih _ _

/-- Invariance of an iterated cochain gives equivariance of its uncurried function. -/
theorem resolutionEval_equivariant (N : TopRep.{max u s} ℤ G) (n : ℕ)
    (x : (TopRep.homogeneousCochains N).X n) (a : G) (g : Fin (n + 1) → G) :
    resolutionEval N (n + 1) x.val (fun i ↦ a * g i) =
      N.ρ a (resolutionEval N (n + 1) x.val g) := by
  have h := resolutionEval_action N (n + 1) a x.val (fun i ↦ a * g i)
  rw [x.property a] at h
  simpa only [inv_mul_cancel_left] using h

end Rep
