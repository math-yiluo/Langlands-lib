/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RepresentationTheory.HomogeneousCochainEvaluation
import Mathlib.Topology.Algebra.MulAction

/-!
# Bijectivity of homogeneous cochain evaluation

Source: Stacks Project, Etale Cohomology, Tag 0DVG; homogeneous change of variables
in the parent comparison proof, steps 1 and 2.
(blueprint: lem-sc-homogeneous-cochain-evaluation-bijective).
-/

@[expose] public section

universe u s

namespace Rep

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private def consMap (n : ℕ) : C(G × (Fin n → G), Fin (n + 1) → G) :=
  ⟨fun p ↦ Fin.cons p.1 p.2, continuous_pi fun i ↦ Fin.cases continuous_fst
    (fun j ↦ (continuous_apply j).comp continuous_snd) i⟩

private def resolutionCurry [CompactSpace G] [T2Space G]
    (N : TopRep.{max u s} ℤ G) :
    (n : ℕ) → C(C(Fin n → G, N.V), (TopRep.resolutionX N n).V)
  | 0 => ⟨fun f ↦ f Fin.elim0, continuous_eval_const _⟩
  | n + 1 =>
    ⟨fun f ↦ (resolutionCurry N n).comp ((f.comp (consMap n)).curry),
      (ContinuousMap.continuous_postcomp _).comp
        (ContinuousMap.continuous_curry.comp (ContinuousMap.continuous_precomp _))⟩

private theorem resolutionEval_curry [CompactSpace G] [T2Space G]
    (N : TopRep.{max u s} ℤ G) (n : ℕ) (f : C(Fin n → G, N.V)) (g : Fin n → G) :
    resolutionEval N n (resolutionCurry N n f) g = f g := by
  induction n with
  | zero => exact congrArg f (Subsingleton.elim _ _)
  | succ n ih =>
    change resolutionEval N n
      (resolutionCurry N n (((f.comp (consMap n)).curry) (g 0))) (Fin.tail g) = f g
    rw [ih]
    change f (Fin.cons (g 0) (Fin.tail g)) = f g
    rw [Fin.cons_self_tail]

private theorem resolutionEval_injective (N : TopRep.{max u s} ℤ G) (n : ℕ) :
    Function.Injective (resolutionEval N n) := by
  induction n with
  | zero =>
    intro x y h
    exact congrFun h Fin.elim0
  | succ n ih =>
    intro x y h
    apply ContinuousMap.ext
    intro a
    apply ih
    funext g
    simpa [resolutionEval] using congrFun h (Fin.cons a g)

/-- Evaluation at cumulative products is bijective.

Source: Stacks Project, Etale Cohomology, Tag 0DVG; homogeneous conversion in the
parent proof, steps 1 and 2.
(blueprint: lem-sc-homogeneous-cochain-evaluation-bijective).

Proof: Uncurry iterated maps on the compact Hausdorff group. Their invariant elements
are precisely equivariant functions. An equivariant function is determined by its values
at (1,g₀,g₀g₁,...), since any tuple h is h₀ times the partial products of the successive
ratios hᵢ⁻¹hᵢ₊₁. This proves injectivity. Given a locally constant c, form the homogeneous
function h ↦ ρ(h₀)c(h₀⁻¹h₁,...,hₙ₋₁⁻¹hₙ). Open stabilizers make the action jointly
continuous on the discrete coefficients. Products and inverses make this function
continuous; compact-open currying produces an iterated map. Its equivariance follows
from cancellation of the common left factor in the successive ratios, and therefore it
is invariant. The successive ratios of partial products recover the original tuple,
so its coordinate map is c. This proves surjectivity, including degree zero. -/
theorem homogeneousCochainEvaluation_bijective [CompactSpace G] [T2Space G]
    (N : TopRep.{max u s} ℤ G) [DiscreteTopology N.V]
    (hN : ∀ x : N.V, IsOpen {g : G | N.ρ g x = x}) (n : ℕ) :
    Function.Bijective (homogeneousCochainEvaluation N n) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply resolutionEval_injective N (n + 1)
    funext g
    let r : Fin n → G := fun i ↦ (g i.castSucc)⁻¹ * g i.succ
    have hd : (fun i ↦ g 0 * Fin.partialProd r i) = g := Fin.partialProd_left_inv g
    have hc := congrArg (fun c : LocallyConstant (Fin n → G) N.V ↦ c r) h
    change resolutionEval N (n + 1) x.val (Fin.partialProd r) =
      resolutionEval N (n + 1) y.val (Fin.partialProd r) at hc
    rw [← hd, resolutionEval_equivariant, resolutionEval_equivariant, hc]
  · intro c
    let : MulAction G N.V :=
      { smul := fun a x ↦ N.ρ a x
        one_smul := by
          intro x
          change N.ρ 1 x = x
          rw [map_one]
          rfl
        mul_smul := by
          intro a b x
          change N.ρ (a * b) x = N.ρ a (N.ρ b x)
          rw [map_mul]
          rfl }
    have : ContinuousSMul G N.V := (continuousSMul_iff_stabilizer_isOpen).2 hN
    let f : C(Fin (n + 1) → G, N.V) :=
      ⟨fun h ↦ N.ρ (h 0) (c (fun i ↦ (h i.castSucc)⁻¹ * h i.succ)),
        continuous_smul.comp ((continuous_apply 0).prodMk
          (c.continuous.comp (continuous_pi fun i ↦
            (continuous_apply i.castSucc).inv.mul (continuous_apply i.succ))))⟩
    let y := resolutionCurry N (n + 1) f
    have hy : ∀ a, (TopRep.resolutionX N (n + 1)).ρ a y = y := by
      intro a
      apply resolutionEval_injective N (n + 1)
      funext h
      rw [resolutionEval_action]
      dsimp only [y]
      rw [resolutionEval_curry, resolutionEval_curry]
      simp [f, mul_inv_rev, mul_assoc, ← mul_apply_eq_comp, ← map_mul]
    refine ⟨⟨y, hy⟩, ?_⟩
    ext g
    change resolutionEval N (n + 1) y (Fin.partialProd g) = c g
    dsimp only [y]
    rw [resolutionEval_curry]
    simp [f, Fin.partialProd_right_inv]

end Rep
