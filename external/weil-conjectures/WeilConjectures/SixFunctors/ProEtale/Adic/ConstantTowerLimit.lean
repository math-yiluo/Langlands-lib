/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegersSheafLowerStar

/-!
# Limits of towers of constant pro-étale sheaves

For a tower `⋯ ⟶ Q₁ ⟶ Q₀` of finite (discrete) commutative rings, the limit of the comparison
pullbacks `ν^* Qₙ` of the constant étale sheaves is the sheaf `C(-, lim Qₙ)` of continuous maps
to the profinite ring `lim Qₙ`
(`AlgebraicGeometry.ProEtale.isLimitComparisonUpperStarConstantSheafTower`). This generalises
`AlgebraicGeometry.ProEtale.isLimitPadicIntegersSheafCone` (`Qₙ = 𝒪_E ⧸ ℓⁿ`), and is the
constant case of the description of `lim ν^* Lₙ` for a tower of finite locally constant
sheaves.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Topology

namespace AlgebraicGeometry.ProEtale

variable {Qs : ℕ → Type} [∀ n, TopologicalSpace (Qs n)] [∀ n, CommRing (Qs n)]
  (τ : ∀ n, Qs (n + 1) →+* Qs n)

/-- The limit `lim Qₙ` of a tower of topological rings, as the subring of compatible families
of `∏ Qₙ`, with the subspace topology. -/
def towerLimitRing : Subring (∀ n, Qs n) where
  carrier := {x | ∀ n, τ n (x (n + 1)) = x n}
  mul_mem' hx hy n := by simp [map_mul, hx n, hy n]
  one_mem' n := by simp
  add_mem' hx hy n := by simp [map_add, hx n, hy n]
  zero_mem' n := by simp
  neg_mem' hx n := by simp [map_neg, hx n]

/-- The projection `lim Qₙ → Qₙ`. -/
def towerLimitRingπ (n : ℕ) : towerLimitRing τ →+* Qs n :=
  (Pi.evalRingHom Qs n).comp (towerLimitRing τ).subtype

lemma continuous_towerLimitRingπ (n : ℕ) : Continuous (towerLimitRingπ τ n) :=
  (continuous_apply n).comp continuous_subtype_val

omit [∀ n, TopologicalSpace (Qs n)] in
lemma towerLimitRingπ_comp (n : ℕ) :
    (τ n).comp (towerLimitRingπ τ (n + 1)) = towerLimitRingπ τ n :=
  RingHom.ext fun x ↦ x.2 n

variable [∀ n, IsTopologicalRing (Qs n)] [∀ n, DiscreteTopology (Qs n)]

/-- **The limit of a tower of constant pro-étale sheaves**: for a tower of discrete rings `Qₙ`,
the sheaf `C(-, lim Qₙ)` is the limit of the comparison pullbacks `ν^* Qₙ` of the constant étale
sheaves (`AlgebraicGeometry.ProEtale.comparisonUpperStarConstantSheafTowerIso`,
`AlgebraicGeometry.ProEtale.isLimitContinuousMapAbSheafCone`). -/
noncomputable def isLimitContinuousMapAbSheafConeTowerLimitRing (T : Scheme.{u}) :
    IsLimit (continuousMapAbSheafCone T τ (fun _ ↦ continuous_of_discreteTopology)
      (towerLimitRingπ τ) (continuous_towerLimitRingπ τ) (towerLimitRingπ_comp τ)) :=
  isLimitContinuousMapAbSheafCone T _ _ _ _ _
    (fun _ _ h ↦ Subtype.ext (funext h))
    (fun q hq ↦ ⟨⟨q, hq⟩, fun _ ↦ rfl⟩)
    (IsInducing.subtypeVal)

/-- `lim_n ν^* Qₙ ≅ C(-, lim Qₙ)`: the cone over the tower of comparison pullbacks of constant
étale sheaves with point `C(-, lim Qₙ)` is a limit cone. -/
noncomputable def isLimitComparisonUpperStarConstantSheafTower (T : Scheme.{u}) :
    IsLimit ((Cone.postcompose (comparisonUpperStarConstantSheafTowerIso T τ).inv).obj
      (continuousMapAbSheafCone T τ (fun _ ↦ continuous_of_discreteTopology)
        (towerLimitRingπ τ) (continuous_towerLimitRingπ τ) (towerLimitRingπ_comp τ))) :=
  (IsLimit.postcomposeInvEquiv _ _).symm (isLimitContinuousMapAbSheafConeTowerLimitRing τ T)

end AlgebraicGeometry.ProEtale
