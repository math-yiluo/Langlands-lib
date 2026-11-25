/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCompletion
public import WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients

/-!
# Reductions of derived completions

Let `Λ` be a ring with a nonzerodivisor `ϖ`. On `D(X_ét, Λ)` the reductions
`K ↦ K ⊗ᴸ (Λ/ϖⁿ)_X` (`AlgebraicGeometry.Etale.reductionModIdeal`) kill the objects on which `ϖ`
acts invertibly (`AlgebraicGeometry.Etale.isZero_reductionModIdeal_of_isIso_smul_id`). Hence
they invert the unit `K ⟶ K^` of the derived completion: an object and its derived completion
have the same reductions. This is how the operations of the integral stage `𝒪_E`, defined by
completing the étale operations, are compared with the finite levels: their reductions are the
étale operations of the reductions.

## Main statements

- `AlgebraicGeometry.Etale.isZero_reductionModIdeal_of_isIso_smul_id`
- `AlgebraicGeometry.Etale.isIso_reductionModIdeal_map_completionAdjunction_unit_app`: the
  reduction of the unit `K ⟶ K^` of the integral derived completion is an isomorphism.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Pretriangulated Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance instEssentiallySmallEtale_reduction
    (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

section General

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- **Reduction kills the objects on which `ϖ` acts invertibly.** For a nonzerodivisor `ϖ` of
`Λ`, `n : ℕ` and `K ∈ D(X_ét, Λ)` on which `ϖ` acts invertibly, the reduction
`K ⊗ᴸ (Λ/ϖⁿ)_X` vanishes: it is the cone of the isomorphism `ϖⁿ : K ⟶ K`. -/
theorem isZero_reductionModIdeal_of_isIso_smul_id {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
    (n : ℕ) (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : IsIso (ϖ • 𝟙 K)) :
    IsZero ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ n)).obj K) := by
  let F := (derivedTensor (ModuleCat.{u + 1} Λ) X).obj K
  let T := _root_.DerivedCategory.quotPowTriangle X.smallEtaleTopology hϖ rfl n
  have hT : F.mapTriangle.obj T ∈ distTriang _ :=
    F.map_distinguished _ (_root_.DerivedCategory.quotPowTriangle_distinguished _ hϖ rfl n)
  have hmor : (F.mapTriangle.obj T).mor₁ = ϖ ^ n • 𝟙 (F.obj T.obj₁) := by
    change F.map T.mor₁ = _
    rw [_root_.DerivedCategory.quotPowTriangle_mor₁, Functor.map_smul,
      CategoryTheory.Functor.map_id]
  let u : F.obj T.obj₁ ≅ K := derivedTensorSingleUnitIso K
  have hK' : IsIso (ϖ ^ n • 𝟙 K) :=
    (_root_.DerivedCategory.smulInvertible.pow (J := X.smallEtaleTopology) hK n)
  have h₁ : IsIso (F.mapTriangle.obj T).mor₁ := by
    have : ϖ ^ n • 𝟙 (F.obj T.obj₁) = u.hom ≫ (ϖ ^ n • 𝟙 K) ≫ u.inv := by
      rw [Linear.smul_comp, Category.id_comp, Linear.comp_smul, Iso.hom_inv_id]
    rw [hmor, this]
    infer_instance
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).2 h₁

/-- A morphism `s : K ⟶ K'` sitting in a distinguished triangle `K ⟶ K' ⟶ C ⟶ K⟦1⟧` with `ϖ`
acting invertibly on `C` induces isomorphisms on all the reductions modulo `ϖⁿ`. -/
theorem isIso_reductionModIdeal_map_of_distinguished {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
    (n : ℕ) {K K' C : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {s : K ⟶ K'} {g : K' ⟶ C} {h : C ⟶ K⟦(1 : ℤ)⟧} (hT : Triangle.mk s g h ∈ distTriang _)
    (hC : IsIso (ϖ • 𝟙 C)) : IsIso ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ n)).map s) :=
  (Triangle.isZero₃_iff_isIso₁ _ ((reductionModIdeal Λ X _).map_distinguished _ hT)).1
    (isZero_reductionModIdeal_of_isIso_smul_id hϖ n C hC)

end General

section Integral

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Small.{u + 1} E] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E]

/-- **An object and its derived completion have the same reductions.** For `E` finite over
`ℚ_ℓ` and `K ∈ D(X_ét, 𝒪_E)`, the reduction modulo `𝔪_Eⁿ` of the unit `K ⟶ K^` of the derived
completion is an isomorphism. -/
theorem isIso_reductionModIdeal_map_completionAdjunction_unit_app {X : Scheme.{u}} (n : ℕ)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))))) :
    IsIso ((reductionModIdeal _ X (PadicAlgCl.maximalIdealShrink l E ^ n)).map
      ((DerivedCategoryDerivedCompleteIntegral.completionAdjunction
        X.smallEtaleTopology l E).unit.app K)) := by
  let h := PadicAlgCl.exists_mem_nonZeroDivisors_maximalIdealShrink_eq_span.{w, u} l E
  obtain ⟨C, g, h', hT, hC⟩ :=
    _root_.DerivedCategory.exists_distinguished_derivedCompletionAdjunction_unit_app
      (J := X.smallEtaleTopology) h K
  rw [h.choose_spec.2]
  exact isIso_reductionModIdeal_map_of_distinguished h.choose_spec.1 n hT hC

end Integral

end Etale

end AlgebraicGeometry
