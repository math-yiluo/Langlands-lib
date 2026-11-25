/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Uniformizer
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionConstructible
public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComapQuotient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ProjectiveTensorUnitCover
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.ConstructibleReading
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.ReductionHomologyCenter

/-!
# Surjectivity and injectivity of a uniformizer on the cohomology sheaves

If `K₁ = 𝔽_{E,X} ⊗ᴸ K` has cohomology in degrees `[a, b]`, then `ϖ` is surjective on `Hᵠ K` for
`q ∉ [a, b]` and injective on `Hᵠ K` for `q ∉ [a + 1, b + 1]`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : FiniteIntermediateField ℓ}
variable {X : Scheme.{u}} {ϖ : PadicAlgCl.integers ℓ E.1}

/-- If `K₁ = 𝔽_{E,X} ⊗ᴸ K` has cohomology in degrees `[a, b]`, then `ϖ` acts surjectively on
`Hᵠ K` for `q < a`. -/
theorem epi_padicIntegersCenter_homology_of_lt
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1) = Ideal.span {ϖ})
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))} {a b : ℤ}
    (hab : ∀ i, i < a ∨ b < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((Mod.comap (padicIntegersToResidueField X ℓ E)).mapDerivedCategory.obj
        ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj K))))
    {q : ℤ} (hq : q < a) :
    Epi ((padicIntegersCenter X ℓ E ϖ).app ((DerivedCategory.homologyFunctor _ q).obj K)) :=
  have hT := (Mod.exists_distinguished_regularEndCenter_derivedExtendScalars _
    (shortExact_padicIntegersRegularEnd X ℓ E ϖ hϖ) K).choose_spec.choose_spec
  CatCenter.epi_app_homologyFunctor_obj_of_isZero _ hT q (hab q (Or.inl hq))

/-- If `K₁ = 𝔽_{E,X} ⊗ᴸ K` has cohomology in degrees `[a, b]`, then `ϖ` acts surjectively on
`Hᵠ K` for `q > b`. -/
theorem epi_padicIntegersCenter_homology_of_gt
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1) = Ideal.span {ϖ})
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))} {a b : ℤ}
    (hab : ∀ i, i < a ∨ b < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((Mod.comap (padicIntegersToResidueField X ℓ E)).mapDerivedCategory.obj
        ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj K))))
    {q : ℤ} (hq : b < q) :
    Epi ((padicIntegersCenter X ℓ E ϖ).app ((DerivedCategory.homologyFunctor _ q).obj K)) :=
  have hT := (Mod.exists_distinguished_regularEndCenter_derivedExtendScalars _
    (shortExact_padicIntegersRegularEnd X ℓ E ϖ hϖ) K).choose_spec.choose_spec
  CatCenter.epi_app_homologyFunctor_obj_of_isZero _ hT q (hab q (Or.inr hq))

/-- If `K₁ = 𝔽_{E,X} ⊗ᴸ K` has cohomology in degrees `[a, b]`, then `ϖ` acts injectively on
`Hᵠ K` for `q ≤ a`. -/
theorem mono_padicIntegersCenter_homology_of_le
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1) = Ideal.span {ϖ})
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))} {a b : ℤ}
    (hab : ∀ i, i < a ∨ b < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((Mod.comap (padicIntegersToResidueField X ℓ E)).mapDerivedCategory.obj
        ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj K))))
    {q : ℤ} (hq : q ≤ a) :
    Mono ((padicIntegersCenter X ℓ E ϖ).app ((DerivedCategory.homologyFunctor _ q).obj K)) :=
  have hT := (Mod.exists_distinguished_regularEndCenter_derivedExtendScalars _
    (shortExact_padicIntegersRegularEnd X ℓ E ϖ hϖ) K).choose_spec.choose_spec
  CatCenter.mono_app_homologyFunctor_obj_of_isZero _ hT (q - 1) q (sub_add_cancel q 1)
    (hab (q - 1) (Or.inl (Int.sub_one_lt_of_le hq)))

/-- If `K₁ = 𝔽_{E,X} ⊗ᴸ K` has cohomology in degrees `[a, b]`, then `ϖ` acts injectively on
`Hᵠ K` for `q > b + 1`. -/
theorem mono_padicIntegersCenter_homology_of_gt
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1) = Ideal.span {ϖ})
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))} {a b : ℤ}
    (hab : ∀ i, i < a ∨ b < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((Mod.comap (padicIntegersToResidueField X ℓ E)).mapDerivedCategory.obj
        ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj K))))
    {q : ℤ} (hq : b + 1 < q) :
    Mono ((padicIntegersCenter X ℓ E ϖ).app ((DerivedCategory.homologyFunctor _ q).obj K)) :=
  have hT := (Mod.exists_distinguished_regularEndCenter_derivedExtendScalars _
    (shortExact_padicIntegersRegularEnd X ℓ E ϖ hϖ) K).choose_spec.choose_spec
  CatCenter.mono_app_homologyFunctor_obj_of_isZero _ hT (q - 1) q (sub_add_cancel q 1)
    (hab (q - 1) (Or.inr (lt_sub_iff_add_lt.2 hq)))

end AlgebraicGeometry.ProEtale
