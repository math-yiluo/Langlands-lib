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
# The action of a uniformizer on the cohomology sheaves of an `𝒪_E`-complex

The reduction triangle `K --ϖ--> K ⟶ K₁ ⟶ K[1]`, where `K₁ = 𝔽_{E,X} ⊗ᴸ K`, relates the cokernel
and the kernel of `ϖ` on the cohomology sheaves of `K` to the cohomology sheaves of `K₁`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : FiniteIntermediateField ℓ}
variable {X : Scheme.{u}} {ϖ : PadicAlgCl.integers ℓ E.1}

/-- If `Hᵠ¹ K = 0`, the cokernel of `ϖ` on `Hᵠ⁰ K` is `Hᵠ⁰ K₁` as an `𝒪_{E,X}`-module, where
`q₀ + 1 = q₁` and `K₁ = 𝔽_{E,X} ⊗ᴸ K`. -/
theorem nonempty_cokernel_padicIntegersCenter_homology_iso
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1) = Ideal.span {ϖ})
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) (q₀ q₁ : ℤ)
    (hq : q₀ + 1 = q₁) (h₁ : IsZero ((DerivedCategory.homologyFunctor _ q₁).obj K)) :
    Nonempty (cokernel ((padicIntegersCenter X ℓ E ϖ).app
        ((DerivedCategory.homologyFunctor _ q₀).obj K)) ≅
      (DerivedCategory.homologyFunctor _ q₀).obj
        ((Mod.comap (padicIntegersToResidueField X ℓ E)).mapDerivedCategory.obj
          ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj K))) :=
  have hT := (Mod.exists_distinguished_regularEndCenter_derivedExtendScalars _
    (shortExact_padicIntegersRegularEnd X ℓ E ϖ hϖ) K).choose_spec.choose_spec
  CatCenter.nonempty_cokernel_app_homologyFunctor_obj_iso _ hT q₀ q₁ hq h₁

/-- The kernel of `ϖ` on `Hᵠ¹ K` is a quotient of `Hᵠ⁰ K₁`, where `q₀ + 1 = q₁` and
`K₁ = 𝔽_{E,X} ⊗ᴸ K`. -/
theorem exists_epi_kernel_padicIntegersCenter_homology
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1) = Ideal.span {ϖ})
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) (q₀ q₁ : ℤ)
    (hq : q₀ + 1 = q₁) :
    ∃ f : (DerivedCategory.homologyFunctor _ q₀).obj
        ((Mod.comap (padicIntegersToResidueField X ℓ E)).mapDerivedCategory.obj
          ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj K)) ⟶
      kernel ((padicIntegersCenter X ℓ E ϖ).app ((DerivedCategory.homologyFunctor _ q₁).obj K)),
      Epi f :=
  have hT := (Mod.exists_distinguished_regularEndCenter_derivedExtendScalars _
    (shortExact_padicIntegersRegularEnd X ℓ E ϖ hϖ) K).choose_spec.choose_spec
  CatCenter.exists_epi_kernel_app_homologyFunctor_obj _ hT q₀ q₁ hq

/-- If `Hᵠ K₁ = 0`, then `ϖ` acts surjectively on `Hᵠ K`, where `K₁ = 𝔽_{E,X} ⊗ᴸ K`. -/
theorem epi_padicIntegersCenter_homology_of_isZero
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1) = Ideal.span {ϖ})
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) (q : ℤ)
    (hq : IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((Mod.comap (padicIntegersToResidueField X ℓ E)).mapDerivedCategory.obj
        ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj K)))) :
    Epi ((padicIntegersCenter X ℓ E ϖ).app ((DerivedCategory.homologyFunctor _ q).obj K)) :=
  have hT := (Mod.exists_distinguished_regularEndCenter_derivedExtendScalars _
    (shortExact_padicIntegersRegularEnd X ℓ E ϖ hϖ) K).choose_spec.choose_spec
  CatCenter.epi_app_homologyFunctor_obj_of_isZero _ hT q hq

/-- If `Hᵠ⁻¹ K₁ = 0`, then `ϖ` acts injectively on `Hᵠ K`, where `K₁ = 𝔽_{E,X} ⊗ᴸ K`. -/
theorem mono_padicIntegersCenter_homology_of_isZero
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1) = Ideal.span {ϖ})
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) (q : ℤ)
    (hq : IsZero ((DerivedCategory.homologyFunctor _ (q - 1)).obj
      ((Mod.comap (padicIntegersToResidueField X ℓ E)).mapDerivedCategory.obj
        ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj K)))) :
    Mono ((padicIntegersCenter X ℓ E ϖ).app ((DerivedCategory.homologyFunctor _ q).obj K)) :=
  have hT := (Mod.exists_distinguished_regularEndCenter_derivedExtendScalars _
    (shortExact_padicIntegersRegularEnd X ℓ E ϖ hϖ) K).choose_spec.choose_spec
  CatCenter.mono_app_homologyFunctor_obj_of_isZero _ hT (q - 1) q (sub_add_cancel q 1) hq

end AlgebraicGeometry.ProEtale
