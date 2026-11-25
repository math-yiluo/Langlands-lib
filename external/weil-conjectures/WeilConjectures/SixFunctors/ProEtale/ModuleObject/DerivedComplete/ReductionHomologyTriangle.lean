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

/-!
# The reduction triangle of an `𝒪_E`-complex

The reduction triangle `K --ϖ--> K ⟶ K₁ ⟶ K[1]`, with `K₁ = 𝔽_{E,X} ⊗ᴸ K` regarded as a complex of
`𝒪_{E,X}`-modules.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : FiniteIntermediateField ℓ}
variable {X : Scheme.{u}} {ϖ : PadicAlgCl.integers ℓ E.1}

/-- The reduction triangle `K --ϖ--> K ⟶ K₁ ⟶ K[1]`, with `K₁ = 𝔽_{E,X} ⊗ᴸ K` regarded as a
complex of `𝒪_{E,X}`-modules. -/
lemma exists_distinguished_derivedUniformizer
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1) = Ideal.span {ϖ})
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) :
    ∃ (g : K ⟶ (Mod.comap (padicIntegersToResidueField X ℓ E)).mapDerivedCategory.obj
        ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj K))
      (h : (Mod.comap (padicIntegersToResidueField X ℓ E)).mapDerivedCategory.obj
        ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj K) ⟶
        K⟦(1 : ℤ)⟧),
      Triangle.mk ((padicIntegersCenter X ℓ E ϖ).derivedCategory.app K) g h ∈ distTriang _ :=
  Mod.exists_distinguished_regularEndCenter_derivedExtendScalars _
    (shortExact_padicIntegersRegularEnd X ℓ E ϖ hϖ) K

end AlgebraicGeometry.ProEtale
