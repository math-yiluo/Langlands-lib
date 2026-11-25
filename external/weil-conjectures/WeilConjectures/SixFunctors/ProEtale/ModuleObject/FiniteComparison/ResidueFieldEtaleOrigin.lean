/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionConstructible

/-!
# The reduction of a bounded constructible `𝒪_E`-complex is of étale origin

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with residue field `𝔽_E` and `X` a noetherian
scheme. For a bounded constructible complex `K₀` of `𝒪_{E,X}`-module objects, the reduction
`K₀ ⊗ᴸ_{𝒪_{E,X}} 𝔽̲_{E,X}`, read through the finite-coefficient comparison
`ProEtale.finiteCoefficientDerivedEquivalence` as a complex of pro-étale sheaves of
`𝔽_E`-modules, is bounded constructible
(`ProEtale.CondensedRing.boundedConstructible_finiteCoefficientDerivedEquivalence_residueField`),
hence bounded below of étale origin
(`ProEtale.CondensedRing.plusEtaleOrigin_extendScalars_residueField_of_boundedConstructible`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

/-- On a noetherian scheme `X`, the reduction `K₀ ⊗ᴸ 𝔽̲_E` of a bounded constructible
`𝒪_E`-complex `K₀`, read as a complex of pro-étale sheaves of `𝔽_E`-modules through
`finiteCoefficientDerivedEquivalence`, lies in `Dᵇc(X, 𝔽_E)`: the reduction is bounded
constructible (`ProEtale.boundedConstructible_derivedExtendScalars_residueField`), and
`finiteCoefficientModEquivalence` preserves constructibility
(`ProEtale.isConstructible_finiteCoefficientModEquivalence_functor_obj`). -/
theorem boundedConstructible_finiteCoefficientDerivedEquivalence_residueField {ℓ : ℕ}
    [Fact ℓ.Prime] {X : Scheme.{u}} [IsNoetherian X] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {K₀ : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))}
    (hK₀ : boundedConstructible _ K₀) :
    DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ULift.{u + 1} (integersResidueField ℓ E.1))) X
      ((finiteCoefficientDerivedEquivalence X (integersResidueField ℓ E.1)).functor.obj
        ((Mod.extendScalars (coefficientMap (Profinite.padicIntegersRingObjToResidueField ℓ E.1)
          X)).leftDerivedFunctor.obj K₀)) := by
  have hL := boundedConstructible_derivedExtendScalars_residueField X ℓ E.1 K₀ hK₀
  rw [← DerivedCategory.boundedConstructibleIntrinsic_eq]
  refine ⟨(finiteCoefficientModEquivalence X
    (integersResidueField ℓ E.1)).functor.bounded_mapDerivedCategory_obj hL.1, fun n ↦ ?_⟩
  exact isConstructible_of_iso (((finiteCoefficientModEquivalence X
    (integersResidueField ℓ E.1)).functor.mapDerivedCategoryHomologyFunctorIso n).app _)
    (isConstructible_finiteCoefficientModEquivalence_functor_obj _ (hL.2 n))

/-- **The reduction of a bounded constructible `𝒪_E`-complex is of étale origin**: on a
noetherian scheme `X`, for a bounded constructible `𝒪_E`-complex `K₀`, the reduction
`K₀ ⊗ᴸ 𝔽̲_E`, read through `finiteCoefficientDerivedEquivalence`, is bounded below of étale
origin. -/
theorem plusEtaleOrigin_extendScalars_residueField_of_boundedConstructible {ℓ : ℕ}
    [Fact ℓ.Prime] {X : Scheme.{u}} [IsNoetherian X] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {K₀ : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))}
    (hK₀ : boundedConstructible _ K₀) :
    DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (integersResidueField ℓ E.1))) X
      ((finiteCoefficientDerivedEquivalence X (integersResidueField ℓ E.1)).functor.obj
        ((Mod.extendScalars (coefficientMap (Profinite.padicIntegersRingObjToResidueField ℓ E.1)
          X)).leftDerivedFunctor.obj K₀)) :=
  (boundedConstructible_finiteCoefficientDerivedEquivalence_residueField E hK₀).plusEtaleOrigin

end AlgebraicGeometry.ProEtale.CondensedRing
