/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicIntegralModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.SmoothPadicAlgCl

/-!
# Integral models and the base change map with coefficients `ℚ̄_ℓ`

On the ambient derived categories of module objects, a bounded constructible `ℚ̄_ℓ`-complex is
`ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} K₀)` for an integral model `K₀`
(`ProEtale.CondensedRing.exists_padicAlgCl_iso_integralModel_obj`). For a commutative square whose
vertical morphisms are quasi-compact and quasi-separated, if the integral base change map is
invertible at a bounded below `𝒪_E`-complex `R₀`, the `ℚ̄_ℓ`-base change map is invertible at every
complex isomorphic to `ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} R₀)`
(`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicAlgCl_of_isIso_integral`), by
`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicAlgCl_of_padicIntegers`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **The base change map under the coefficient changes `𝒪_E ⟶ E ⟶ ℚ̄_ℓ`**: for a commutative
square whose vertical morphisms are quasi-compact and quasi-separated, if the base change map with
coefficients `𝒪_E` is invertible at a bounded below `R₀`, then the base change map with
coefficients `ℚ̄_ℓ` is invertible at every object isomorphic to `ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} R₀)`
(`isIso_baseChangeMap_app_padicAlgCl_of_padicIntegers`, transported along the isomorphism). -/
theorem isIso_baseChangeMap_app_padicAlgCl_of_isIso_integral {X Y X' Y' : Scheme.{u}}
    {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X} [QuasiCompact p] [QuasiSeparated p]
    [QuasiCompact p'] [QuasiSeparated p'] (sq : CommSq g' p' p g) (E : FiniteIntermediateField ℓ)
    (R₀ : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) (n : ℤ) [R₀.IsGE n]
    (h : IsIso ((baseChangeMap (Profinite.padicIntegersRingObj ℓ E.1) sq).app R₀))
    {A : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (e : (Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
      X)).leftDerivedFunctor.obj ((Mod.extendScalars (coefficientMap
        (padicIntegersRingObjToContinuousMapRingObj ℓ E) X)).leftDerivedFunctor.obj R₀) ≅ A) :
    IsIso ((baseChangeMap (Profinite.padicAlgClRingObj ℓ) sq).app A) := by
  rw [← NatTrans.isIso_app_iff_of_iso _ e]
  exact isIso_baseChangeMap_app_padicAlgCl_of_padicIntegers ℓ E sq R₀ n inferInstance h

/-- **Integral models of `ℚ̄_ℓ`-complexes on the ambient derived categories**
(`ProEtale.exists_padicAlgCl_iso_integralModel`): every bounded constructible `ℚ̄_ℓ`-complex `K`
on a topologically noetherian scheme is isomorphic to `ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} K₀)` for a finite
subextension `E` and a bounded constructible `𝒪_E`-complex `K₀`, the extensions of scalars being
those of `isIso_baseChangeMap_app_padicAlgCl_of_isIso_integral`. -/
theorem exists_padicAlgCl_iso_integralModel_obj (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X]
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) K) :
    ∃ (E : FiniteIntermediateField ℓ)
      (K₀ : BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)),
      Nonempty ((Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
        X)).leftDerivedFunctor.obj ((Mod.extendScalars (coefficientMap
          (padicIntegersRingObjToContinuousMapRingObj ℓ E) X)).leftDerivedFunctor.obj K₀.obj) ≅
        K) := by
  have k := exists_padicAlgCl_iso_integralModel X ℓ ⟨K, hK⟩
  obtain ⟨E, K₀, he⟩ := k
  refine ⟨E, K₀, ⟨?_⟩⟩
  exact (derivedExtendScalarsToPadicAlgCl X ℓ E).mapIso
    ((boundedConstructibleExtendScalarsCompatibility X ℓ E).app K₀).symm ≪≫
    (boundedConstructible _).ι.mapIso he.some

end AlgebraicGeometry.ProEtale.CondensedRing
