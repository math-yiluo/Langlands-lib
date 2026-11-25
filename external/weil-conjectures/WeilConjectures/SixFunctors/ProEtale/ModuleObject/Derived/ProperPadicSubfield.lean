/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperNoetherianBase
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionFormulaPadicAlgCl
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionFormulaPadicIntegers
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionFormulaPadicSubfieldAux

/-!
# Proper base change and the projection formula for `E`-sheaves

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ`. This file deduces proper base change and the
proper projection formula for bounded constructible `E`-complexes from the integral statements
(blueprint `proposition-proper-direct-image-constructible-complexes` (3), for `Λ = E`):

* `ProEtale.CondensedRing.isIso_baseChangeMap_app_padicSubfield_of_isProper`: for a cartesian
  square `g' ≫ p = p' ≫ g` with `p` proper over noetherian bases over fields in which `ℓ` is
  invertible, the base change map with coefficients `E` is invertible at every bounded
  constructible `E`-complex;
* `ProEtale.CondensedRing.isIso_projectionMap_continuousMapRingObj_of_boundedConstructible`: for
  a proper `p`, the projection map with coefficients `E` is invertible at bounded constructible
  `E`-complexes.

A bounded constructible `E`-complex `K` has an integral model: `K ≅ E ⊗ᴸ_{𝒪_E} K₀` for a bounded
constructible `𝒪_E`-complex `K₀`
(`ProEtale.CondensedRing.exists_derivedExtendScalars_iso_integralModel`),
and the extension of scalars `𝒪_E ⟶ E` is flat and commutes with the direct images of bounded
below complexes, so both statements are transported from `𝒪_E` to `E`
(`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicSubfield_of_padicIntegers`,
`ProEtale.CondensedRing.isIso_projectionMap_app_app_padicSubfield_of_padicIntegers`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **Integral models of `E`-complexes on the ambient derived categories**
(`ProEtale.exists_boundedConstructibleExtendScalars_obj_iso`): every bounded constructible
`E`-complex `K` on a topologically noetherian scheme is isomorphic to `E ⊗ᴸ_{𝒪_E} K₀` for a
bounded constructible `𝒪_E`-complex `K₀`. -/
theorem exists_derivedExtendScalars_iso_integralModel (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X] (E : FiniteIntermediateField ℓ)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.1) X)))
    (hK : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E.1) X) K) :
    ∃ K₀ : BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X),
      Nonempty ((Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
        X)).leftDerivedFunctor.obj K₀.obj ≅ K) := by
  have k := exists_boundedConstructibleExtendScalars_obj_iso X ℓ E ⟨K, hK⟩
  obtain ⟨K₀, he⟩ := k
  exact ⟨K₀, ⟨((boundedConstructibleExtendScalarsCompatibility X ℓ E).app K₀).symm ≪≫
    (boundedConstructible _).ι.mapIso he.some⟩⟩

/-- **Proper base change for `E`-sheaves over noetherian bases over fields**: for a cartesian
square `g' ≫ p = p' ≫ g` of schemes with `p` proper, `Y` a noetherian `k`-scheme and `Y'` a
noetherian `k₂`-scheme for fields `k` and `k₂` in which `ℓ` is invertible, the base change map
`Lg^* Rp_* ⟶ Rp'_* Lg'^*` with coefficients `E` is invertible at every bounded constructible
`E`-complex `K`. The complex `K` has an integral model `E ⊗ᴸ_{𝒪_E} K₀`
(`exists_derivedExtendScalars_iso_integralModel`), at which the base change map is invertible
since the integral one is at `K₀`
(`isIso_baseChangeMap_app_padicIntegers_of_isProper_of_isNoetherian`,
`isIso_baseChangeMap_app_padicSubfield_of_padicIntegers`). -/
theorem isIso_baseChangeMap_app_padicSubfield_of_isProper
    {k k₂ : Type u} [Field k] [Field k₂] [Fact (ringChar k ≠ ℓ)] [Fact (ringChar k₂ ≠ ℓ)]
    {X Y X' Y' : Scheme.{u}} [IsNoetherian Y] [IsNoetherian Y'] (aY : Y ⟶ Spec (.of k))
    (aY' : Y' ⟶ Spec (.of k₂)) {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}
    [IsProper p] (sq : CommSq g' p' p g) (hsq : IsPullback g' p' p g)
    (E : FiniteIntermediateField ℓ)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.1) X)))
    (hK : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E.1) X) K) :
    IsIso ((baseChangeMap (Profinite.continuousMapRingObj E.1) sq).app K) := by
  have : IsProper p' := MorphismProperty.of_isPullback (P := @IsProper) hsq inferInstance
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType p
  have k := exists_derivedExtendScalars_iso_integralModel ℓ X E K hK
  obtain ⟨K₀, he⟩ := k
  have : K₀.obj.IsGE K₀.property.1.1.choose := K₀.property.1.1.choose_spec
  rw [← NatTrans.isIso_app_iff_of_iso _ he.some]
  exact isIso_baseChangeMap_app_padicSubfield_of_padicIntegers ℓ E sq K₀.obj
    K₀.property.1.1.choose inferInstance
    (isIso_baseChangeMap_app_padicIntegers_of_isProper_of_isNoetherian ℓ aY aY' sq hsq E K₀)

variable {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **The projection formula for `E`** (blueprint
`proposition-proper-direct-image-constructible-complexes` (3), for `Λ = E`): for a proper
`p : X ⟶ Y` and bounded constructible `E`-complexes `K` on `X` and `M` on `Y`, the projection map
`Rp_* K ⊗ᴸ M ⟶ Rp_*(K ⊗ᴸ Lp^* M)` is an isomorphism. The complexes have integral models
`E ⊗ᴸ_{𝒪_E} K₀` and `E ⊗ᴸ_{𝒪_E} M₀` (`exists_derivedExtendScalars_iso_integralModel`), at which the
projection map is invertible since the integral one is at `(K₀, M₀)`
(`isIso_projectionMap_padicIntegersRingObj_of_boundedConstructible`,
`isIso_projectionMap_app_app_padicSubfield_of_padicIntegers`). -/
theorem isIso_projectionMap_continuousMapRingObj_of_boundedConstructible
    (E : FiniteIntermediateField ℓ) (p : X ⟶ Y) [IsProper p.left]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.1) X.left)))
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.1) Y.left)))
    (hK : boundedConstructible _ K) (hM : boundedConstructible _ M) :
    IsIso (((projectionMap (Profinite.continuousMapRingObj E.1) p.left).app K).app M) := by
  have := isNoetherian_of_locallyOfFiniteType X.hom
  have := isNoetherian_of_locallyOfFiniteType Y.hom
  have : QuasiCompact p.left :=
    have : QuasiCompact (p.left ≫ Y.hom) := by rw [Over.w p]; infer_instance
    QuasiCompact.of_comp p.left Y.hom
  have : QuasiSeparated p.left :=
    have : QuasiSeparated (p.left ≫ Y.hom) := by rw [Over.w p]; infer_instance
    QuasiSeparated.of_comp p.left Y.hom
  have kK := exists_derivedExtendScalars_iso_integralModel ℓ X.left E K hK
  have kM := exists_derivedExtendScalars_iso_integralModel ℓ Y.left E M hM
  obtain ⟨K₀, eK⟩ := kK
  obtain ⟨M₀, eM⟩ := kM
  have hKM₀ := (PadicIntegersRingObj.isMonoidal_boundedConstructible ℓ E.1 X).toTensorLE.prop_tensor
    _ _ K₀.property (boundedConstructible_leftDerivedUpperStar_obj _ ℓ p M₀)
  have e₁ := isIso_projectionMap_app_app_padicSubfield_of_padicIntegers_aux ℓ E p.left K₀.obj
    M₀.obj _ _ (exists_isGE_of_boundedConstructible K₀.property).choose_spec
    (exists_isGE_of_boundedConstructible hKM₀).choose_spec
    (isIso_projectionMap_padicIntegersRingObj_of_boundedConstructible ℓ E.1 p K₀.obj M₀.obj
      K₀.property M₀.property)
  exact NatTrans.isIso_app_app_of_iso
    (projectionMap (Profinite.continuousMapRingObj E.1) p.left) eK.some eM.some

end AlgebraicGeometry.ProEtale.CondensedRing
