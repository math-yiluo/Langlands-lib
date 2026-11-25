/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralUpperShriekCompatibility
public import WeilConjectures.TraceFormula.Specialization.DefectCentreMap
public import WeilConjectures.TraceFormula.Specialization.NearbySmoothExchangeLocal
public import WeilConjectures.TraceFormula.Specialization.NearbySmoothExchangeIntegral
public import WeilConjectures.TraceFormula.Specialization.NearbySmoothExchangeIntegralInput
public import WeilConjectures.TraceFormula.Specialization.NormalizePrecoherent

/-!

# The smooth exchange of nearby cycles for the deformation to the normal cone

For a smooth morphism `f : X ⟶ Y` of separated `k`-schemes of finite type and `J = f⁻¹ I`, the
morphism of deformation models `f̃ : 𝒟_J X ⟶ 𝒟_I Y` is the base change of `f`, hence smooth
(`ProEtale.CondensedRing.smooth_deformationTotalMap`), and its square of geometric generic fibres is
cartesian. By smooth base change, its pullback exchange `α_{f̃} : Lf_s^* Ψ_Y ⟶ Ψ_X Lf^*` is an
isomorphism on bounded constructible `ℚ̄_ℓ`-complexes
(`ProEtale.CondensedRing.isIso_pullbackExchange_deformationModel_app_of_smooth`).

## Proof

`ProEtale.CondensedRing.isIso_pullbackExchange_deformationModel_app_of_smooth` (the smooth half
of blueprint `prose-E-03` (1), applied to the smooth morphism of deformation
models of blueprint `lemma-functoriality-deformation` (3)) is reduced, by
`ProEtale.CondensedRing.NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_isIso_baseChangeMap_app`
and `ProEtale.CondensedRing.isIso_baseChangeMap_app_of_smooth` (locally on the source a smooth
morphism is étale over an affine space), to smooth base change along the projections
`𝔸ⁿ_𝒴 ⟶ 𝒴` for the inclusion `j` of the geometric generic fibre,
`ProEtale.CondensedRing.isIso_baseChangeMap_affineSpace_deformationModel_app` (blueprint
`theorem-smooth-base-change-all-admissible--1`). This is in turn reduced to integral coefficients
by integral models and the coefficient change `𝒪_E ⟶ ℚ̄_ℓ` of base change maps along qcqs
morphisms
(`ProEtale.CondensedRing.isIso_baseChangeMap_app_leftDerivedUpperStar_padicAlgCl_of_integral`).
The integral statement,
`ProEtale.CondensedRing.isIso_baseChangeMap_affineSpace_deformationModel_app_padicIntegers`, is
integral smooth base change for qcqs pushforward, proved by derived Nakayama for derived complete
complexes (`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicIntegers_of_smooth`).

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (k' : Type u) [Field k'] [Algebra k k']

/-- **Smooth base change along affine spaces for the geometric generic fibre** (blueprint
`theorem-smooth-base-change-all-admissible--1`, for the projection `π : 𝔸ⁿ_𝒴 ⟶ 𝒴`): for the
inclusion `j : 𝒴_Ω ⟶ 𝒴` of the geometric generic fibre of the deformation model `𝒴 = 𝒟_I Y` and the
cartesian square of `j` along `π`, the base change morphism `Lπ^* Rj_* ⟶ Rj'_* Lπ'^*` is invertible
at `Lε^* K` for every bounded constructible `ℚ̄_ℓ`-complex `K` on `Y`.

The morphism `j` is not of finite type (it is a base change of the geometric generic point
`Spec Ω ⟶ Spec k'⟦t⟧` of the trait), so the finite-type smooth base change
`ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_smooth` does not apply. Writing
`K ≅ ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} K₀)` for an integral model `K₀`, this follows from the integral statement
`ProEtale.CondensedRing.isIso_baseChangeMap_affineSpace_deformationModel_app_padicIntegers`
by
`ProEtale.CondensedRing.isIso_baseChangeMap_app_leftDerivedUpperStar_padicAlgCl_of_integral`. -/
theorem isIso_baseChangeMap_affineSpace_deformationModel_app {Y : Over (Spec (.of k))}
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (I : Y.left.IdealSheafData) (n : ℕ)
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left))}
    (hK : boundedConstructible _ K) :
    IsIso ((baseChangeMap (Profinite.padicAlgClRingObj ℓ)
      (IsPullback.of_hasPullback (deformationModel Y I k').j
        (𝔸(ULift.{u} (Fin n); (deformationModel Y I k').total) ↘
          (deformationModel Y I k').total)).toCommSq).app
      ((L(((deformationModel Y I k').ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K)) := by
  have := noetherianSpace_left_of_over Y
  have : QuasiCompact (deformationModel Y I k').j := by
    rw [deformationModel_j, deformationGenericToTotal]
    infer_instance
  have : QuasiSeparated (deformationModel Y I k').j := by
    rw [deformationModel_j, deformationGenericToTotal]
    infer_instance
  exact isIso_baseChangeMap_app_leftDerivedUpperStar_padicAlgCl_of_integral ℓ _ _ hK
    fun E _ hK₀ ↦ isIso_baseChangeMap_affineSpace_deformationModel_app_padicIntegers k' I n E hK₀

/-- **The smooth exchange of nearby cycles** (blueprint `prose-E-03` (1),
smooth case, for the morphism of deformation models of blueprint `lemma-functoriality-deformation`
(3); SGA 7 XIII 2.1.7.1): for a morphism `φ : 𝒟_J X ⟶ 𝒟_I Y` of deformation models whose morphism of
total spaces is smooth and whose square of geometric generic fibres is cartesian (for instance the
deformation of a smooth `f` with `J = f⁻¹ I`), the pullback exchange `α_φ : Lg_s^* Ψ_Y ⟶ Ψ_X Lg^*`
is an isomorphism on bounded constructible `ℚ̄_ℓ`-complexes, by smooth base change along the
inclusion `j` of the geometric generic fibre. -/
theorem isIso_pullbackExchange_deformationModel_app_of_smooth [IsSepClosed k']
    [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    {I : Y.left.IdealSheafData} {J : X.left.IdealSheafData} {g : X.left ⟶ Y.left}
    {g' : (deformationSpecialFibre X J k').left ⟶ (deformationSpecialFibre Y I k').left}
    (φ : (deformationModel X J k').Hom (deformationModel Y I k') g g') [Smooth φ.total]
    (hj : IsPullback φ.generic (deformationModel X J k').j (deformationModel Y I k').j φ.total)
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left))}
    (hK : boundedConstructible _ K) :
    IsIso ((φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app K) := by
  have : CompactSpace (deformationModel X J k').total :=
    QuasiCompact.compactSpace_of_compactSpace (deformationTotalToTrait X J k')
  have : QuasiSeparatedSpace (deformationModel X J k').total :=
    quasiSeparatedSpace_of_quasiSeparated (deformationTotalToTrait X J k')
  have hA (n : ℕ) := isIso_baseChangeMap_affineSpace_deformationModel_app k' I n hK
  have h₁ := φ.isIso_pullbackExchange_app_of_isIso_baseChangeMap_app
    (Profinite.padicAlgClRingObj ℓ) K
  have h₂ := isIso_baseChangeMap_app_of_smooth (Profinite.padicAlgClRingObj ℓ) hj
    ((L(((deformationModel Y I k').ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K)
  rw [Subsingleton.elim hj.toCommSq φ.commSq_j] at h₂
  revert hA h₁ h₂
  normalize_precoherent
  intro hA h₁ h₂
  exact h₁ (h₂ hA)

end AlgebraicGeometry.ProEtale.CondensedRing
