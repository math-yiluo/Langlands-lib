/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.SmoothPadicIntegers
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.SmoothResidue
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.TraceFormula.Specialization.DeformationModel

/-!

# Integral smooth base change along affine spaces for the geometric generic fibre

For the inclusion `j : 𝒴_Ω ⟶ 𝒴` of the geometric generic fibre of the deformation model
`𝒴 = 𝒟_I Y` and the projection `π : 𝔸ⁿ_𝒴 ⟶ 𝒴`, the base change map `Lπ^* Rj_* ⟶ Rj'_* Lπ'^*` with
coefficients `𝒪_E` is invertible at `Lε^* K₀` for every bounded constructible `𝒪_E`-complex `K₀` on
`Y` (`ProEtale.CondensedRing.isIso_baseChangeMap_affineSpace_deformationModel_app_padicIntegers`).

## Proof

This is integral smooth base change for quasi-compact quasi-separated pushforward
(`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicIntegers_of_smooth`), applied to the
bounded constructible complex `Lε^* K₀` on the noetherian geometric generic fibre. Its proof
reduces modulo a uniformizer `ϖ` to smooth base change with coefficients `𝔽_E` and concludes by
derived Nakayama: both sides are derived complete, since bounded constructible complexes are
(`ProEtale.derivedCompleteIntegers_of_boundedConstructible`), derived pushforwards preserve
derived completeness, and so do derived pullbacks, which commute with derived limits because
pro-étale pullbacks preserve limits (`ProEtale.preservesLimitsOfSize_upperStar_ab`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (k' : Type u) [Field k'] [Algebra k k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

omit [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] in
/-- **Integral smooth base change along affine spaces for the geometric generic fibre** (the
`𝒪_E`-coefficient special case, for the projection `π : 𝔸ⁿ_𝒴 ⟶ 𝒴`, of smooth base change; the
blueprint node `theorem-smooth-base-change-all-admissible--1` is the torsion étale statement): for
the inclusion `j : 𝒴_Ω ⟶ 𝒴` of the geometric generic fibre of the deformation
model `𝒴 = 𝒟_I Y` and the cartesian square of `j` along `π`, the base change morphism
`Lπ^* Rj_* ⟶ Rj'_* Lπ'^*` with coefficients `𝒪_E` is invertible at `Lε^* K₀` for every bounded
constructible `𝒪_E`-complex `K₀` on `Y`. The geometric generic fibre is noetherian and `Lε^* K₀`
is bounded constructible, so this is
`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicIntegers_of_smooth`. -/
theorem isIso_baseChangeMap_affineSpace_deformationModel_app_padicIntegers
    {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (I : Y.left.IdealSheafData) (n : ℕ) (E : FiniteIntermediateField ℓ)
    {K₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y.left))}
    (hK₀ : boundedConstructible _ K₀) :
    IsIso ((baseChangeMap (Profinite.padicIntegersRingObj ℓ E.1)
      (IsPullback.of_hasPullback (deformationModel Y I k').j
        (𝔸(ULift.{u} (Fin n); (deformationModel Y I k').total) ↘
          (deformationModel Y I k').total)).toCommSq).app
      ((L(((deformationModel Y I k').ε)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj K₀)) := by
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : IsNoetherian Y.left := {}
  have : IsLocallyNoetherian (deformationGeneric Y I k') :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.snd (deformationTotalToTrait Y I k') (traitGenericPoint k'))
  have : CompactSpace (deformationGeneric Y I k') :=
    QuasiCompact.compactSpace_of_compactSpace
      (pullback.snd (deformationTotalToTrait Y I k') (traitGenericPoint k'))
  have : IsNoetherian (deformationModel Y I k').generic :=
    (⟨⟩ : IsNoetherian (deformationGeneric Y I k'))
  have : CompactSpace (deformationModel Y I k').total :=
    QuasiCompact.compactSpace_of_compactSpace (deformationTotalToTrait Y I k')
  have : QuasiSeparatedSpace (deformationModel Y I k').total :=
    quasiSeparatedSpace_of_quasiSeparated (deformationTotalToTrait Y I k')
  have : QuasiCompact (deformationModel Y I k').j := by
    rw [deformationModel_j, deformationGenericToTotal]
    infer_instance
  have : QuasiSeparated (deformationModel Y I k').j := by
    rw [deformationModel_j, deformationGenericToTotal]
    infer_instance
  have : Smooth (𝔸(ULift.{u} (Fin n); (deformationModel Y I k').total) ↘
      (deformationModel Y I k').total) :=
    SmoothOfRelativeDimension.smooth (Nat.card (ULift.{u} (Fin n))) _
  have : CompactSpace 𝔸(ULift.{u} (Fin n); (deformationModel Y I k').total) :=
    QuasiCompact.compactSpace_of_compactSpace
      (𝔸(ULift.{u} (Fin n); (deformationModel Y I k').total) ↘ (deformationModel Y I k').total)
  have : QuasiSeparatedSpace 𝔸(ULift.{u} (Fin n); (deformationModel Y I k').total) :=
    quasiSeparatedSpace_of_quasiSeparated
      (𝔸(ULift.{u} (Fin n); (deformationModel Y I k').total) ↘ (deformationModel Y I k').total)
  have : CompactSpace ↥(pullback (deformationModel Y I k').j
      (𝔸(ULift.{u} (Fin n); (deformationModel Y I k').total) ↘
        (deformationModel Y I k').total)) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst _ _)
  have : QuasiSeparatedSpace ↥(pullback (deformationModel Y I k').j
      (𝔸(ULift.{u} (Fin n); (deformationModel Y I k').total) ↘
        (deformationModel Y I k').total)) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst _ _)
  have hℓk : IsUnit (ℓ : k) := by
    refine IsUnit.mk0 _ fun h ↦ (Fact.out : ringChar k ≠ ℓ) ?_
    exact (Nat.prime_dvd_prime_iff_eq (Fact.out : (ringChar k).Prime) Fact.out).1
      ((ringChar.spec k ℓ).1 h)
  have hℓ : IsUnit (ℓ : Γ((deformationModel Y I k').total, ⊤)) := by
    simpa using (hℓk.map (ΓSpecIso (.of k)).inv.hom).map
      (deformationTotalToBase Y I k' ≫ Y.hom).appTop.hom
  exact isIso_baseChangeMap_app_padicIntegers_of_smooth ℓ E.1
    (𝔸(ULift.{u} (Fin n); (deformationModel Y I k').total) ↘ (deformationModel Y I k').total)
    (IsPullback.of_hasPullback (deformationModel Y I k').j _) hℓ _
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ _ K₀ hK₀)

end AlgebraicGeometry.ProEtale.CondensedRing
