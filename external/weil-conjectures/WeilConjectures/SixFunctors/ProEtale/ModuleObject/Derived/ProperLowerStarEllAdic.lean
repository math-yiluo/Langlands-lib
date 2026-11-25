/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructibleEllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarCoproducts
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdicBound
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarHeart

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicProperConstructibleCohomology
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicProperBoundedBelowCoproducts
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicProperHeartUniformBound

/-!
# The proper direct image for the `ℓ`-adic coefficient rings: the inputs

Let `ℓ` be a prime, `k` a field in which `ℓ` is invertible, and `p : Z ⟶ Y` a proper morphism to
a noetherian `k`-scheme. For the `ℓ`-adic condensed coefficient rings `Λ = E, 𝒪_E, ℚ̄_ℓ`, the
properties of the derived direct image `Rp_*` on module objects over `Λ` used for the
compact-support direct image on `Loc(Dᵇc)` (blueprint
`proposition-construction-independence-rf-shriek`) are:

* `Rp_*` maps `Dᵇc(Z)⟦Λ⟧` into `Dᵇc(Y)⟦Λ⟧` (blueprint
`proposition-proper-direct-image-constructible-complexes`):
  `boundedConstructible_rightDerivedLowerStar_obj_of_isProper_continuousMapRingObj`,
  `boundedConstructible_rightDerivedLowerStar_obj_of_isProper_padicIntegersRingObj`,
  `boundedConstructible_rightDerivedLowerStar_obj_of_isProper_padicAlgClRingObj`;
* for `Y` separated of finite type over `k`, `Rp_*` has finite amplitude on the
  ind-constructible heart and commutes with direct sums there
  (`AlgebraicGeometry.ProEtale.CondensedRing.ProperLowerStarHeartHypotheses`, blueprints
  `lemma-uniform-bound-proper-direct-image` for `E` and `ℚ̄_ℓ`,
  `proposition-compactness-proper-direct-image--2` (1) for `𝒪_E`):
  `properLowerStarHeartHypotheses_continuousMapRingObj`,
  `properLowerStarHeartHypotheses_padicIntegersRingObj`,
  `properLowerStarHeartHypotheses_padicAlgClRingObj`.

From the latter, the restriction of `Rp_*` to `Loc(Dᵇc(Z)⟦Λ⟧)` preserves direct sums
(`AlgebraicGeometry.ProEtale.CondensedRing.ProperLowerStarHeartHypotheses.preservesColimitsOfShape`,
blueprint `proposition-compactness-proper-direct-image--2` (2), (3), proved by dévissage and left
completeness).

The finiteness of `Rp_*` on `Dᵇc` is reduced to residue field coefficients
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdicFiniteness`):
over a noetherian base this uses the finiteness theorem for proper morphisms with torsion
coefficients over a noetherian base
(`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_isProper_of_isNoetherian`),
and over a base of finite type over `k` the proved finite type case
(`boundedConstructible_rightDerivedLowerStar_of_isProper_*_of_finiteType`). The heart hypotheses
follow from the ind-constructible heart (`isIndConstructibleHeart_*`), the continuity of `Rp_*`
(`properLowerStarHeartHypotheses_of_isIndConstructibleHeart`) and a uniform bound on
constructible sheaves
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdicBound`); the
ind-constructible heart is stated for separated `k`-schemes of finite type (the setting of the
blueprint), hence the finite type hypotheses on `Y`.
-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]

/-- `Rp_*` preserves `Dᵇc` once it has a uniform bound on the ind-constructible heart and
constructible cohomology on `Dᵇc` (both supplied per coefficient ring). -/
private theorem boundedConstructible_proper_of_bound
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (hbound : ∃ d : ℤ, ∀ M, constructibleCoproductClosure Λ Z M →
      (R((p)_*⟦Λ⟧).obj ((DerivedCategory.singleFunctor _ 0).obj M)).IsLE d)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) (hK : boundedConstructible _ K)
    (hcoh : ∀ q : ℤ, IsConstructibleModuleObject (condensedRingObj Λ Y)
      ((DerivedCategory.homologyFunctor _ q).obj (R((p)_*⟦Λ⟧).obj K))) :
    boundedConstructible _ (R((p)_*⟦Λ⟧).obj K) := by
  obtain ⟨d, hd⟩ := hbound
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hK.1
  have : K.IsGE a := ha
  have : K.IsLE b := hb
  have hP : DerivedCategory.homologyProperty (constructibleCoproductClosure Λ Z) K :=
    fun n ↦ ObjectProperty.le_weakSerreCoproductClosure _ _ (hK.2 n)
  have hle := DerivedCategory.isLE_obj_of_isLE_of_homologyProperty
    R((p)_*⟦Λ⟧) d (constructibleCoproductClosure Λ Z) hd K hK.1 hP b
  have hge := Functor.isGE_rightDerivedFunctor_obj ((p)_*⟦Λ⟧) K a
  exact ⟨⟨⟨a, hge⟩, ⟨b + d, hle⟩⟩, hcoh⟩

/-- The proper heart hypotheses for `Rp_*`, given the uniform heart bound (supplied per
coefficient ring). -/
private theorem properHeart_of_bound
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) [IsProper p]
    (hbound : ∃ d : ℤ, ∀ M, constructibleCoproductClosure Λ Z M →
      (R((p)_*⟦Λ⟧).obj ((DerivedCategory.singleFunctor _ 0).obj M)).IsLE d) :
    ProperLowerStarHeartHypotheses Λ p := by
  refine ⟨hbound, ?_⟩
  intro J N _
  have : PreservesColimit
      (Discrete.functor (fun j ↦ (DerivedCategory.singleFunctor _ 0).obj (N j)))
      R((p)_*⟦Λ⟧) :=
    condensed_boundedBelow_preservesCoproduct Λ p J 0 _ (fun _ ↦ inferInstance)
  infer_instance

/-! ### The coefficient ring `E` -/

/-- Blueprint `proposition-proper-direct-image-constructible-complexes`
(`proposition-proper-direct-image-constructible-complexes` (1)): for the coefficient ring `E` of a
finite extension `E` of `ℚ_ℓ` and a proper morphism `p : Z ⟶ Y` to a noetherian `k`-scheme, `Rp_*`
maps `Dᵇc(Z)⟦E⟧` into `Dᵇc(Y)⟦E⟧`. -/
theorem boundedConstructible_rightDerivedLowerStar_obj_of_isProper_continuousMapRingObj
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    {Z Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [IsNoetherian Y] (p : Z ⟶ Y) [IsProper p]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E) Z)))
    (hK : boundedConstructible _ K) :
    boundedConstructible _ (R((p)_*⟦Profinite.continuousMapRingObj.{u} E⟧).obj K) :=
  boundedConstructible_rightDerivedLowerStar_continuousMapRingObj_of_residueField ℓ p E
    (residueFieldFiniteness_of_isNoetherian ℓ p aY) K hK

/-- Blueprint `lemma-uniform-bound-proper-direct-image` (`lemma-uniform-bound-proper-direct-image`):
for the coefficient ring `E` of a finite extension `E` of `ℚ_ℓ` and a proper morphism `p : Z ⟶ Y` to
a separated `k`-scheme of finite type, `Rp_*` sends ind-constructible sheaves into degrees `≤ 2d`
(`d` bounding the dimensions of the fibres) and commutes with direct sums of them. -/
theorem properLowerStarHeartHypotheses_continuousMapRingObj (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {Z Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (p : Z ⟶ Y) [IsProper p] :
    ProperLowerStarHeartHypotheses (Profinite.continuousMapRingObj.{u} E) p := by
  obtain ⟨d, hd⟩ := exists_isLE_rightDerivedLowerStar_singleFunctor_continuousMapRingObj ℓ aY p
  obtain ⟨E', e, _⟩ := Profinite.exists_continuousMapRingObj_iso.{u} ℓ E
  have : PreservesFiniteLimits
      (tensorLeft (condensedRingObj (Profinite.continuousMapRingObj.{u} E) Z)) :=
    preservesFiniteLimits_of_natIso
      ((curriedTensor _).mapIso ((upperStarFromPoint Z).mapIso e.symm))
  exact properLowerStarHeartHypotheses_of_isIndConstructibleHeart _ p
    (isIndConstructibleHeart_continuousMapRingObj ℓ E (p ≫ aY)) _
    (isLE_rightDerivedLowerStar_singleFunctor_of_iso e p _ (hd E'))

/-! ### The coefficient ring `𝒪_E` -/

/-- Blueprint `proposition-proper-direct-image-constructible-complexes`
(`proposition-proper-direct-image-constructible-complexes` (1)): for the coefficient ring `𝒪_E` of a
finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and a proper morphism `p : Z ⟶ Y` to a noetherian `k`-scheme,
`Rp_*` maps `Dᵇc(Z)⟦𝒪_E⟧` into `Dᵇc(Y)⟦𝒪_E⟧`. -/
theorem boundedConstructible_rightDerivedLowerStar_obj_of_isProper_padicIntegersRingObj
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] {Z Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [IsNoetherian Y] (p : Z ⟶ Y) [IsProper p]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) Z)))
    (hK : boundedConstructible _ K) :
    boundedConstructible _ (R((p)_*⟦Profinite.padicIntegersRingObj.{u} ℓ E⟧).obj K) :=
  boundedConstructible_rightDerivedLowerStar_padicIntegersRingObj_of_residueField ℓ p E
    (residueFieldFiniteness_of_isNoetherian ℓ p aY) K hK

/-- Blueprint `proposition-compactness-proper-direct-image--2` (1): for the coefficient ring `𝒪_E`
of a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and a proper morphism `p : Z ⟶ Y` to a separated
`k`-scheme of finite type, `Rp_*` sends ind-constructible sheaves into degrees `≤ 2d` (`d`
bounding the dimensions of the fibres) and commutes with direct sums of them. -/
theorem properLowerStarHeartHypotheses_padicIntegersRingObj (E : Type) [Field E]
    [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] {Z Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY] (p : Z ⟶ Y) [IsProper p] :
    ProperLowerStarHeartHypotheses (Profinite.padicIntegersRingObj.{u} ℓ E) p := by
  obtain ⟨d, hd⟩ := exists_isLE_rightDerivedLowerStar_singleFunctor_padicIntegers ℓ aY p
  obtain ⟨E', e, _⟩ := Profinite.exists_padicIntegersRingObj_iso.{u} ℓ E
  have : PreservesFiniteLimits
      (tensorLeft (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) Z)) :=
    preservesFiniteLimits_of_natIso
      ((curriedTensor _).mapIso ((upperStarFromPoint Z).mapIso e.symm))
  exact properLowerStarHeartHypotheses_of_isIndConstructibleHeart _ p
    (isIndConstructibleHeart_padicIntegersRingObj ℓ E (p ≫ aY)) _
    (isLE_rightDerivedLowerStar_singleFunctor_of_iso e p _ (hd E'))

/-! ### The coefficient ring `ℚ̄_ℓ` -/

/-- Blueprint `proposition-proper-direct-image-constructible-complexes`: for the coefficient ring
`ℚ̄_ℓ` and a proper morphism `p : Z ⟶ Y` to a noetherian `k`-scheme, `Rp_*` maps `Dᵇc(Z)⟦ℚ̄_ℓ⟧` into
`Dᵇc(Y)⟦ℚ̄_ℓ⟧`. -/
theorem boundedConstructible_rightDerivedLowerStar_obj_of_isProper_padicAlgClRingObj
    {Z Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [IsNoetherian Y] (p : Z ⟶ Y) [IsProper p]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) Z)))
    (hK : boundedConstructible _ K) :
    boundedConstructible _ (R((p)_*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧).obj K) :=
  boundedConstructible_rightDerivedLowerStar_padicAlgClRingObj_of_residueField ℓ p
    (residueFieldFiniteness_of_isNoetherian ℓ p aY) K hK

/-- Blueprint `lemma-uniform-bound-proper-direct-image` (`lemma-uniform-bound-proper-direct-image`):
for the coefficient ring `ℚ̄_ℓ` and a proper morphism `p : Z ⟶ Y` to a separated `k`-scheme of
finite type, `Rp_*` sends ind-constructible sheaves into degrees `≤ 2d` (`d` bounding the dimensions
of the fibres) and commutes with direct sums of them. -/
theorem properLowerStarHeartHypotheses_padicAlgClRingObj {Z Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (p : Z ⟶ Y) [IsProper p] :
    ProperLowerStarHeartHypotheses (Profinite.padicAlgClRingObj.{u} ℓ) p := by
  obtain ⟨d, hd⟩ := exists_isLE_rightDerivedLowerStar_singleFunctor_padicAlgClRingObj ℓ aY p
  exact properLowerStarHeartHypotheses_of_isIndConstructibleHeart _ p
    (isIndConstructibleHeart_padicAlgClRingObj ℓ (p ≫ aY)) d hd

end AlgebraicGeometry.ProEtale.CondensedRing
