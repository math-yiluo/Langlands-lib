/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelDerived
public import WeilConjectures.SixFunctors.ProEtale.Adic.BoundedConstructibleCondensedComparison
public import WeilConjectures.WeilSheaf.CondensedModelWeil
public import WeilConjectures.WeilSheaf.ProperLowerStarAdjoint
public import WeilConjectures.WeilSheaf.UpperShriekGeometric

/-!
# The condensed Frobenius preserves bounded constructible complexes

The Frobenius `(Fr_X⁻¹)_*` of the condensed model preserves and reflects bounded constructible
complexes on the geometric fibre `X̄`
(`AlgebraicGeometry.ProEtale.boundedConstructible_lowerStar_frobenius_mapDerivedCategory_obj_iff`):
transported from the `ℓ`-adic model
(`WeilSheaf.boundedConstructibleAdic_frobeniusPullback_mapDerivedCategory_obj_iff`)
along `adicSheafDerivedEquivCondensedMod`, using the comparison of the two Frobenii
`AlgebraicGeometry.ProEtaleWeilSheaf.condensedFrobeniusComparison`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

set_option linter.style.haveILetI false in
/-- **The condensed Frobenius preserves and reflects bounded constructible complexes.** -/
theorem boundedConstructible_lowerStar_frobenius_mapDerivedCategory_obj_iff
    (M : _root_.DerivedCategory (CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).mapDerivedCategory.obj
          M) ↔
      boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) M := by
  set E := adicSheafDerivedEquivCondensedMod l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  haveI : (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).IsEquivalence :=
    (CondensedRing.lowerStarEquivalenceOfIso (Profinite.padicAlgClRingObj l)
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.symm).isEquivalence_functor
  haveI : PreservesFiniteColimits (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv) :=
    inferInstance
  let c := Functor.mapDerivedCategoryCompIsoOfIso
    (ProEtaleWeilSheaf.condensedFrobeniusComparison k₀ l X)
  let K := E.inverse.obj M
  have eM : E.functor.obj K ≅ M := E.counitIso.app M
  have e1 : (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).mapDerivedCategory.obj
        M ≅
      E.functor.obj ((WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategory.obj K) :=
    (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).mapDerivedCategory.mapIso
        eM.symm ≪≫ c.app K
  have hA : ∀ K' : _root_.DerivedCategory
      (AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber),
      ProEtale.DerivedCategory.boundedConstructibleAdic l
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber K' ↔
        boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l)
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) (E.functor.obj K') := fun K' ↦
    boundedConstructibleAdic_iff_boundedConstructible l k₀ (AlgebraicClosure k₀)
      (Over.mk (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure) K'
  exact (ObjectProperty.prop_iff_of_iso _ e1).trans ((hA _).symm.trans
    ((WeilSheaf.boundedConstructibleAdic_frobeniusPullback_mapDerivedCategory_obj_iff K).trans
      ((hA K).trans (ObjectProperty.prop_iff_of_iso _ eM))))

end AlgebraicGeometry.ProEtale
