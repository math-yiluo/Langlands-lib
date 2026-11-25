/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.UpperShriekGeometric
public import WeilConjectures.CategoryTheory.DerivedCategory.FreeComparisonMapDerivedCategory

/-!
# Constructibility of the condensed carrier

The exact equivalence of native and condensed Weil sheaves intertwines the two
forgetful functors. Thus the carrier of a native Weil complex is bounded
constructible also in the condensed model.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.WeilComplex

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))]

/-- Forgetting the condensed Weil structure agrees with passing the native
geometric carrier through the coefficient equivalence. -/
noncomputable def condensedCarrierIso (K : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) :
    (Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.obj
      ((ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.obj K) ≅
    (adicSheafDerivedEquivCondensedMod l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.obj
      ((Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.obj K) :=
  (Functor.mapDerivedCategoryCompForgetIso
    (Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso
      (ProEtaleWeilSheaf.condensedFrobeniusComparison k₀ l X))).app K

variable [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- Bounded constructibility is detected on the condensed geometric carrier. -/
theorem objectProperty_iff_boundedConstructible_condensedCarrier
    (K : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) :
    objectProperty k₀ l X K ↔
    boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      ((Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.obj
        ((ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.obj K)) := by
  refine (objectProperty_iff K).trans ?_
  let K₀ : DerivedCategory
      (AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
    (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategory.obj K
  have h := boundedConstructibleAdic_iff_boundedConstructible l k₀ (AlgebraicClosure k₀)
    (Over.mk (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure)
    K₀
  refine h.trans ?_
  exact ⟨(boundedConstructible _).prop_of_iso (condensedCarrierIso K).symm,
    (boundedConstructible _).prop_of_iso (condensedCarrierIso K)⟩

/-- Native bounded constructibility gives bounded constructibility of the
forgotten condensed Weil complex. -/
theorem boundedConstructible_condensedCarrier (K : WeilComplex k₀ l X) :
    boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      ((Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.obj
        ((ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.obj K.obj)) := by
  exact (objectProperty_iff_boundedConstructible_condensedCarrier K.obj).1 K.property

/-- Realize a condensed Weil complex with bounded constructible carrier as a
native Weil complex. -/
noncomputable def nativeOfCondensedCarrier
    (C : DerivedCategory (Endofunctor.IsoAlgebra
      (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)))
    (hC : boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      ((Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.obj C)) :
    WeilComplex k₀ l X :=
  ⟨(ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).inverse.obj C,
    (objectProperty_iff_boundedConstructible_condensedCarrier _).2
      ((boundedConstructible _).prop_of_iso
        ((Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.mapIso
          ((ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).counitIso.app C)).symm hC)⟩

/-- The realization has the prescribed condensed Weil complex, including its
Frobenius datum. -/
noncomputable def nativeOfCondensedCarrierIso
    (C : DerivedCategory (Endofunctor.IsoAlgebra
      (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)))
    (hC : boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      ((Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.obj C)) :
    (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.obj
      (nativeOfCondensedCarrier C hC).obj ≅ C :=
  (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).counitIso.app C

end AlgebraicGeometry.WeilComplex
