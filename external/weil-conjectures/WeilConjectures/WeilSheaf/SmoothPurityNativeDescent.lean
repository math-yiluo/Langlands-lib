/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityCondensedCarrier
public import WeilConjectures.WeilSheaf.CondensedModelBaseChange

/-!
# Native descent of finite-base constructible complexes

A constructible complex over the finite field pulls back to a condensed Weil
complex with constructible carrier. The coefficient equivalence realizes this
as a native Weil complex, functorially and with the specified descent datum.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [Finite k]
  {X : Scheme.{u}} (s : X ⟶ Spec (CommRingCat.of k))

/-- The descended pullback of a constructible finite-base complex has a
constructible geometric carrier. -/
theorem boundedConstructible_geometricFiberWeilLowerStar
    (P : Dᵇc(X)⟦Profinite.padicAlgClRingObj l⟧) :
    boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj l) s.geometricFiber)
      ((Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.obj
        ((geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l) s).mapDerivedCategory.obj
          P.obj)) := by
  have h := boundedConstructible_leftDerivedUpperStar_obj_of_scheme
    (Profinite.padicAlgClRingObj l) s.geometricFiberProj P.obj P.property
  have h' := (boundedConstructible _).prop_of_iso
    ((leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj l)
      s.geometricFiberProj).app P.obj) h
  exact (boundedConstructible _).prop_of_iso
    ((Functor.mapDerivedCategoryCompIso
      (geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l) s)
      (Endofunctor.IsoAlgebra.forget _)).symm.app P.obj) h'

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.WeilComplex

open ProEtale
open scoped ProEtale.CondensedRing

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- Descent from the finite base followed by native coefficient realization. -/
noncomputable def finiteBaseNativeDescent :
    Dᵇc(X)⟦Profinite.padicAlgClRingObj l⟧ ⥤ WeilComplex k₀ l X :=
  (objectProperty k₀ l X).lift
    ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l) X)).ι ⋙
      (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀))).mapDerivedCategory ⋙
      (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).inverse)
    (fun P ↦ (nativeOfCondensedCarrier _
      (CondensedRing.boundedConstructible_geometricFiberWeilLowerStar l
        (X ↘ Spec (CommRingCat.of k₀)) P)).property)

/-- The native descent functor realizes the specified condensed descent functor. -/
noncomputable def finiteBaseNativeDescentComparison :
    finiteBaseNativeDescent (k₀ := k₀) (l := l) (X := X) ⋙
        (objectProperty k₀ l X).ι ⋙
        (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor ≅
      (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l) X)).ι ⋙
        (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
          (X ↘ Spec (CommRingCat.of k₀))).mapDerivedCategory :=
  NatIso.ofComponents
    (fun P ↦ (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).counitIso.app
      ((CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀))).mapDerivedCategory.obj P.obj))
    (fun φ ↦ (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).counitIso.hom.naturality
      ((CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀))).mapDerivedCategory.map φ.hom))

end AlgebraicGeometry.WeilComplex
