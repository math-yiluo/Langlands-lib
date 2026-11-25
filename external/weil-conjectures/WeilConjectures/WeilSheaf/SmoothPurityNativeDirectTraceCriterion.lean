/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityCondensedCarrier
public import WeilConjectures.WeilSheaf.SmoothPurityCondensedTraceCriterion

/-!
# A native direct-image trace criterion in condensed coordinates

The free Weil resolution proves universality in the condensed category. Full
faithfulness of the native comparison then proves invertibility of the native
adjoint of the trace.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.WeilComplex

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X Y : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]

/-- Direct image of native Weil complexes commutes with the condensed equivalence. -/
noncomputable def directTraceCondensedComparison :
    derivedLowerStar (k₀ := k₀) (l := l) f ⋙ (objectProperty k₀ l Y).ι ⋙
        (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l Y).functor ≅
      (objectProperty k₀ l X).ι ⋙ (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor ⋙
        (CondensedRing.geometricFiberMapWeilLowerStar (Profinite.padicAlgClRingObj l)
          f (comp_over f _)).rightDerivedFunctor :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (ProEtaleWeilSheaf.rightDerivedLowerStarCompToCondensedIso k₀ l f)

/-- The adjunct of a native direct-image trace is invertible when its condensed
carrier is universal on the geometric shifts of every source. -/
theorem isIso_homEquiv_of_condensed_direct_trace
    {J : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l X}
    (adj : derivedLowerStar (k₀ := k₀) (l := l) f ⊣ J)
    {P : WeilComplex k₀ l X} {N : WeilComplex k₀ l Y}
    (ε : (derivedLowerStar (k₀ := k₀) (l := l) f).obj P ⟶ N)
    (δ : (CondensedRing.geometricFiberMapWeilLowerStar (Profinite.padicAlgClRingObj l)
        f (comp_over f _)).rightDerivedFunctor.obj
          ((ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.obj P.obj) ⟶
      (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l Y).functor.obj N.obj)
    (hε : (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l Y).functor.map ε.hom =
      (directTraceCondensedComparison f).hom.app P ≫ δ)
    (h : ∀ (K : WeilComplex k₀ l X) (n : ℤ), Function.Bijective fun φ :
      (shiftFunctor _ n).obj ((Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.obj
        ((ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.obj K.obj)) ⟶
      (Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.obj
        ((ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.obj P.obj) ↦
        (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
          (Scheme.Hom.geometricFiberMap f (comp_over f _))).rightDerivedFunctor.map φ ≫
        (Endofunctor.IsoAlgebra.derivedForgetCommIso
          (CondensedRing.lowerStarGeometricFiberMapCompFrobeniusIso
            (Profinite.padicAlgClRingObj l) f (comp_over f _))).inv.app
          ((ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.obj P.obj) ≫
        (Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.map δ) :
    IsIso (adj.homEquiv P N ε) := by
  have := (objectProperty k₀ l X).fullyFaithfulι.full
  have := (objectProperty k₀ l Y).fullyFaithfulι.full
  have := (objectProperty k₀ l X).fullyFaithfulι.faithful
  have := (objectProperty k₀ l Y).fullyFaithfulι.faithful
  apply Adjunction.isIso_homEquiv_of_fullyFaithful_trace adj
    ((objectProperty k₀ l X).ι ⋙ (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor)
    ((objectProperty k₀ l Y).ι ⋙ (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l Y).functor)
    _ (directTraceCondensedComparison f) ε δ hε
  intro K
  exact Endofunctor.IsoAlgebra.bijective_map_comp_rightDerived_of_bounded
    (CondensedRing.lowerStarGeometricFiberMapCompFrobeniusIso
      (Profinite.padicAlgClRingObj l) f (comp_over f _))
    (CondensedRing.condensed_trace_preservesCoproduct (Profinite.padicAlgClRingObj l)
      (Scheme.Hom.geometricFiberMap f (comp_over f _))) δ _
    (boundedConstructible_condensedCarrier K).1 (h K)

end AlgebraicGeometry.WeilComplex
