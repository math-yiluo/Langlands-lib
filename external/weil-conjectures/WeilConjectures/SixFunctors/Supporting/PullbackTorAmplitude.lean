/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantExact
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorInterval
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility

/-!
# Pullback preserves finite Tor amplitude

Source: Weil conjectures blueprint, sec-six-functors/sk-prop-sf-rf-shriek-preservation,
order 2064 (blueprint: proposition-six-operations-dctf--1).
The finite pullback below specializes the recorded ringed-site operation along the
canonical constant-section coefficient isomorphism. It introduces no chosen ring map.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The finite-level derived pullback on the recorded constant-ring module category.
The coefficient comparison is the canonical inverse-image map, whose invertibility
is the recorded constant-coefficient theorem. Exact module pullback descends termwise.
Source: blueprint order 2064, finite-level operation from order 1467;
Stacks Tags 03D2 and 0735 (blueprint: proposition-six-operations-dctf--1). -/
noncomputable def sfFiniteDerivedPullback
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n) ⥤
      proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n) :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  letI : TopologicalSpace (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) := ⊥
  letI : DiscreteTopology (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) :=
    discreteTopology_bot _
  letI := ProEtale.finiteCoefficientCommRingMap_isIso f
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
  proEtaleRingDerivedPullback f
    (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E n))
    (proEtaleConstantRing X (Padic.coefficientExtensionRing l E n))
    (asIso (proEtaleCoefficientInverseImageMap f (Padic.coefficientExtensionRing l E n)))

private theorem torAmplitude_of_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L) (a b : ℤ)
    (h : HasProEtaleTorAmplitude T A K a b) :
    HasProEtaleTorAmplitude T A L a b := by
  refine ⟨h.1, ?_⟩
  intro C P hC f hf hP M i hi
  obtain ⟨eC⟩ := hC
  exact h.2 C P ⟨eC ≪≫ e.symm⟩ f hf hP M i hi

private theorem etaleBounded_iff (T : Scheme.{u}) (A : Type (u + 1))
    [CommRing A] [Finite A] (K : Etale.DerivedCategoryModule A T) :
    Etale.DerivedCategory.isBoundedConstructible A T K ↔
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T K := by
  constructor
  · rintro ⟨hc, a, b, _, hab⟩
    refine ⟨⟨⟨a, (DerivedCategory.isGE_iff K a).2 (fun i hi ↦ hab i (.inl hi))⟩,
      ⟨b, (DerivedCategory.isLE_iff K b).2 (fun i hi ↦ hab i (.inr hi))⟩⟩, ?_⟩
    intro i
    exact (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc i)
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨?_, min a b, b, min_le_right _ _, ?_⟩
    · intro i
      exact (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc i)
    · intro i hi
      rcases hi with hi | hi
      · exact (DerivedCategory.isGE_iff K a).1 ha i (lt_of_lt_of_le hi (min_le_left _ _))
      · exact (DerivedCategory.isLE_iff K b).1 hb i hi

private noncomputable def intrinsicComparisonPullbackIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A] [Finite A] :
    ProEtale.finiteCoefficientIntrinsicComparison Y A ⋙ proEtaleConstantRingPullback A f ≅
      Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f ⋙
        ProEtale.finiteCoefficientIntrinsicComparison X A :=
  Functor.isoWhiskerLeft _ (openSquarePullbackModel A f) ≪≫
    (Functor.isoWhiskerLeft
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y)
      ((sfIntrinsicModuleEquivalence Y A).funInvIdAssoc
        (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f ⋙
          ProEtale.finiteCoefficientIntrinsicRealization X A))) ≪≫
    Functor.isoWhiskerRight
      (ProEtale.comparisonUpperStarCompUpperStarIso
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)
      (ProEtale.finiteCoefficientIntrinsicRealization X A)

private noncomputable def intrinsicDerivedComparisonPullbackIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A] [Finite A] :
    ProEtale.finiteCoefficientIntrinsicDerivedComparison Y A ⋙
        proEtaleConstantRingDerivedPullback A f ≅
      (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).mapDerivedCategory ⋙
        ProEtale.finiteCoefficientIntrinsicDerivedComparison X A :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (intrinsicComparisonPullbackIso f A) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm

private theorem comparison_tor_iff (T : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A] (a b : ℤ) (hab : a ≤ b)
    (K : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) T)
    (hK : DerivedCategory.TStructure.t.plus K) :
    Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1, u} A) T a b K ↔
      HasProEtaleTorAmplitude T A
        ((ProEtale.finiteCoefficientIntrinsicDerivedComparison T A).obj K) a b := by
  let C := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T
  let R := ProEtale.finiteCoefficientIntrinsicRealization T A
  let e := (Functor.mapDerivedCategoryCompIso C R).app K
  have h := ProEtale.comparison_torAmplitudeIn_iff A T a b hab ⟨K, hK⟩
  exact h.trans ⟨fun h ↦ torAmplitude_of_iso T A e a b h,
    fun h ↦ torAmplitude_of_iso T A e.symm a b h⟩

/-- Pullback preserves bounded constructibility and the very same Tor interval.
Source: Weil blueprint, order 2064 (blueprint: proposition-six-operations-dctf--1).
Proof:
1. The coefficient quotient is finite. Apply the intrinsic finite-ring derived
comparison to descend K to a bounded constructible etale complex L. Convert its
finite-value constructibility and cohomological interval to the source library's
bounded-constructibility predicate.
2. Exact etale inverse image preserves bounded constructibility. The canonical
comparison square, followed by the unit-preserving identification of constant-ring
pullback with transported inverse image, identifies the intrinsic comparison of
f^*L with the specified sfFiniteDerivedPullback of K.
3. The comparison Tor-interval equivalence reflects the assumed interval [a,b]
to L. The source library's torAmplitudeIn_leftDerivedUpperStar preserves this
interval: choose a flat model in [a,b], pull it back termwise using preservation
of flat module sheaves, and compute the tensor with each degree-zero sheaf.
Apply the comparison Tor-interval equivalence on X and transport along the
isomorphism of step 2. Its constructibility conclusion also gives the required
finite support of intrinsic homology. -/
theorem sf_pullback_torAmplitude
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n)
    (X Y : Over (Spec (CommRingCat.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (K : proEtaleDerivedCategory Y.left (Padic.coefficientExtensionRing l E n))
    (hK : intrinsicFiniteTorsionConstructible l E n hn Y.left K)
    (a b : ℤ)
    (hTor : HasProEtaleTorAmplitude Y.left (Padic.coefficientExtensionRing l E n) K a b) :
    intrinsicFiniteTorsionConstructible l E n hn X.left
        ((sfFiniteDerivedPullback l E n hn f.left).obj K) ∧
      HasProEtaleTorAmplitude X.left (Padic.coefficientExtensionRing l E n)
        ((sfFiniteDerivedPullback l E n hn f.left).obj K) a b := by
  classical
  let A := Padic.coefficientExtensionRing l E n
  have : Finite A := Padic.finite_coefficientExtensionRing l E n hn
  let B := ULift.{u + 1, u} A
  let F := proEtaleConstantRingDerivedPullback A f.left
  change intrinsicFiniteTorsionConstructible l E n hn X.left (F.obj K) ∧
    HasProEtaleTorAmplitude X.left A (F.obj K) a b
  obtain ⟨c, hc⟩ := hK.1.bddBelow
  obtain ⟨d, hd⟩ := hK.1.bddAbove
  have hvan : ∀ i : ℤ, (i < min c d ∨ d < i) →
      CategoryTheory.Limits.IsZero ((DerivedCategory.homologyFunctor _ i).obj K) := by
    intro i hi
    by_contra hz
    rcases hi with hi | hi
    · exact (not_lt_of_ge (hc hz)) (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (not_lt_of_ge (hd hz)) hi
  obtain ⟨L, ⟨eL⟩⟩ := ((finiteRing_constructibleDerived_origin Y.left A).2.2.1 K).mpr
    ⟨hK.2, min c d, d, min_le_right _ _, hvan⟩
  have hbc := (etaleBounded_iff Y.left B L.obj).mp L.property
  let P := (Etale.upperStar (ModuleCat.{u + 1} B) f.left).mapDerivedCategory.obj L.obj
  have hbcP : Etale.DerivedCategory.isBoundedConstructible B X.left P :=
    (etaleBounded_iff X.left B P).mpr (hbc.mapDerivedCategory_upperStar f.left)
  have hplus : DerivedCategory.TStructure.t.plus L.obj := hbc.1.1
  have hplusP : DerivedCategory.TStructure.t.plus P :=
    ((etaleBounded_iff X.left B P).mp hbcP).1.1
  have htL : Etale.DerivedCategory.hasTorAmplitudeIn B Y.left a b L.obj :=
    (comparison_tor_iff Y.left A a b hTor.1 L.obj hplus).mpr
      (torAmplitude_of_iso Y.left A eL.symm a b hTor)
  have htP : Etale.DerivedCategory.hasTorAmplitudeIn B X.left a b P := by
    apply Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr
    exact (Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} B) X.left a b).prop_of_iso
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} B) f.left).app L.obj)
      (Etale.torAmplitudeIn_leftDerivedUpperStar (ModuleCat.{u + 1} B) f.left a b
        (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp htL))
  let eP : (ProEtale.finiteCoefficientIntrinsicDerivedComparison X.left A).obj P ≅
      F.obj K :=
    ((intrinsicDerivedComparisonPullbackIso f.left A).app L.obj).symm ≪≫ F.mapIso eL
  have himage := ((finiteRing_constructibleDerived_origin X.left A).2.2.1 (F.obj K)).mp
    ⟨⟨P, hbcP⟩, ⟨eP⟩⟩
  refine ⟨⟨?_, himage.1⟩, ?_⟩
  · obtain ⟨c', d', _, hv⟩ := himage.2
    apply (Set.finite_Icc c' d').subset
    intro i hi
    exact ⟨le_of_not_gt (fun h ↦ hi (hv i (.inl h))),
      le_of_not_gt (fun h ↦ hi (hv i (.inr h)))⟩
  · exact torAmplitude_of_iso X.left A eP a b
      ((comparison_tor_iff X.left A a b hTor.1 P hplusP).mp htP)

end WeilConjectures
