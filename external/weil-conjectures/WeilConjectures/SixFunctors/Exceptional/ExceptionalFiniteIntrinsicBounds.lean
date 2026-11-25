/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Exceptional.ExceptionalFiniteRestrictionAdjunction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekPreservation
import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions
import all WeilConjectures.AlgebraicGeometry.SfAffineChartPresentation.PurityAffineChartBounds
import all WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated

/-! # Uniform intrinsic bounds for the specified exceptional functor

Source: blueprint theorem-f-shriek-finite-coefficients--1
(blueprint: lem-sf-finite-intrinsic-exceptional-bounds).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem bounds_bounded_iff_support
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C) :
    DerivedCategory.TStructure.t.bounded K ↔
      Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor C i).obj K)} := by
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    apply (Set.finite_Icc a b).subset
    intro i hi
    exact ⟨le_of_not_gt (fun h ↦ hi ((DerivedCategory.isGE_iff K a).mp ha i h)),
      le_of_not_gt (fun h ↦ hi ((DerivedCategory.isLE_iff K b).mp hb i h))⟩
  · intro h
    obtain ⟨a, ha⟩ := h.bddBelow
    obtain ⟨b, hb⟩ := h.bddAbove
    refine ⟨⟨a, (DerivedCategory.isGE_iff K a).mpr (fun i hi ↦ ?_)⟩,
      ⟨b, (DerivedCategory.isLE_iff K b).mpr (fun i hi ↦ ?_)⟩⟩
    · by_contra hz
      exact (not_lt_of_ge (ha hz)) hi
    · by_contra hz
      exact (not_lt_of_ge (hb hz)) hi

private theorem bounds_constructible_iff
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    [Finite (Padic.coefficientExtensionRing l E n)]
    (T : Scheme.{u})
    (K : DerivedCategory (Sheaf (ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))))) :
    intrinsicFiniteTorsionConstructible l E n hn T
        ((sfIntrinsicDerivedEquivalence T (Padic.coefficientExtensionRing l E n)).functor.obj K) ↔
      ProEtale.DerivedCategory.boundedConstructible
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) T K := by
  let A := Padic.coefficientExtensionRing l E n
  let : Finite A := Padic.finite_coefficientExtensionRing l E n hn
  let F := ProEtale.finiteCoefficientIntrinsicRealization T A
  have : F.IsEquivalence := (ProEtale.finiteCoefficientIntrinsicRealization_exact T A).1
  have hc (i : ℤ) :
      IsConstructibleProEtaleModuleSheaf T A
        ((DerivedCategory.homologyFunctor _ i).obj (F.mapDerivedCategory.obj K)) ↔
      ProEtale.IsConstructible (ULift.{u + 1, u} A)
        ((DerivedCategory.homologyFunctor _ i).obj K) := by
    let e := (F.mapDerivedCategoryHomologyFunctorIso i).app K
    exact ⟨fun h ↦ (intrinsicRealization_constructible_iff T A _).mp
      (intrinsicConstructible_of_iso T A e.symm h),
      fun h ↦ intrinsicConstructible_of_iso T A e
        ((intrinsicRealization_constructible_iff T A _).mpr h)⟩
  constructor
  · rintro ⟨hb, hconstructible⟩
    have hbk : DerivedCategory.TStructure.t.bounded K :=
      F.bounded_of_bounded_mapDerivedCategory_obj ((bounds_bounded_iff_support _).mpr hb)
    exact ProEtale.DerivedCategory.boundedConstructible_of_homology _ hbk
      (fun i ↦ ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj _
        ((hc i).mp (hconstructible i)))
  · intro h
    have hi := ProEtale.DerivedCategory.boundedConstructible_le_boundedConstructibleIntrinsic
      _ h
    exact ⟨(bounds_bounded_iff_support _).mp (F.bounded_mapDerivedCategory_obj hi.1),
      fun i ↦ (hc i).mpr (hi.2 i)⟩

private theorem bounds_interval_iff
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    [Finite (Padic.coefficientExtensionRing l E n)]
    (T : Scheme.{u}) (a b : ℤ)
    (K : DerivedCategory (Sheaf (ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))))) :
    constructibleInterval l E n hn T a b
        ((sfIntrinsicDerivedEquivalence T (Padic.coefficientExtensionRing l E n)).functor.obj K) ↔
      ProEtale.DerivedCategory.constructibleIn
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) T a b K := by
  let A := Padic.coefficientExtensionRing l E n
  let : Finite A := Padic.finite_coefficientExtensionRing l E n hn
  let F := ProEtale.finiteCoefficientIntrinsicRealization T A
  have : F.IsEquivalence := (ProEtale.finiteCoefficientIntrinsicRealization_exact T A).1
  have hs (P : proEtaleDerivedCategory T A) :
      proEtaleCohomologicalSupport P ⊆ Set.Icc a b ↔
        DerivedCategory.homologyConcentratedIn a b P := by
    constructor
    · intro h
      constructor
      · apply (DerivedCategory.isGE_iff P a).mpr
        intro i hi
        by_contra hz
        exact (not_lt_of_ge (h hz).1) hi
      · apply (DerivedCategory.isLE_iff P b).mpr
        intro i hi
        by_contra hz
        exact (not_lt_of_ge (h hz).2) hi
    · intro h i hi
      exact ⟨le_of_not_gt (fun h' ↦ hi ((DerivedCategory.isGE_iff P a).mp h.1 i h')),
        le_of_not_gt (fun h' ↦ hi ((DerivedCategory.isLE_iff P b).mp h.2 i h'))⟩
  change (_ ∧ _) ↔ (_ ∧ _)
  rw [bounds_constructible_iff l E n hn T K]
  dsimp only
  rw [hs]
  exact and_congr_right fun _ ↦
    ⟨F.homologyConcentratedIn_of_homologyConcentratedIn_mapDerivedCategory_obj,
      F.homologyConcentratedIn_mapDerivedCategory_obj⟩

private theorem bounds_tor_iso
    (T : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L) (a b : ℤ)
    (h : HasProEtaleTorAmplitude T A K a b) : HasProEtaleTorAmplitude T A L a b := by
  refine ⟨h.1, ?_⟩
  intro P Q he f hf hQ M i hi
  exact h.2 P Q (he.map (fun z ↦ z ≪≫ e.symm)) f hf hQ M i hi

/-- Uniform intrinsic exceptional bounds for the specified ambient right functor.
Source: blueprint theorem-f-shriek-finite-coefficients--1, exceptional construction step 3
(blueprint: lem-sf-finite-intrinsic-exceptional-bounds).

Proof: Choose finite affine target charts, affine source charts over them, and their
closed affine-space presentations once for f. Discard empty source charts. Apply
sf_purity_affine_chart_bounds to this presentation at each positive coefficient
stage. The chart maximum D and target dimension e are geometric, independent of
E and n. For nonempty source the resulting endpoints are a-2D and b+2e+1;
for empty source both constants are zero. The purity functor is defined using a
chosen compactification. Uniqueness of the ordinary etale right adjoint identifies
it with the right adjoint for the specified c, compatibly with comparison functors.
Transport the bounds through that isomorphism. The canonical exact coefficient
realization identifies fixed-module constructibility and Tor amplitude with the
intrinsic predicates, including the same interval endpoints. The intrinsic output
is therefore bounded constructible and has finite Tor amplitude. This gives all
three assertions. An inverted input cohomological interval forces a zero object;
additivity sends it to zero, so the same support assertion holds without imposing
a <= b. Positive Tor intervals already include a <= b by definition. -/
theorem sfFiniteOperations_intrinsicExceptionalBounds (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) :
    ∃ cMinus cPlus : ℤ, ∀ (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l)
      (n : ℕ+),
      (∀ L : finiteTorConstructibleCategory l E.carrier n n.pos Y,
        finiteTorConstructible l E.carrier n n.pos X
          ((sfFiniteOperationsIntrinsicRight l E n c).obj L.obj)) ∧
      (∀ (L : finiteTorConstructibleCategory l E.carrier n n.pos Y) (a b : ℤ),
        constructibleInterval l E.carrier n n.pos Y a b L.obj →
        constructibleInterval l E.carrier n n.pos X (a + cMinus) (b + cPlus)
          ((sfFiniteOperationsIntrinsicRight l E n c).obj L.obj)) ∧
      (∀ (L : finiteTorConstructibleCategory l E.carrier n n.pos Y) (a b : ℤ),
        HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E.carrier n) L.obj a b →
        HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E.carrier n)
          ((sfFiniteOperationsIntrinsicRight l E n c).obj L.obj) (a + cMinus) (b + cPlus))
    := by
  classical
  let : HasCompactification f := c.hasCompactification
  obtain ⟨dY, hdY⟩ := exists_topologicalKrullDim_le (Y ↘ Spec (.of D.k))
  obtain ⟨dX, hbounds⟩ :=
    ProEtale.exists_preservationClauses (Y ↘ Spec (.of D.k)) f
  refine ⟨-2 * (dX : ℤ), 2 * (dY : ℤ) + 1, ?_⟩
  intro E n
  let A := Padic.coefficientExtensionRing l E.carrier n
  let Λ := ULift.{u + 1, u} A
  let : HasInvertibleExponent Λ (Spec (.of D.k)) :=
    coefficient_invertible D l _hl E.carrier n (Spec (.of D.k)) (𝟙 _)
  let eX := sfIntrinsicDerivedEquivalence X A
  let eY := sfIntrinsicDerivedEquivalence Y A
  let G := ProEtale.rightDerivedUpperShriek Λ f
  let B := ProEtale.sfFiniteExceptionalAt Λ c
  let e : G ≅ B :=
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft _
        ((Etale.rightDerivedUpperShriekAdjunctionOfCompactification Λ c).rightAdjointUniq
          (Adjunction.ofIsLeftAdjoint
            (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c)))) _
  have hclosed (T : Scheme.{u}) :
      (intrinsicFiniteTorsionConstructible l E.carrier n n.pos T).IsClosedUnderIsomorphisms :=
    (proEtale_bounded_constructible_isTriangulated T A).1
  have hc (L : finiteTorConstructibleCategory l E.carrier n n.pos Y) :
      ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
        (eY.inverse.obj L.obj) := by
    let := hclosed Y
    exact (bounds_constructible_iff l E.carrier n n.pos Y _).mp
      (ObjectProperty.prop_of_iso _ (eY.counitIso.app L.obj).symm L.property.1)
  obtain ⟨hinterval, htor⟩ := hbounds Λ dY hdY
  have torBound (L : finiteTorConstructibleCategory l E.carrier n n.pos Y)
      (a b : ℤ) (ht : HasProEtaleTorAmplitude Y A L.obj a b) :
      intrinsicFiniteTorsionConstructible l E.carrier n n.pos X
          ((sfFiniteOperationsIntrinsicRight l E n c).obj L.obj) ∧
        HasProEtaleTorAmplitude X A
          ((sfFiniteOperationsIntrinsicRight l E n c).obj L.obj)
          (a - 2 * (dX : ℤ)) (b + 2 * (dY : ℤ) + 1) := by
    have ht' := (ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
      A Y a b ht.1 (eY.inverse.obj L.obj)).mp
        (bounds_tor_iso Y A (eY.counitIso.app L.obj).symm a b ht)
    obtain ⟨hc', ht'⟩ := htor a b (eY.inverse.obj L.obj) (hc L) ht'
    have hcB := (ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} Λ) X).prop_of_iso (e.app _) hc'
    have htB := (ProEtale.DerivedCategory.torAmplitudeIn
      (ModuleCat.{u + 1} Λ) X _ _).prop_of_iso (e.app _) ht'
    exact ⟨(bounds_constructible_iff l E.carrier n n.pos X _).mpr hcB,
      (ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
        A X _ _ (by have := ht.1; omega) _).mpr htB⟩
  refine ⟨?_, ?_, ?_⟩
  · intro L
    obtain ⟨a, b, ht⟩ := L.property.2
    obtain ⟨hc', ht'⟩ := torBound L a b ht
    exact ⟨hc', _, _, ht'⟩
  · intro L a b hL
    have hLin : constructibleInterval l E.carrier n n.pos Y a b
        (eY.functor.obj (eY.inverse.obj L.obj)) := by
      let := hclosed Y
      refine ⟨ObjectProperty.prop_of_iso _ (eY.counitIso.app L.obj).symm hL.1, ?_⟩
      intro i hi
      apply hL.2
      intro hz
      exact hi (((DerivedCategory.homologyFunctor _ i).mapIso
        (eY.counitIso.app L.obj)).isZero_iff.mpr hz)
    have hfixed := (bounds_interval_iff l E.carrier n n.pos Y a b _).mp hLin
    have hout := hinterval a b (eY.inverse.obj L.obj) hfixed
    have houtB : ProEtale.DerivedCategory.constructibleIn
        (ModuleCat.{u + 1} Λ) X _ _ (B.obj (eY.inverse.obj L.obj)) :=
      ⟨(ProEtale.DerivedCategory.boundedConstructible
          (ModuleCat.{u + 1} Λ) X).prop_of_iso (e.app _) hout.1,
        ObjectProperty.prop_of_iso _ (e.app _) hout.2⟩
    change constructibleInterval l E.carrier n n.pos X _ _
      (eX.functor.obj (B.obj (eY.inverse.obj L.obj)))
    simpa only [sub_eq_add_neg, neg_mul, add_assoc] using
      (bounds_interval_iff l E.carrier n n.pos X _ _ _).mpr houtB
  · intro L a b ht
    simpa only [sub_eq_add_neg, neg_mul, add_assoc] using (torBound L a b ht).2

end WeilConjectures
