/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralScalarMates
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated
import Mathlib.Data.Nat.Prime.Infinite

/-! # Endpoint reconstruction for exceptional integral transport

This is the single-endpoint, single-field-stage reconstruction subproblem used by
the core transport reconstruction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients
open CategoryTheory.Limits

private theorem complete_iff (l : ℕ) [Fact l.Prime] (E : FieldStage.{u} l)
    (T : Scheme.{u}) (K : DerivedCategory (scalarReductionSource l E.carrier T)) :
    IsSfDerivedComplete l E.carrier T K ↔
      IntegralOnSlice.IsComplete l E.carrier T none K := by
  constructor
  · intro hK
    obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
    let : Fact p.Prime := ⟨hprime⟩
    let D : FiniteFieldDatum.{0} := {
      p := p, a := 1, q := p, prime := hprime, exponent_pos := le_refl 1,
      cardinality_eq := (pow_one p).symm, k₀ := ZMod p,
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
    have hl : l ≠ D.p := by change l ≠ p; omega
    exact ⟨D, hl, (sfDerivedComplete_iff_legacy l E.carrier T D hl K).mp hK⟩
  · rintro ⟨D, hl, hK⟩
    exact (sfDerivedComplete_iff_legacy l E.carrier T D hl K).mpr hK

private theorem support_iff (T : Scheme.{u}) (A : Type u) [CommRing A]
    (K : proEtaleDerivedCategory T A) (a b : ℤ) :
    proEtaleCohomologicalSupport K ⊆ Set.Icc a b ↔ K.IsGE a ∧ K.IsLE b := by
  classical
  constructor
  · intro h
    constructor
    · apply (DerivedCategory.isGE_iff K a).mpr
      intro i hi
      by_contra hz
      exact (not_le_of_gt hi) (h hz).1
    · apply (DerivedCategory.isLE_iff K b).mpr
      intro i hi
      by_contra hz
      exact (not_le_of_gt hi) (h hz).2
  · rintro ⟨ha, hb⟩ i hi
    exact ⟨le_of_not_gt (fun h ↦ hi ((DerivedCategory.isGE_iff K a).mp ha i h)),
      le_of_not_gt (fun h ↦ hi ((DerivedCategory.isLE_iff K b).mp hb i h))⟩

private theorem tor_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L) (a b : ℤ)
    (h : HasProEtaleTorAmplitude T A K a b) : HasProEtaleTorAmplitude T A L a b := by
  refine ⟨h.1, ?_⟩
  intro N P hN f hf hP M i hi
  exact h.2 N P (hN.map (fun q ↦ q ≪≫ e.symm)) f hf hP M i hi

private theorem fiber_bounds_iso (l : ℕ) [Fact l.Prime] (E : FieldStage.{u} l)
    (T : Scheme.{u}) (n : ℕ)
    {K L : proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E.carrier (n + 1))}
    (e : K ≅ L) (a b c d : ℤ)
    (h : finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos _) T K ∧
      K.IsGE a ∧ K.IsLE b ∧
      HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E.carrier (n + 1))
        K c d) :
    finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos _) T L ∧
      L.IsGE a ∧ L.IsLE b ∧
      HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E.carrier (n + 1))
        L c d := by
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos _) T) :=
    (finite_ctf_isTriangulated l E.carrier (n + 1) (Nat.succ_pos _) T).1
  have : K.IsGE a := h.2.1
  have : K.IsLE b := h.2.2.1
  exact ⟨ObjectProperty.prop_of_iso _ e h.1,
    DerivedCategory.TStructure.t.isGE_of_iso e a,
    DerivedCategory.TStructure.t.isLE_of_iso e b, tor_iso T _ e c d h.2.2.2⟩

private theorem sequence_of_iso (l : ℕ) [Fact l.Prime] (E : FieldStage.{u} l)
    (T : Scheme.{u}) {M N : coefficientSequenceDerived l E.carrier T}
    (e : M ≅ N) (hM : sequenceProperty l E T M)
    (hN : IsNormalizedCoefficientSequence l E.carrier T N) : sequenceProperty l E T N := by
  obtain ⟨a, b, c, d, hab, hcd, h⟩ := hM.2
  exact ⟨hN, a, b, c, d, hab, hcd, fun n ↦
    fiber_bounds_iso l E T n
      ((coefficientSequenceDerivedEvaluation l E.carrier T n).mapIso e) a b c d (h n)⟩

private theorem reduction_iff (l : ℕ) [Fact l.Prime] (E : FieldStage.{u} l)
    (T : Scheme.{u}) (S : CoefficientDerivedSystemCalculus l E.carrier T)
    (K : DerivedCategory (scalarReductionSource l E.carrier T)) :
    finiteTorConstructibleIntegral l E.carrier T K ↔
      IntegralOnSlice.IsComplete l E.carrier T none K ∧
        sequenceProperty l E T (S.reduction.obj K) := by
  constructor
  · rintro ⟨⟨hc, a, b, hab, h⟩, c, d, hcd, ht⟩
    refine ⟨(complete_iff l E T K).mp hc, S.reduction_normalized K,
      a, b, c, d, hab, hcd, fun n ↦ ?_⟩
    have hs := (support_iff T _ _ a b).mp (h n).2
    exact fiber_bounds_iso l E T n ((S.reductionEvaluation n).app K).symm a b c d
      ⟨⟨(h n).1, c, d, ht n⟩, hs.1, hs.2, ht n⟩
  · rintro ⟨hc, _, a, b, c, d, hab, hcd, h⟩
    have hn (n : ℕ) :=
      fiber_bounds_iso l E T n ((S.reductionEvaluation n).app K) a b c d (h n)
    exact ⟨⟨(complete_iff l E T K).mpr hc, a, b, hab, fun n ↦
      ⟨(hn n).1.1, (support_iff T _ _ a b).mpr ⟨(hn n).2.1, (hn n).2.2.1⟩⟩⟩,
      c, d, hcd, fun n ↦ (hn n).2.2.2⟩

/-- A normalized reduction/limit reconstruction exists at one endpoint and one field
stage.  This is the endpoint instance of Zheng, Construction 5.25 and Proposition 5.26.
The proof applies the normalized reduction/limit theorem to the coefficient sequence,
then restricts to the replete subcategory carrying the common finite and Tor bounds.
(blueprint: new-lem-sf-exceptional-ring-transport-endpoint-reconstruction)
-/
theorem exists_exceptional_transport_endpoint_reconstruction
    (l : ℕ) [Fact l.Prime] (E : FieldStage.{u} l)
    {T : Scheme.{u}} :
    Nonempty (Reconstruction l E T) := by
  obtain ⟨S, _⟩ := coefficientDerivedSystemEvaluationCalculus l E.carrier T
  have hr := purNormalizedReconstructionOfScheme l E.carrier T S
  let P := finiteTorConstructibleIntegral l E.carrier T
  let Q := sequenceProperty l E T
  let R : P.FullSubcategory ⥤ Q.FullSubcategory :=
    Q.lift (P.ι ⋙ S.reduction)
      (fun K ↦ ((reduction_iff l E T S K.obj).mp K.property).2)
  let L : Q.FullSubcategory ⥤ P.FullSubcategory :=
    P.lift (Q.ι ⋙ coefficientSequenceLimit l E.carrier T) (fun N ↦ by
      have hc := (hr.1 N.obj N.property.1).1
      have : IsIso (S.adjunction.counit.app N.obj) := (hr.1 N.obj N.property.1).2
      apply (reduction_iff l E T S _).mpr
      exact ⟨hc, sequence_of_iso l E T (asIso (S.adjunction.counit.app N.obj)).symm
        N.property (S.reduction_normalized _)⟩)
  let adj : R ⊣ L := S.adjunction.restrictFullyFaithful
    P.fullyFaithfulι Q.fullyFaithfulι (Iso.refl _) (Iso.refl _)
  have hu (K) : P.ι.map (adj.unit.app K) = S.adjunction.unit.app K.obj := by
    dsimp only [adj]
    rw [Adjunction.map_restrictFullyFaithful_unit_app]
    change S.adjunction.unit.app K.obj ≫
      (coefficientSequenceLimit l E.carrier T).map (𝟙 _) ≫ 𝟙 _ = _
    rw [CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  have he (N) : Q.ι.map (adj.counit.app N) = S.adjunction.counit.app N.obj := by
    dsimp only [adj]
    rw [Adjunction.map_restrictFullyFaithful_counit_app]
    change 𝟙 _ ≫ S.reduction.map (𝟙 _) ≫ S.adjunction.counit.app N.obj = _
    rw [CategoryTheory.Functor.map_id]
    simp only [Category.id_comp]
  have hiu (K) : IsIso (adj.unit.app K) := by
    have : IsIso (S.adjunction.unit.app K.obj) :=
      hr.2 K.obj ((reduction_iff l E T S K.obj).mp K.property).1
    have : IsIso (P.ι.map (adj.unit.app K)) := by rw [hu]; infer_instance
    exact isIso_of_reflects_iso _ P.ι
  have hie (N) : IsIso (adj.counit.app N) := by
    have : IsIso (S.adjunction.counit.app N.obj) := (hr.1 N.obj N.property.1).2
    have : IsIso (Q.ι.map (adj.counit.app N)) := by rw [he]; infer_instance
    exact isIso_of_reflects_iso _ Q.ι
  refine ⟨{
    calculus := S
    equivalence := adj.toEquivalence
    reduction := rfl
    limit := rfl
    unit := ?_
    counit := ?_
    evaluation := fun n ↦
      (finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos _) T).lift
        (Q.ι ⋙ coefficientSequenceDerivedEvaluation l E.carrier T n) (fun N ↦ by
          obtain ⟨a, b, c, d, hab, hcd, h⟩ := N.property.2
          exact (h n).1)
    evaluation_eq := fun _ ↦ rfl }⟩
  · intro K
    exact heq_of_eq (hu K)
  · intro N
    exact heq_of_eq (he N)

end WeilConjectures.ExceptionalIntegralScalar
