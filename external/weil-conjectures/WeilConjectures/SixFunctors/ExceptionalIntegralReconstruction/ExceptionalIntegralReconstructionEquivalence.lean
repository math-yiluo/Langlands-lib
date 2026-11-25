/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction.ExceptionalIntegralReconstructionInterfaces
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.SixFunctors.Supporting.PurSequenceAdjointResolutionShifts
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import Mathlib.CategoryTheory.Adjunction.Restrict

/-! # Restriction of actual reconstruction to uniform finite-Tor bounds

Source: Zheng, Section 4; integral reconstruction proof, step 1.
(blueprint: lem-sf-exceptional-integral-reconstruction-equivalence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralReconstruction
open IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem complete_iff (T : Scheme.{u}) (K : Integral l E T) :
    IsSfDerivedComplete l E T K ↔ IntegralOnSlice.IsComplete l E T none K := by
  constructor
  · intro hK
    obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
    let : Fact p.Prime := ⟨hprime⟩
    let F : FiniteFieldDatum.{0} :=
      { p := p, a := 1, q := p, prime := hprime, exponent_pos := le_rfl,
        cardinality_eq := (pow_one p).symm, k₀ := ZMod p,
        card_base := by simp [Nat.card_eq_fintype_card], k := AlgebraicClosure (ZMod p) }
    have hl : l ≠ F.p := by change l ≠ p; omega
    exact ⟨F, hl, (sfDerivedComplete_iff_legacy l E T F hl K).mp hK⟩
  · rintro ⟨F, hl, hK⟩
    exact (sfDerivedComplete_iff_legacy l E T F hl K).mpr hK

private theorem finite_bounds_iso (T : Scheme.{u}) (n : ℕ)
    {K L : proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E (n + 1))}
    (e : K ≅ L) {a b c d : ℤ}
    (hK : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) T K ∧
      proEtaleCohomologicalSupport K ⊆ Set.Icc a b ∧
      HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E (n + 1)) K c d) :
    intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) T L ∧
      proEtaleCohomologicalSupport L ⊆ Set.Icc a b ∧
      HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E (n + 1)) L c d := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) T) :=
    (proEtale_bounded_constructible_isTriangulated T A).1
  refine ⟨ObjectProperty.prop_of_iso _ e hK.1, ?_, hK.2.2.1, ?_⟩
  · intro i hi
    apply hK.2.1
    intro hz
    exact hi (((DerivedCategory.homologyFunctor _ i).mapIso e).isZero_iff.mp hz)
  · intro N P hN f hf hP M i hi
    obtain ⟨q⟩ := hN
    exact hK.2.2.2 N P ⟨q ≪≫ e.symm⟩ f hf hP M i hi

private theorem reduction_bounds (T : Scheme.{u}) (K : Integral l E T) :
    finiteTorConstructibleIntegral l E T K ↔
      IsSfDerivedComplete l E T K ∧
        LevelBounds l E T ((calculus l E T).reduction.obj K) := by
  constructor
  · rintro ⟨⟨hc, a, b, hab, h⟩, c, d, hcd, ht⟩
    refine ⟨hc, a, b, c, d, hab, hcd, fun n ↦ ?_⟩
    exact finite_bounds_iso l E T n (((calculus l E T).reductionEvaluation n).symm.app K)
      ⟨(h n).1, (h n).2, ht n⟩
  · rintro ⟨hc, a, b, c, d, hab, hcd, h⟩
    have h' := fun n ↦ finite_bounds_iso l E T n
      (((calculus l E T).reductionEvaluation n).app K) (h n)
    exact ⟨⟨hc, a, b, hab, fun n ↦ ⟨(h' n).1, (h' n).2.1⟩⟩,
      c, d, hcd, fun n ↦ (h' n).2.2⟩

/-- The actual adjunction restricts to the uniform bounded finite-Tor categories.
Source: Zheng, Section 4, and step 1 of integral reconstruction.
(blueprint: lem-sf-exceptional-integral-reconstruction-equivalence).

Proof: reduction is normalized by its K-flat model. Its evaluation comparison
transports the two common intervals without changing their endpoints. Conversely,
the actual counit of a normalized system is invertible; its evaluations transport
those same intervals to the reductions of the total limit, which is complete.
Restrict the ambient adjunction along the full inclusions. Its unit and counit
are the actual ambient maps and are invertible by normalized reconstruction, so
it is an equivalence. Finally retain the resolution and shift comparisons of the
same calculus. This also applies to zero objects and empty schemes. -/
theorem exceptionalIntegralReconstructionEquivalence
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) (T : Scheme.{u})
    [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))] [QuasiCompact (T ↘ Spec (.of D.k))] :
    Nonempty (Reconstruction l E T) := by
  let S := calculus l E T
  let P := finiteTorConstructibleIntegral l E T
  let Q := normalized l E T
  have hR (K : P.FullSubcategory) : Q (S.reduction.obj K.obj) :=
    ⟨S.reduction_normalized K.obj, ((reduction_bounds l E T K.obj).mp K.property).2⟩
  have hL (N : Q.FullSubcategory) : P ((coefficientSequenceLimit l E T).obj N.obj) := by
    obtain ⟨hc, hi⟩ := (purNormalizedReconstructionOfScheme l E T S).1 N.obj N.property.1
    apply (reduction_bounds l E T _).mpr
    refine ⟨(complete_iff l E T _).mpr hc, ?_⟩
    obtain ⟨a, b, c, d, hab, hcd, h⟩ := N.property.2
    refine ⟨a, b, c, d, hab, hcd, fun n ↦ ?_⟩
    exact finite_bounds_iso l E T n
      (((coefficientSequenceDerivedEvaluation l E T n).mapIso
        (@asIso _ _ _ _ (S.adjunction.counit.app N.obj) hi)).symm) (h n)
  let R := Q.lift (P.ι ⋙ S.reduction) hR
  let L := P.lift (Q.ι ⋙ coefficientSequenceLimit l E T) hL
  let adj : R ⊣ L := S.adjunction.restrictFullyFaithful
    P.fullyFaithfulι Q.fullyFaithfulι (Iso.refl _) (Iso.refl _)
  have hu (K) : P.ι.map (adj.unit.app K) = S.adjunction.unit.app K.obj := by
    dsimp only [adj]
    rw [Adjunction.map_restrictFullyFaithful_unit_app]
    change S.adjunction.unit.app K.obj ≫
      (coefficientSequenceLimit l E T).map (𝟙 _) ≫ 𝟙 _ = _
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
    exact Category.comp_id _
  have he (N) : Q.ι.map (adj.counit.app N) = S.adjunction.counit.app N.obj := by
    dsimp only [adj]
    rw [Adjunction.map_restrictFullyFaithful_counit_app]
    change 𝟙 _ ≫ S.reduction.map (𝟙 _) ≫ S.adjunction.counit.app N.obj = _
    rw [CategoryTheory.Functor.map_id]
    simp only [Category.id_comp]
  let (K : P.FullSubcategory) : IsIso (adj.unit.app K) := by
    have : IsIso (S.adjunction.unit.app K.obj) :=
      (purNormalizedReconstructionOfScheme l E T S).2 K.obj
        ((complete_iff l E T K.obj).mp K.property.1.1)
    have : IsIso (P.ι.map (adj.unit.app K)) := by rw [hu]; infer_instance
    exact isIso_of_reflects_iso _ P.ι
  let (N : Q.FullSubcategory) : IsIso (adj.counit.app N) := by
    have : IsIso (S.adjunction.counit.app N.obj) :=
      ((purNormalizedReconstructionOfScheme l E T S).1 N.obj N.property.1).2
    have : IsIso (Q.ι.map (adj.counit.app N)) := by rw [he]; infer_instance
    exact isIso_of_reflects_iso _ Q.ι
  have hS : CoefficientDerivedSystemCoherence l E T S :=
    (coefficientDerivedSystemEvaluationCalculus l E T).choose_spec.some
  obtain ⟨res, shifts⟩ := purSequenceAdjointResolutionShifts l E T D hl S hS
  obtain ⟨shifts⟩ := shifts
  obtain ⟨limShifts⟩ := purReductionLimitShiftAdjunction l E T S hS
  refine ⟨{
    coherence := hS
    equivalence := adj.toEquivalence
    reduction := Iso.refl _
    limit := Iso.refl _
    unit := ?_
    counit := ?_
    resolutions := res
    resolutionShifts := shifts
    shifts := limShifts }⟩
  · intro K
    change P.ι.map (adj.unit.app K) ≫
      𝟙 ((coefficientSequenceLimit l E T).obj (S.reduction.obj K.obj)) ≫
      (coefficientSequenceLimit l E T).map (𝟙 (S.reduction.obj K.obj)) =
        S.adjunction.unit.app K.obj
    rw [CategoryTheory.Functor.map_id]
    exact (congrArg (fun g ↦ P.ι.map (adj.unit.app K) ≫ g)
      (CategoryTheory.Category.id_comp (𝟙 _))).trans
        ((CategoryTheory.Category.comp_id _).trans (hu K))
  · intro N
    change 𝟙 _ ≫ S.reduction.map (𝟙 _) ≫ S.adjunction.counit.app N.obj =
      Q.ι.map (adj.counit.app N)
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
    exact (he N).symm

end WeilConjectures.ExceptionalIntegralReconstruction
