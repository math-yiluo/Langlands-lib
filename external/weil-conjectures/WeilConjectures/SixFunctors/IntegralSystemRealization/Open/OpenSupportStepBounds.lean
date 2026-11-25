/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import all WeilConjectures.AlgebraicGeometry.Open.OpenExtensionFiniteTor
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleOrigin
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import all WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorCoherence
import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralCanonicalAmbientModels
import all WeilConjectures.SixFunctors.GeneratorReduction.OpenReconstructionEffectivity
import all WeilConjectures.SmoothPurity.CompletedOpenTensor.CompletedOpenTensorSystemRealization

/-! # Single-operation bounds for completed compact support

Source: Stacks 0941, 0F10 and 0F7J; the common-bound argument in
lem-sf-completed-shriek-composition-laws, steps 7 and 8.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem finite_bounds_iso (W : Scheme.{u}) (n : ℕ)
    {K L : proEtaleDerivedCategory W (Padic.coefficientExtensionRing l E (n + 1))}
    (e : K ≅ L) (a b c d : ℤ)
    (hc : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W K)
    (hs : proEtaleCohomologicalSupport K ⊆ Set.Icc a b)
    (ht : HasProEtaleTorAmplitude W (Padic.coefficientExtensionRing l E (n + 1)) K c d) :
    intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W L ∧
      proEtaleCohomologicalSupport L ⊆ Set.Icc a b ∧
      HasProEtaleTorAmplitude W (Padic.coefficientExtensionRing l E (n + 1)) L c d := by
  have : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W) :=
    (proEtale_bounded_constructible_isTriangulated W _).1
  refine ⟨ObjectProperty.prop_of_iso _ e hc, ?_, ht.1, ?_⟩
  · intro i hi
    apply hs
    intro hz
    exact hi (hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e.symm))
  · rintro S P ⟨e'⟩ f hf hP N i hi
    exact ht.2 S P ⟨e' ≪≫ e.symm⟩ f hf hP N i hi

private theorem open_levelBounds (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) {X Y : Over (Spec (CommRingCat.of D.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (j : X ⟶ Y) [IsOpenImmersion j.left] [QuasiCompact j.left]
    (M : System l E X.left) (hM : LevelBounds l E X.left M) :
    LevelBounds l E Y.left ((Operations.shriek l E o j.left).obj M) := by
  let : X.left.Over (Spec (.of D.k)) := ⟨X.hom⟩
  let : Y.left.Over (Spec (.of D.k)) := ⟨Y.hom⟩
  let : j.left.IsOver (Spec (.of D.k)) := ⟨j.w⟩
  have : LocallyOfFiniteType (X.left ↘ Spec (.of D.k)) := ‹LocallyOfFiniteType X.hom›
  have : QuasiCompact (X.left ↘ Spec (.of D.k)) := ‹QuasiCompact X.hom›
  have : LocallyOfFiniteType (Y.left ↘ Spec (.of D.k)) := ‹LocallyOfFiniteType Y.hom›
  have : QuasiCompact (Y.left ↘ Spec (.of D.k)) := ‹QuasiCompact Y.hom›
  obtain ⟨a, b, c, d, hab, hcd, h⟩ := hM
  refine ⟨a, b, c, d, hab, hcd, fun n ↦ ?_⟩
  obtain ⟨hc, hs, ht⟩ := h n
  obtain ⟨hc', hs', ht'⟩ := finiteStageDerivedExtensionByZero_constructibleFiniteTor
    D l hl E (n + 1) (Nat.succ_pos n) j.left
      ((coefficientSequenceDerivedEvaluation l E X.left n).obj M) hc ⟨c, d, ht⟩
  have hb : proEtaleCohomologicalSupport
      ((finiteStageDerivedExtensionByZero l E (n + 1) (Nat.succ_pos n) j.left).obj
        ((coefficientSequenceDerivedEvaluation l E X.left n).obj M)) ⊆ Set.Icc a b := by
    intro i hi
    by_contra hn
    have hout : i < a ∨ b < i := by
      by_cases ha : a ≤ i
      · exact Or.inr (lt_of_not_ge (fun hb ↦ hn ⟨ha, hb⟩))
      · exact Or.inl (lt_of_not_ge ha)
    apply hi
    apply hs' a b _ i hout
    intro r hr
    by_contra hz
    have hh := hs hz
    rcases hr with hr | hr
    · exact (not_lt_of_ge hh.1) hr
    · exact (not_lt_of_ge hh.2) hr
  exact finite_bounds_iso l E Y.left n
    (((o.openEvaluation j.left).evaluation n).app M).symm a b c d
    hc'.1 hb (ht' c d ht)

private theorem open_integralConstructible (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Over (Spec (CommRingCat.of D.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (j : X ⟶ Y) [IsOpenImmersion j.left]
    (K : Integral l E X.left) (hK : sfIntegralConstructible l E X.left K) :
    sfIntegralConstructible l E Y.left ((ringedOpen l E j.left).obj K) := by
  obtain ⟨h⟩ := OpenFactorCoherence.fixedOpen_exists l E D hl X Y j
  exact h.constructible K hK

private theorem finite_origin (W : Scheme.{u}) (n : ℕ)
    (K : proEtaleDerivedCategory W (Padic.coefficientExtensionRing l E (n + 1)))
    (hc : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W K)
    (a b : ℤ) (hs : proEtaleCohomologicalSupport K ⊆ Set.Icc a b) :
    ∃ L : DerivedCategory.Plus (Sheaf (ProEt.topology W)
        (ModuleCat.{u + 1} (ULift.{u + 1, u}
          (Padic.coefficientExtensionRing l E (n + 1))))),
      Nonempty (FixedEtaleOriginWitness W
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) L) ∧
      Nonempty ((sfIntrinsicModuleEquivalence W
        (Padic.coefficientExtensionRing l E (n + 1))).functor.mapDerivedCategory.obj
          L.obj ≅ K) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  have : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let F := sfIntrinsicModuleEquivalence W A
  let L := F.inverse.mapDerivedCategory.obj K
  let e : F.functor.mapDerivedCategory.obj L ≅ K := F.mapDerivedCategory.counitIso.app K
  have hzero (i : ℤ) (hi : i < a ∨ b < i) :
      IsZero ((DerivedCategory.homologyFunctor _ i).obj K) := by
    by_contra hz
    have hh := hs hz
    rcases hi with hi | hi
    · exact (not_lt_of_ge hh.1) hi
    · exact (not_lt_of_ge hh.2) hi
  have hz (i : ℤ) (hi : i < a ∨ b < i) :
      IsZero ((DerivedCategory.homologyFunctor _ i).obj L) := by
    apply F.functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
    exact (hzero i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e)
  have hconstruct (i : ℤ) : ProEtale.IsConstructible (ULift.{u + 1, u} A)
      ((DerivedCategory.homologyFunctor _ i).obj L) := by
    apply (realization_constructible_iff W A _).mp
    let eH := ((F.functor.mapDerivedCategoryHomologyFunctorIso i).app L) ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso e
    rw [proEtaleModuleRestriction_constructible_iff]
    exact ProEtale.isConstructible_of_iso
      ((proEtaleModuleRestriction W A).mapIso eH.symm)
      ((proEtaleModuleRestriction_constructible_iff W A _).mp (hc.2 i))
  obtain ⟨P, hP, ⟨ep⟩⟩ := ProEtale.fixedDerivedOrigin W (ULift.{u + 1, u} A)
    L hconstruct a b hz
  have hL : DerivedCategory.TStructure.t.plus L :=
    ⟨a, (DerivedCategory.isGE_iff L a).mpr (fun i hi ↦ hz i (Or.inl hi))⟩
  have hP' : DerivedCategory.TStructure.t.plus P := by
    obtain ⟨c, d, _, hb⟩ := hP.2
    exact ⟨c, (DerivedCategory.isGE_iff P c).mpr (fun i hi ↦ hb i (Or.inl hi))⟩
  exact ⟨⟨L, hL⟩, ⟨⟨⟨P, hP'⟩, ep⟩⟩, ⟨e⟩⟩

private theorem origins_of_levelBounds (W : Scheme.{u}) (M : System l E W)
    (hM : LevelBounds l E W M) : Nonempty (Origins l E W M) := by
  classical
  obtain ⟨a, b, c, d, _, _, h⟩ := hM
  have ho (n : ℕ) := finite_origin l E W n
    ((coefficientSequenceDerivedEvaluation l E W n).obj M) (h n).1 a b (h n).2.1
  choose L O ev using ho
  let e (n : ℕ) := Classical.choice (ev n)
  let w (n : ℕ) := Classical.choice (O n)
  let R (n : ℕ) := normalizedDVRRes l E W (Nat.le_succ n)
  let S (n : ℕ) := Sheaf.derivedRestrictScalars (ProEt.topology W)
    (Padic.coefficientExtensionTransition l E (n + 1)).ulift.{u + 1, u + 1}
  let F (n : ℕ) := (sfIntrinsicModuleEquivalence W
    (Padic.coefficientExtensionRing l E (n + 1))).functor.mapDerivedCategory
  let t (n : ℕ) : (F (n + 1)).obj (L (n + 1)).obj ⟶
      (F (n + 1)).obj ((S n).obj (L n).obj) := by
    let := normalizedDVRModuleRes_limits l E W (Nat.le_succ n)
    let := normalizedDVRModuleRes_colimits l E W (Nat.le_succ n)
    exact (e (n + 1)).hom ≫
      (coefficientSequenceDerivedTransition l E W (Nat.le_succ n)).app M ≫
      (R n).map (e n).inv ≫
      (Functor.mapDerivedCategoryNatIso (eqToIso (originRestrictionEquality l E W n))).inv.app
        ((F n).obj (L n).obj) ≫
      (Functor.mapDerivedCategorySquareIso (sfRealizationRestriction W
        (Padic.coefficientExtensionTransition l E (n + 1)))).hom.app (L n).obj
  let f (n : ℕ) : (L (n + 1)).obj ⟶ (S n).obj (L n).obj := (F (n + 1)).preimage (t n)
  have hf (n : ℕ) : (F (n + 1)).map (f n) = t n := (F (n + 1)).map_preimage _
  have ht (n : ℕ) : ∃ g : (w (n + 1)).complex.obj ⟶
      (Sheaf.derivedRestrictScalars W.smallEtaleTopology
        (Padic.coefficientExtensionTransition l E (n + 1)).ulift.{u + 1, u + 1}).obj
          (w n).complex.obj,
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u}
          (Padic.coefficientExtensionRing l E (n + 2)))) W).mapDerivedCategory.map g =
        (w (n + 1)).iso.hom ≫ f n ≫
          (S n).map (w n).iso.inv ≫
          (ProEtale.pbcDerivedComparisonRestrict W
            (Padic.coefficientExtensionTransition l E (n + 1)).ulift.{u + 1, u + 1}).hom.app
              (w n).complex.obj := by
    let P := (w n).complex
    obtain ⟨q, hq⟩ := P.property
    have := hq
    have hp : DerivedCategory.TStructure.t.plus
        ((Sheaf.derivedRestrictScalars W.smallEtaleTopology
          (Padic.coefficientExtensionTransition l E (n + 1)).ulift.{u + 1, u + 1}).obj P.obj) :=
      ⟨q, Functor.isGE_mapDerivedCategory_obj
        (Sheaf.restrictScalars W.smallEtaleTopology
          (Padic.coefficientExtensionTransition l E (n + 1)).ulift.{u + 1, u + 1}) P.obj q⟩
    exact (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map _ _ hp).2 _
  choose g hg using ht
  refine ⟨{ level := L
            origin := O
            evaluation := e
            fixedTransition := f
            etaleTransition := g
            originSquare := ?_
            transitionSquare := ?_ }⟩
  · intro n
    change (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 2)))) W).mapDerivedCategory.map (g n) ≫
      (ProEtale.pbcDerivedComparisonRestrict W
        (Padic.coefficientExtensionTransition l E (n + 1)).ulift.{u + 1, u + 1}).inv.app
          (w n).complex.obj ≫ (S n).map (w n).iso.hom = (w (n + 1)).iso.hom ≫ f n
    rw [hg]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← (S n).map_comp, Iso.inv_hom_id, (S n).map_id]
    exact congrArg (fun z ↦ (w (n + 1)).iso.hom ≫ z)
      (CategoryTheory.Category.comp_id (f n))
  · intro n
    let := normalizedDVRModuleRes_limits l E W (Nat.le_succ n)
    let := normalizedDVRModuleRes_colimits l E W (Nat.le_succ n)
    change (F (n + 1)).map (f n) ≫ _ ≫
      (Functor.mapDerivedCategoryNatIso (eqToIso (originRestrictionEquality l E W n))).hom.app
        ((F n).obj (L n).obj) = _
    rw [hf]
    simp only [t, Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app]
    rw [CategoryTheory.Category.comp_id]

private theorem coefficient_prime_unit (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) :
    IsUnit (l : D.k) := by
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  have hc : Fintype.card D.k₀ = D.p ^ D.a := by
    simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow hc
  have hu : IsUnit (l : D.k₀) := (CharP.isUnit_natCast_iff D.prime).2 (by
    intro hdiv
    exact hl ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : l.Prime)).1 hdiv).symm)
  simpa only [map_natCast] using hu.map (algebraMap D.k₀ D.k)

private theorem open_normalized {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (hX : IsUnit (l : Γ(X, ⊤))) (o : Open l E j) (M : System l E X)
    (hM : IsNormalizedCoefficientSequence l E X M) :
    IsNormalizedCoefficientSequence l E Y (o.derived.obj M) := by
  obtain ⟨o', ⟨a⟩⟩ := integralCanonicalAmbientModels l E
  let SX := calculus l E X
  let SY := calculus l E Y
  let K := (coefficientSequenceLimit l E X).obj M
  have hc : IsIso (SX.adjunction.counit.app M) :=
    ((purNormalizedReconstruction l E X hX SX).1 M hM).2
  have hr := GeneratorReduction.fixedOpenReduction_isIso l E o' a.realizationModel j K
  let e : (Operations.shriek l E o' j).obj M ≅
      SY.reduction.obj ((ringedOpen l E j).obj K) :=
    (Operations.shriek l E o' j).mapIso (asIso (SX.adjunction.counit.app M)).symm ≪≫
      asIso ((a.realizationModel.openReduction l E j).app K)
  let t : Operations.shriek l E o' j ≅ o.derived :=
    (o'.extension j).adj.leftAdjointUniq o.adj
  intro m n h P
  exact CompletedOpenTensor.normalized_of_iso l E Y (e.symm ≪≫ t.app M)
    (fun {m n} h P ↦ SY.reduction_normalized _ h P) h P

/-- One quasi-compact open letter preserves the system domain and integral
constructibility, with the same finite cohomology and Tor intervals.
Source: Stacks 0GL1, 0E8I, 0941; parent proof step 8
(blueprint: lem-sf-open-support-step-bounds).

Proof: the finite open CTF theorem preserves constructible cohomology and the
same cohomological and Tor intervals at every level; transport these conclusions
through the specified open evaluation. For normalization, reconstruct the input
as the reduction of its total limit using the invertible actual counit. The
canonical ambient model and the proved open-reduction effectivity theorem identify
its open extension with an actual reduction system, which is normalized. Uniqueness
of left adjoints transports this conclusion to the specified operation o.
For each output level use bounded constructible etale descent after the canonical
module equivalence. Full faithfulness of that equivalence and of the bounded-below
etale comparison lifts the actual system transition and proves the two origin
squares. Finally the canonical open-factor coherence data already prove integral
constructibility of ringedOpen, independently of the system input. Combine the
three system properties and this independent integral conclusion. No separatedness
hypothesis is introduced. -/
theorem openSupportStep_bounds (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) {X Y : Over (Spec (CommRingCat.of D.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (j : X ⟶ Y) [IsOpenImmersion j.left] [QuasiCompact j.left]
    (M : System l E X.left) (hM : Good l E X.left M) (K : Integral l E X.left)
    (hK : sfIntegralConstructible l E X.left K) :
    Good l E Y.left ((Operations.shriek l E o j.left).obj M) ∧
      sfIntegralConstructible l E Y.left ((ringedOpen l E j.left).obj K) := by
  refine ⟨?_, open_integralConstructible l E D hl j K hK⟩
  refine ⟨?_, open_levelBounds l E D hl o j M hM.2.1, ?_⟩
  · have hX : IsUnit (l : Γ(X.left, ⊤)) := by
      simpa only [map_natCast] using (coefficient_prime_unit l D hl).map
        ((Scheme.ΓSpecIso (.of D.k)).inv ≫ X.hom.appTop).hom
    intro m n h P
    exact open_normalized l E j.left hX (o.extension j.left) M
      (fun {m n} h P ↦ hM.1 h P) h P
  · exact origins_of_levelBounds l E Y.left _ (open_levelBounds l E D hl o j M hM.2.1)

end WeilConjectures.IntegralSystemRealization
