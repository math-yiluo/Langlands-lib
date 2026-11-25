/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenTensorQuotient.OpenTensorQuotientData
public import WeilConjectures.SmoothPurity.CompletedOpenTensor.CompletedOpenTensorRepresentatives
import WeilConjectures.SmoothPurity.Sf.SfFiniteOpenRestrictionPresentation
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteImmersionConstructibilityInterval
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Mathlib.Data.Nat.Prime.Infinite

/-! # Geometric preservation for compatible open reduction models

Source: Bhatt--Scholze, Lemma 6.5.8(2),(3); Stacks Tags 03DI and 09AH.
(blueprint: lem-sf-open-quotient-model-geometry).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] SheafOfModules.monoidalCategory

universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
  AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenTensorQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

private theorem complete_iff (T : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource l E T)) :
    IsSfDerivedComplete l E T K ↔ IntegralOpenReduction.complete l E T K := by
  constructor
  · intro hK
    obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
    have : Fact p.Prime := ⟨hprime⟩
    let D : FiniteFieldDatum.{0} :=
      { p := p
        a := 1
        q := p
        prime := hprime
        exponent_pos := by decide
        cardinality_eq := by simp
        k₀ := ZMod p
        card_base := by simp [Nat.card_eq_fintype_card]
        k := AlgebraicClosure (ZMod p) }
    have hl : l ≠ D.p := by change l ≠ p; omega
    exact ⟨D, hl, (sfDerivedComplete_iff_legacy l E T D hl K).mp hK⟩
  · rintro ⟨D, hl, hK⟩
    exact (sfDerivedComplete_iff_legacy l E T D hl K).mpr hK

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private def restrictionEvaluation (o : IntegralOpenReduction.Operations l E j) (n : ℕ) :
    IntegralOpenReduction.systemRestriction l E j o ⋙ coefficientSequenceEvaluation l E U n ≅
      coefficientSequenceEvaluation l E X n ⋙ IntegralOpenReduction.finiteRestriction l E j o n :=
  isoWhiskerLeft
      (IntegralOpenReduction.systemRestriction l E j o ⋙ coefficientSequenceEvaluation l E U n)
      (o.finite n).unitIso ≪≫
    isoWhiskerRight
      (isoWhiskerLeft (IntegralOpenReduction.systemRestriction l E j o)
        (o.transportEvaluation n).symm) (o.finite n).inverse ≪≫
    isoWhiskerRight
      (isoWhiskerLeft
        (SemilinearSections.openRestriction (ProEt.topology X)
          (IntegralOpenReduction.rings l E X) (IntegralOpenReduction.transitions l E X)
          (IntegralOpenReduction.openObject j))
        (isoWhiskerRight o.systems.counitIso
          (SemilinearSections.evaluation
            ((ProEt.topology X).over (IntegralOpenReduction.openObject j))
            (fun k ↦ (IntegralOpenReduction.rings l E X k).over
              (IntegralOpenReduction.openObject j))
            (fun k ↦ ((ProEt.topology X).overPullback CommRingCat.{u + 1}
              (IntegralOpenReduction.openObject j)).map
                (IntegralOpenReduction.transitions l E X k)) n))) (o.finite n).inverse ≪≫
    isoWhiskerRight (o.openSystems.restrictionEvaluation n) (o.finite n).inverse

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem finiteProperties_iso (T : Scheme.{u}) (n : ℕ)
    {K L : proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E (n + 1))}
    (e : K ≅ L) (a b : ℤ)
    (hK : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_le_succ n.zero_le) T K)
    (hs : proEtaleCohomologicalSupport K ⊆ Set.Icc a b) :
    intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_le_succ n.zero_le) T L ∧
      proEtaleCohomologicalSupport L ⊆ Set.Icc a b := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1)
    (Nat.succ_le_succ n.zero_le)
  have hsupport : proEtaleCohomologicalSupport L ⊆ proEtaleCohomologicalSupport K := by
    intro i hi hz
    exact hi (((DerivedCategory.homologyFunctor _ i).mapIso e).isZero_iff.mp hz)
  exact ⟨⟨hK.1.subset hsupport, fun i ↦ constructible_of_iso A
    ((DerivedCategory.homologyFunctor _ i).mapIso e).symm (hK.2 i)⟩, hsupport.trans hs⟩

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Finite coefficient identification and integral constructibility for the same open
operations. This concerns the geometric part of open reduction, independently of tensor
augmentations and normalized tensor chain maps.

Source: Bhatt--Scholze, Lemma 6.5.8(2),(3), and Stacks Tags 03DI, 09AH.
(blueprint: lem-sf-open-quotient-model-geometry).

Proof: at each positive coefficient level identify the ringed-slice open extension
with intrinsic extension by zero through the constant-coefficient ring comparison.
Both are left adjoint to the same restriction; their unit on each extension summand
is insertion into that summand. This gives the finite-model isomorphism, including
for empty opens and the identity immersion.

For extension use the completeOpen.extensionComplete field. Compute each derived
reduction on a flat-term K-flat representative using strictOpen.ordinary and its
scalar-unit normalized comparison. After the finite-model identification this is
exact intrinsic finite extension of the original reduction. Apply the finite open
constructibility and interval theorem at every level. Transport constructibility
and cohomological support through these isomorphisms: the single input interval
works at every output level. Completeness and these reductions give integral
constructibility by its definition.

For restriction use completeOpen.restrictionComplete. The completed immersion
pullback comparison identifies its quotient reductions with exact finite restriction.
Pull back each constructible partition by the open immersion; the strata are the
scheme-theoretic intersections and the locally constant models and finite stalks
pull back to those strata. Exact restriction takes zero cohomology to zero, so
every specified interval is preserved. Apply this separately to each supplied
uniform interval, not merely to the interval witnessing constructibility. These
arguments use arbitrary unbounded representatives and impose no finite-Tor bound. -/
theorem openQuotientModelGeometry [IsNoetherian X] [IsNoetherian U]
    (hlX : IsUnit (l : Γ(X, ⊤))) (hlU : IsUnit (l : Γ(U, ⊤)))
    (C : CompletedOpenTensor.Context l E j) :
    FiniteExtensionModel l E j C.operations ∧ IntegralGeometry l E j C.operations := by
  classical
  -- Only ambient invertibility is needed for finite extension; restriction is exact.
  refine (fun (_ : IsUnit (l : Γ(U, ⊤))) ↦ ?_) hlU
  -- The finite comparison is fixed by the normalized restriction presentation.
  let (n : ℕ) : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ n.zero_le)
  let ι (n : ℕ) : IntegralOpenReduction.finiteExtension l E j C.operations n ≅
      sfIntrinsicExtensionByZero j (Padic.coefficientExtensionRing l E (n + 1)) :=
    sfFiniteOpenLeftComparison l E j C.operations n
      (sfFiniteOpenRestriction_presentation l E j C.operations n).exists.choose
  let ρ (n : ℕ) : IntegralOpenReduction.finiteRestriction l E j C.operations n ≅
      proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1)) j :=
    (sfFiniteOpenRestriction_presentation l E j C.operations n).exists.choose ≪≫
      (sfIntrinsicExtensionByZeroAdjunction j _).rightAdjointUniq
        (sfIntrinsicOpenAdjunction _ j) ≪≫ (openSquarePullbackModel _ j).symm
  let hSysExtA : (IntegralOpenReduction.systemExtension l E j C.operations).Additive :=
    IntegralOpenReduction.systemExtensionAdditive l E j C.operations
  let hSysExtL : PreservesFiniteLimits (IntegralOpenReduction.systemExtension l E j C.operations) :=
    IntegralOpenReduction.systemExtensionLimits l E j C.operations
  let hSysExtC :
      PreservesFiniteColimits (IntegralOpenReduction.systemExtension l E j C.operations) :=
    IntegralOpenReduction.systemExtensionColimits l E j C.operations
  let hSysResA : (IntegralOpenReduction.systemRestriction l E j C.operations).Additive :=
    IntegralOpenReduction.systemRestrictionAdditive l E j C.operations
  let hSysResL :
      PreservesFiniteLimits (IntegralOpenReduction.systemRestriction l E j C.operations) := by
    let hInv : PreservesLimitsOfSize.{0, 0} C.operations.systems.inverse :=
      C.operations.systems.toAdjunction.rightAdjoint_preservesLimits
    have hInvFinite : PreservesFiniteLimits C.operations.systems.inverse :=
      @PreservesLimitsOfSize.preservesFiniteLimits _ _ _ _ C.operations.systems.inverse hInv
    let := SemilinearSections.openRestrictionLimits.{u + 1, u, u + 1} (ProEt.topology X)
      (IntegralOpenReduction.rings l E X) (IntegralOpenReduction.transitions l E X)
      (IntegralOpenReduction.openObject j)
    dsimp only [IntegralOpenReduction.systemRestriction]
    exact @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ (by infer_instance) hInvFinite
  let hSysResC :
      PreservesFiniteColimits (IntegralOpenReduction.systemRestriction l E j C.operations) := by
    let hInv : PreservesColimitsOfSize.{0, 0} C.operations.systems.inverse :=
      C.operations.systems.symm.toAdjunction.leftAdjoint_preservesColimits
    have hInvFinite : PreservesFiniteColimits C.operations.systems.inverse :=
      @PreservesColimitsOfSize.preservesFiniteColimits _ _ _ _ C.operations.systems.inverse hInv
    let := SemilinearSections.openRestrictionColimits.{u + 1, u, u + 1} (ProEt.topology X)
      (IntegralOpenReduction.rings l E X) (IntegralOpenReduction.transitions l E X)
      (IntegralOpenReduction.openObject j)
    dsimp only [IntegralOpenReduction.systemRestriction]
    exact @comp_preservesFiniteColimits _ _ _ _ _ _ _ _ (by infer_instance) hInvFinite
  -- The compatible context already contains the reduction squares; descend the
  -- ordinary evaluation squares and then apply finite geometric preservation.
  have hext (K : DerivedCategory (scalarReductionSource l E U))
      (hc : IsSfDerivedComplete l E U K) (a b : ℤ) (hab : a ≤ b)
      (hred : ∀ n : ℕ,
        intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_le_succ n.zero_le) U
          ((scalarReductionDerivedExtension l E U n).obj K) ∧
        proEtaleCohomologicalSupport ((scalarReductionDerivedExtension l E U n).obj K) ⊆
          Set.Icc a b) :
      ∀ n : ℕ,
        intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_le_succ n.zero_le) X
          ((scalarReductionDerivedExtension l E X n).obj
            ((IntegralOpenReduction.shriek l E j C.operations).obj K)) ∧
        proEtaleCohomologicalSupport ((scalarReductionDerivedExtension l E X n).obj
          ((IntegralOpenReduction.shriek l E j C.operations).obj K)) ⊆ Set.Icc a b := by
    intro n
    let : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
      Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ n.zero_le)
    let hEvalXA : (coefficientSequenceEvaluation l E X n).Additive :=
      coefficientSequenceEvaluation_additive l E X n
    let hEvalXL : PreservesFiniteLimits (coefficientSequenceEvaluation l E X n) :=
      (coefficientSequenceEvaluation_exact l E X n).1
    let hEvalXC : PreservesFiniteColimits (coefficientSequenceEvaluation l E X n) :=
      (coefficientSequenceEvaluation_exact l E X n).2
    let hEvalUA : (coefficientSequenceEvaluation l E U n).Additive :=
      coefficientSequenceEvaluation_additive l E U n
    let hEvalUL : PreservesFiniteLimits (coefficientSequenceEvaluation l E U n) :=
      (coefficientSequenceEvaluation_exact l E U n).1
    let hEvalUC : PreservesFiniteColimits (coefficientSequenceEvaluation l E U n) :=
      (coefficientSequenceEvaluation_exact l E U n).2
    let hIntrinsicA : (sfIntrinsicExtensionByZero j
        (Padic.coefficientExtensionRing l E (n + 1))).Additive :=
      (sfIntrinsicExtensionByZero_exact j _).1
    let hIntrinsicL : PreservesFiniteLimits (sfIntrinsicExtensionByZero j
        (Padic.coefficientExtensionRing l E (n + 1))) :=
      (sfIntrinsicExtensionByZero_exact j _).2.1
    let hIntrinsicC : PreservesFiniteColimits (sfIntrinsicExtensionByZero j
        (Padic.coefficientExtensionRing l E (n + 1))) :=
      (sfIntrinsicExtensionByZero_exact j _).2.2
    let hFinA : (IntegralOpenReduction.finiteExtension l E j C.operations n).Additive :=
      IntegralOpenReduction.finiteExtensionAdditive l E j C.operations n
    let hFinL : PreservesFiniteLimits
        (IntegralOpenReduction.finiteExtension l E j C.operations n) :=
      preservesFiniteLimits_of_natIso
        (F := sfIntrinsicExtensionByZero j (Padic.coefficientExtensionRing l E (n + 1)))
        (G := IntegralOpenReduction.finiteExtension l E j C.operations n) (ι n).symm
    let hFinC : PreservesFiniteColimits
        (IntegralOpenReduction.finiteExtension l E j C.operations n) :=
      preservesFiniteColimits_of_natIso
        (F := sfIntrinsicExtensionByZero j (Padic.coefficientExtensionRing l E (n + 1)))
        (G := IntegralOpenReduction.finiteExtension l E j C.operations n) (ι n).symm
    let K' : (IntegralOpenReduction.complete l E U).FullSubcategory :=
      ⟨K, (complete_iff l E U K).mp hc⟩
    let α := ((C.ambient.reductionEvaluation n).app
        ((IntegralOpenReduction.shriek l E j C.operations).obj K)).symm ≪≫
      (coefficientSequenceDerivedEvaluation l E X n).mapIso (C.completeOpen.r.app K') ≪≫
      (@Functor.mapDerivedCategorySquareIso _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (IntegralOpenReduction.systemExtension l E j C.operations)
        (coefficientSequenceEvaluation l E X n) (coefficientSequenceEvaluation l E U n)
        (IntegralOpenReduction.finiteExtension l E j C.operations n)
        hSysExtA hSysExtL hSysExtC hEvalXA hEvalXL hEvalXC
        hEvalUA hEvalUL hEvalUC hFinA hFinL hFinC
        (IntegralOpenReduction.extensionEvaluation l E j C.operations n)).app
          (C.openSite.reduction.obj K) ≪≫
      (IntegralOpenReduction.finiteExtension l E j C.operations n).mapDerivedCategory.mapIso
        ((C.openSite.reductionEvaluation n).app K) ≪≫
      (@Functor.mapDerivedCategoryNatIso _ _ _ _ _ _ _ _
        (IntegralOpenReduction.finiteExtension l E j C.operations n)
        (sfIntrinsicExtensionByZero j (Padic.coefficientExtensionRing l E (n + 1)))
        hFinA hIntrinsicA hFinL hFinC hIntrinsicL hIntrinsicC (ι n)).app
        ((scalarReductionDerivedExtension l E U n).obj K)
    have hl : ∀ x : X, IsUnit (l : X.presheaf.stalk x) := by
      intro x
      simpa only [map_natCast] using (hlX.map (X.presheaf.germ ⊤ x trivial).hom)
    have h := open_finite_constructibility_interval l E (n + 1)
      (Nat.succ_le_succ n.zero_le) j hl a b hab
      ((scalarReductionDerivedExtension l E U n).obj K) (hred n).1 (hred n).2
    exact finiteProperties_iso l E X n α.symm a b h.1 h.2.1
  have hres (K : DerivedCategory (scalarReductionSource l E X))
      (hc : IsSfDerivedComplete l E X K) (a b : ℤ)
      (hred : ∀ n : ℕ,
        intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_le_succ n.zero_le) X
          ((scalarReductionDerivedExtension l E X n).obj K) ∧
        proEtaleCohomologicalSupport ((scalarReductionDerivedExtension l E X n).obj K) ⊆
          Set.Icc a b) :
      ∀ n : ℕ,
        intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_le_succ n.zero_le) U
          ((scalarReductionDerivedExtension l E U n).obj
            ((IntegralOpenReduction.star l E j C.operations).obj K)) ∧
        proEtaleCohomologicalSupport ((scalarReductionDerivedExtension l E U n).obj
          ((IntegralOpenReduction.star l E j C.operations).obj K)) ⊆ Set.Icc a b := by
    intro n
    let : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
      Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ n.zero_le)
    let hEvalXA : (coefficientSequenceEvaluation l E X n).Additive :=
      coefficientSequenceEvaluation_additive l E X n
    let hEvalXL : PreservesFiniteLimits (coefficientSequenceEvaluation l E X n) :=
      (coefficientSequenceEvaluation_exact l E X n).1
    let hEvalXC : PreservesFiniteColimits (coefficientSequenceEvaluation l E X n) :=
      (coefficientSequenceEvaluation_exact l E X n).2
    let hEvalUA : (coefficientSequenceEvaluation l E U n).Additive :=
      coefficientSequenceEvaluation_additive l E U n
    let hEvalUL : PreservesFiniteLimits (coefficientSequenceEvaluation l E U n) :=
      (coefficientSequenceEvaluation_exact l E U n).1
    let hEvalUC : PreservesFiniteColimits (coefficientSequenceEvaluation l E U n) :=
      (coefficientSequenceEvaluation_exact l E U n).2
    let hIntrinsicA : (proEtaleConstantRingPullback
        (Padic.coefficientExtensionRing l E (n + 1)) j).Additive :=
      proEtaleRingModulePullback_additive j _ _ _
    let hIntrinsicL : PreservesFiniteLimits (proEtaleConstantRingPullback
        (Padic.coefficientExtensionRing l E (n + 1)) j) :=
      proEtaleRingModulePullback_preservesFiniteLimits j _ _ _
    let hIntrinsicC : PreservesFiniteColimits (proEtaleConstantRingPullback
        (Padic.coefficientExtensionRing l E (n + 1)) j) :=
      proEtaleRingModulePullback_preservesFiniteColimits j _ _ _
    let hFinA : (IntegralOpenReduction.finiteRestriction l E j C.operations n).Additive :=
      Functor.additive_of_iso
        (F := proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1)) j)
        (G := IntegralOpenReduction.finiteRestriction l E j C.operations n) (ρ n).symm
    let hFinL : PreservesFiniteLimits
        (IntegralOpenReduction.finiteRestriction l E j C.operations n) :=
      preservesFiniteLimits_of_natIso
        (F := proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1)) j)
        (G := IntegralOpenReduction.finiteRestriction l E j C.operations n) (ρ n).symm
    let hFinC : PreservesFiniteColimits
        (IntegralOpenReduction.finiteRestriction l E j C.operations n) :=
      preservesFiniteColimits_of_natIso
        (F := proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1)) j)
        (G := IntegralOpenReduction.finiteRestriction l E j C.operations n) (ρ n).symm
    let K' : (IntegralOpenReduction.complete l E X).FullSubcategory :=
      ⟨K, (complete_iff l E X K).mp hc⟩
    let α := ((C.openSite.reductionEvaluation n).app
        ((IntegralOpenReduction.star l E j C.operations).obj K)).symm ≪≫
      (coefficientSequenceDerivedEvaluation l E U n).mapIso (C.completeOpen.s.app K') ≪≫
      (@Functor.mapDerivedCategorySquareIso _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (IntegralOpenReduction.systemRestriction l E j C.operations)
        (coefficientSequenceEvaluation l E U n) (coefficientSequenceEvaluation l E X n)
        (IntegralOpenReduction.finiteRestriction l E j C.operations n)
        hSysResA hSysResL hSysResC hEvalUA hEvalUL hEvalUC
        hEvalXA hEvalXL hEvalXC hFinA hFinL hFinC
        (restrictionEvaluation l E j C.operations n)).app (C.ambient.reduction.obj K) ≪≫
      (IntegralOpenReduction.finiteRestriction l E j C.operations n).mapDerivedCategory.mapIso
        ((C.ambient.reductionEvaluation n).app K) ≪≫
      (@Functor.mapDerivedCategoryNatIso _ _ _ _ _ _ _ _
        (IntegralOpenReduction.finiteRestriction l E j C.operations n)
        (proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1)) j)
        hFinA hIntrinsicA hFinL hFinC hIntrinsicL hIntrinsicC (ρ n)).app
        ((scalarReductionDerivedExtension l E X n).obj K)
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let F := proEtaleConstantRingPullback A j
    let R := (scalarReductionDerivedExtension l E X n).obj K
    have hs : proEtaleCohomologicalSupport (F.mapDerivedCategory.obj R) ⊆
        proEtaleCohomologicalSupport R := by
      intro i hi hz
      exact hi ((F.map_isZero hz).of_iso
        ((F.mapDerivedCategoryHomologyFunctorIso i).symm.app R))
    have hF : intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_le_succ n.zero_le) U (F.mapDerivedCategory.obj R) := by
      refine ⟨(hred n).1.1.subset hs, fun i ↦ ?_⟩
      exact constructible_of_iso A ((F.mapDerivedCategoryHomologyFunctorIso i).symm.app R)
        (pullback_constructible A j _ ((hred n).1.2 i))
    exact finiteProperties_iso l E U n α.symm a b hF (hs.trans (hred n).2)
  refine ⟨fun n ↦ ⟨ι n⟩, ?_, ?_, ?_, ?_⟩
  · intro K hK
    refine ⟨(complete_iff l E X _).mpr
      (C.completeOpen.extensionComplete ⟨K, (complete_iff l E U K).mp hK.1⟩), ?_⟩
    obtain ⟨a, b, hab, hred⟩ := hK.2
    exact ⟨a, b, hab, hext K hK.1 a b hab hred⟩
  · intro K hK
    refine ⟨(complete_iff l E U _).mpr
      (C.completeOpen.restrictionComplete ⟨K, (complete_iff l E X K).mp hK.1⟩), ?_⟩
    obtain ⟨a, b, hab, hred⟩ := hK.2
    exact ⟨a, b, hab, hres K hK.1 a b hred⟩
  · intro K a b hK hab hs n
    obtain ⟨a', b', _, hred⟩ := hK.2
    exact (hext K hK.1 a b hab (fun n ↦ ⟨(hred n).1, hs n⟩) n).2
  · intro K a b hK _hab hs n
    obtain ⟨a', b', _, hred⟩ := hK.2
    exact (hres K hK.1 a b (fun n ↦ ⟨(hred n).1, hs n⟩) n).2

end WeilConjectures.OpenTensorQuotient
