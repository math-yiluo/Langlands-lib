/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement

import all WeilConjectures.SmoothPurity.Sf.SfCompleteDirectImageReduction
import all WeilConjectures.SmoothPurity.Sf.SfIntegralDirectImageConstructible
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import all WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import Mathlib.FieldTheory.Finite.Basic
import all WeilConjectures.AlgebraicGeometry.Compact.CompactSupportUniformTorBound
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSquareExchange
import WeilConjectures.AlgebraicGeometry.FibreDimension
import all WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeSystemTransition
import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSupportScalarComparison
import all WeilConjectures.SmoothPurity.Compact.CompactSupportFiniteAction

/-! # Single-operation bounds for completed compact support

Source: Stacks 0941, 0F10 and 0F7J; the common-bound argument in
lem-sf-completed-shriek-composition-laws, steps 7 and 8.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem intrinsic_of_iso (W : Scheme.{u}) (n : ℕ)
    {P Q : proEtaleDerivedCategory W (Padic.coefficientExtensionRing l E (n + 1))}
    (e : P ≅ Q)
    (hP : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W P) :
    intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W Q := by
  have : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  constructor
  · apply hP.1.subset
    intro i hi
    exact fun hz ↦ hi (hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e).symm)
  · intro i
    exact intrinsicConstructible_of_iso W _
      ((DerivedCategory.homologyFunctor _ i).mapIso e) (hP.2 i)

private theorem completedPush_constructible (k : Type u) [Field k]
    (hk : IsUnit (l : k)) {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (K : Integral l E X)
    (hK : sfIntegralConstructible l E X K) :
    sfIntegralConstructible l E Y ((sfCompletedDerivedDirectImage l E f).obj K) := by
  classical
  have h := sfIntegralDirectImage_constructible k l hk E f K hK
  obtain ⟨hp, ⟨L⟩⟩ := h.1
  let := hp
  obtain ⟨N, hN⟩ := h.2.2.1
  obtain ⟨a, b, hab, hlevels⟩ := hK.2
  obtain ⟨p, _, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hprime⟩
  obtain ⟨D⟩ := CompletedCoefficientPushforward.comparison l E f p (by omega)
  refine ⟨completed_image_complete l E f D K hK.1, a, max a (b + N),
    le_max_left _ _, ?_⟩
  intro n
  have hi := sf_projection_formula l E f n K
  let e := (asIso (sf_projection_map l E f n K)).symm
  refine ⟨intrinsic_of_iso l E Y n e ((h.2.1 L).2.2.2 n), ?_⟩
  intro i hi
  have hs : i ∈ proEtaleCohomologicalSupport (sfFiniteDerivedDirectImage l E f K n) :=
    fun hz ↦ hi (hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e).symm)
  have hb := h.2.2.2.1 N hN a b (fun m ↦ (hlevels m).2) n hs
  exact ⟨hb.1, hb.2.trans (le_max_right _ _)⟩

private def ringedPushIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ringedPush l E f ≅ sfCompletedDerivedDirectImage l E f := by
  have hc : proEtaleRingDirectImageMap f
      (completedIntegralCommRingSheafUnrestricted l E Y)
      (completedIntegralCommRingSheafUnrestricted l E X)
      (asIso (PurCompactSupport.completedPullMap l E f)) = sfCompletedCoefficientMap l E f := by
    change (proEtaleSheafAdjunction f CommRingCat).homEquiv _ _
      (((proEtaleSheafAdjunction f CommRingCat).homEquiv _ _).symm
        (sfCompletedCoefficientMap l E f)) = _
    exact Equiv.apply_symm_apply _ _
  have hm : proEtaleRingModuleDirectImage f
      ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.completed l E).pull f) = sfCompletedModuleDirectImage l E f := by
    unfold proEtaleRingModuleDirectImage sfCompletedModuleDirectImage
    erw [hc]
  have : (sfCompletedModuleDirectImage l E f).Additive := by
    rw [← hm]
    infer_instance
  exact Functor.rightDerivedFunctorNatIso (eqToIso hm)

private theorem integral_of_iso (W : Scheme.{u}) {K L : Integral l E W} (e : K ≅ L)
    (hK : sfIntegralConstructible l E W K) : sfIntegralConstructible l E W L := by
  refine ⟨complete_iso l E W e hK.1, ?_⟩
  obtain ⟨a, b, hab, hs⟩ := hK.2
  refine ⟨a, b, hab, fun n ↦ ?_⟩
  let en := (scalarReductionDerivedExtension l E W n).mapIso e
  refine ⟨intrinsic_of_iso l E W n en (hs n).1, ?_⟩
  intro i hi
  exact (hs n).2 (fun hz ↦ hi
    (hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso en).symm))

private theorem primeUnit (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) :
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

private theorem push_levelBounds (k : Type u) [Field k] (hk : IsUnit (l : k))
    (o : Operations l E) {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]
    (M : System l E X) (hM : LevelBounds l E X M) :
    LevelBounds l E Y ((Operations.push l E o f).obj M) := by
  classical
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  obtain ⟨r, hr⟩ := exists_topologicalKrullDim_le_of_isPullback_of_compactSpace f
  obtain ⟨a, b, c, d, hab, hcd, hlevels⟩ := hM
  refine ⟨c, d + 2 * (r : ℤ), c, d + 2 * (r : ℤ), by omega, by omega, ?_⟩
  intro n
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  have : HasInvertibleExponent (ULift.{u + 1, u} A) (Spec (.of k)) := by
    refine ⟨l ^ (n + 1), pow_pos (Fact.out : l.Prime).pos _, coefficient_killed l E _, ?_⟩
    simpa only [map_pow, map_natCast, Nat.cast_pow] using
      (hk.pow (n + 1)).map (Scheme.ΓSpecIso (.of k)).inv.hom
  let P := (coefficientSequenceDerivedEvaluation l E X n).obj M
  have hP : ProEtale.spFiniteConstructibleTor X A P := by
    refine ⟨⟨a, b, hab, ?_⟩, (hlevels n).1.2, c, d, (hlevels n).2.2⟩
    intro i hi
    by_contra hz
    have hb := (hlevels n).2.1 hz
    rcases hb with ⟨hba, hbb⟩
    rcases hi with hi | hi <;> omega
  have : QuasiCompact (Compactification.ofIsProper f).i :=
    inferInstanceAs (QuasiCompact (𝟙 X))
  have hb := ProEtale.finite_bound k A X Y f (Compactification.ofIsProper f) r
    (fun y ↦ hr _ _ _ _ (IsPullback.of_hasPullback _ _)) c d hcd P hP
      (hlevels n).2.2
  let e := (ProEtale.compact_coordinates A (Compactification.ofIsProper f)).app P ≪≫
    (proEtaleConstantDerivedDirectImage f A).mapIso
      ((sfIntrinsicDerivedOpenId A X).app P) ≪≫
    ((o.evaluation f).evaluation n).symm.app M
  have hs : proEtaleCohomologicalSupport
      ((coefficientSequenceDerivedEvaluation l E Y n).obj
        ((Operations.push l E o f).obj M)) ⊆ Set.Icc c (d + 2 * (r : ℤ)) := by
    intro i hi
    have hz : ¬ IsZero ((DerivedCategory.homologyFunctor _ i).obj _) :=
      fun hz ↦ hi (hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e).symm)
    by_contra hout
    exact hz (hb.2.2 i (by simpa only [Set.mem_Icc, not_and_or, not_le] using hout))
  refine ⟨⟨Set.Finite.subset (Set.finite_Icc _ _) hs, ?_⟩, hs,
    ProEtale.tor_of_iso Y A e hb.2.1⟩
  intro i
  exact intrinsicConstructible_of_iso Y A
    ((DerivedCategory.homologyFunctor _ i).mapIso e) (hb.1.2.1 i)

private theorem origins_of_levelBounds (W : Scheme.{u}) (M : System l E W)
    (hM : LevelBounds l E W M) : Nonempty (Origins l E W M) := by
  classical
  let A := fun n : ℕ ↦ Padic.coefficientExtensionRing l E (n + 1)
  let (n : ℕ) : Finite (A n) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let C := fun n : ℕ ↦ ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (A n))) W
  let R := fun n : ℕ ↦ (sfIntrinsicModuleEquivalence W (A n)).functor
  obtain ⟨a, b, c, d, hab, hcd, hs⟩ := hM
  have horigin (n : ℕ) : ∃ K :
      (Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1, u} (A n)) W).FullSubcategory,
      Nonempty ((ProEtale.finiteCoefficientIntrinsicDerivedComparison W (A n)).obj K.obj ≅
        (coefficientSequenceDerivedEvaluation l E W n).obj M) := by
    apply (finiteRing_constructibleDerived_origin W (A n)).2.2.1 _ |>.mpr
    refine ⟨(hs n).1.2, a, b, hab, ?_⟩
    intro i hi
    by_contra hz
    have hb := (hs n).2.1 hz
    rcases hb with ⟨hba, hbb⟩
    rcases hi with hi | hi <;> omega
  choose K hK using horigin
  let Kplus (n : ℕ) : DerivedCategory.Plus
      (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} (A n)))) :=
    ⟨(K n).obj, by
      obtain ⟨s, t, _, ht⟩ := (K n).property.2
      exact ⟨s, (DerivedCategory.isGE_iff _ s).2 (fun i hi ↦ ht i (.inl hi))⟩⟩
  let levels (n : ℕ) : DerivedCategory.Plus
      (Sheaf (ProEt.topology W) (ModuleCat.{u + 1} (ULift.{u + 1, u} (A n)))) :=
    ⟨(C n).mapDerivedCategory.obj (K n).obj, by
      obtain ⟨s, ht⟩ := (Kplus n).property
      let := ht
      exact ⟨s, (C n).isGE_mapDerivedCategory_obj _ s⟩⟩
  let origin (n : ℕ) : Nonempty (FixedEtaleOriginWitness W
      (ULift.{u + 1, u} (A n)) (levels n)) :=
    ⟨⟨Kplus n, Iso.refl _⟩⟩
  let ev (n : ℕ) : (R n).mapDerivedCategory.obj (levels n).obj ≅
      (coefficientSequenceDerivedEvaluation l E W n).obj M :=
    (Functor.mapDerivedCategoryCompIso (C n) (R n)).app (K n).obj ≪≫ (hK n).some
  let res (n : ℕ) := Sheaf.derivedRestrictScalars (ProEt.topology W)
    (RingHom.ulift.{u + 1, u + 1, u, u}
      (Padic.coefficientExtensionTransition l E (n + 1)))
  let (n : ℕ) := normalizedDVRModuleRes_limits l E W (Nat.le_succ n)
  let (n : ℕ) := normalizedDVRModuleRes_colimits l E W (Nat.le_succ n)
  let cmp (n : ℕ) : (R (n + 1)).mapDerivedCategory.obj ((res n).obj (levels n).obj) ≅
      (normalizedDVRRes l E W (Nat.le_succ n)).obj
        ((R n).mapDerivedCategory.obj (levels n).obj) :=
    (Functor.mapDerivedCategorySquareIso (sfRealizationRestriction W
      (Padic.coefficientExtensionTransition l E (n + 1)))).symm.app (levels n).obj ≪≫
    (Functor.mapDerivedCategoryNatIso (eqToIso (originRestrictionEquality l E W n))).app _
  let trans (n : ℕ) : (levels (n + 1)).obj ⟶ (res n).obj (levels n).obj :=
    (R (n + 1)).mapDerivedCategory.preimage
      ((ev (n + 1)).hom ≫
        (coefficientSequenceDerivedTransition l E W (Nat.le_succ n)).app M ≫
        (normalizedDVRRes l E W (Nat.le_succ n)).map (ev n).inv ≫ (cmp n).inv)
  have het (n : ℕ) : ∃ t : (Classical.choice (origin (n + 1))).complex.obj ⟶
      (Sheaf.derivedRestrictScalars W.smallEtaleTopology
        (RingHom.ulift.{u + 1, u + 1, u, u}
      (Padic.coefficientExtensionTransition l E (n + 1)))).obj
          (Classical.choice (origin n)).complex.obj,
      (C (n + 1)).mapDerivedCategory.map t =
        (Classical.choice (origin (n + 1))).iso.hom ≫ trans n ≫
        (res n).map (Classical.choice (origin n)).iso.inv ≫
        (ProEtale.pbcDerivedComparisonRestrict W
          (RingHom.ulift.{u + 1, u + 1, u, u}
      (Padic.coefficientExtensionTransition l E (n + 1)))).hom.app
            (Classical.choice (origin n)).complex.obj := by
    let T := Sheaf.restrictScalars W.smallEtaleTopology
      (RingHom.ulift.{u + 1, u + 1, u, u}
      (Padic.coefficientExtensionTransition l E (n + 1)))
    have ht : DerivedCategory.TStructure.t.plus
        (T.mapDerivedCategory.obj (Classical.choice (origin n)).complex.obj) := by
      obtain ⟨s, hs⟩ := (Classical.choice (origin n)).complex.property
      let := hs
      exact ⟨s, T.isGE_mapDerivedCategory_obj _ s⟩
    exact (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map _ _ ht).2 _
  choose et het using het
  refine ⟨{
    level := levels
    origin := origin
    evaluation := ev
    fixedTransition := trans
    etaleTransition := et
    originSquare := ?_
    transitionSquare := ?_ }⟩
  · intro n
    change (C (n + 1)).mapDerivedCategory.map (et n) ≫ _ ≫ _ = _
    rw [het n]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    change _ ≫ trans n ≫ (res n).map _ ≫ (res n).map _ = _
    rw [← (res n).map_comp, Iso.inv_hom_id, (res n).map_id, Category.comp_id]
  · intro n
    change (R (n + 1)).mapDerivedCategory.map (trans n) ≫ _ ≫ _ = _
    dsimp only [trans]
    rw [Functor.map_preimage]
    have hc := (cmp n).inv_hom_id
    simpa only [cmp, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Category.assoc,
      Category.comp_id] using
      congrArg (fun t ↦ (ev (n + 1)).hom ≫
        (coefficientSequenceDerivedTransition l E W (Nat.le_succ n)).app M ≫
        (normalizedDVRRes l E W (Nat.le_succ n)).map (ev n).inv ≫ t) hc

private theorem normalized_iso (W : Scheme.{u})
    {A B : coefficientSequenceDerived l E W} (e : A ≅ B)
    (hA : IsNormalizedCoefficientSequence l E W A) :
    IsNormalizedCoefficientSequence l E W B := by
  intro m n h P
  let en := (coefficientSequenceDerivedEvaluation l E W n).mapIso e
  let em := (coefficientSequenceDerivedEvaluation l E W m).mapIso e
  let G := normalizedDVRRes l E W h
  have hn := (coefficientSequenceDerivedTransition l E W h).naturality e.hom
  change em.hom ≫ (coefficientSequenceDerivedTransition l E W h).app B =
    (coefficientSequenceDerivedTransition l E W h).app A ≫ G.map en.hom at hn
  constructor
  · intro x y hxy
    apply (cancel_epi en.hom).1
    apply (hA h P).injective
    change (coefficientSequenceDerivedTransition l E W h).app A ≫ G.map (en.hom ≫ x) =
      (coefficientSequenceDerivedTransition l E W h).app A ≫ G.map (en.hom ≫ y)
    change (coefficientSequenceDerivedTransition l E W h).app B ≫ G.map x =
      (coefficientSequenceDerivedTransition l E W h).app B ≫ G.map y at hxy
    simp only [G.map_comp, ← Category.assoc, ← hn]
    simpa only [Category.assoc] using congrArg (fun k ↦ em.hom ≫ k) hxy
  · intro t
    obtain ⟨s, hs⟩ := (hA h P).surjective (em.hom ≫ t)
    refine ⟨en.inv ≫ s, ?_⟩
    apply (cancel_epi em.hom).1
    change em.hom ≫ (coefficientSequenceDerivedTransition l E W h).app B ≫
      G.map (en.inv ≫ s) = em.hom ≫ t
    rw [G.map_comp, ← Category.assoc, hn]
    simp only [Category.assoc, ← G.map_comp, Iso.hom_inv_id_assoc]
    exact hs

private def nativePushIso (o : Operations l E) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Operations.push l E o f ≅ ProEtale.VaryingRing.P
      (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) f := by
  let R := compactSupportSystemLevel l E
  let q := compactSupportSystemQuotient l E
  have he : pullbackTensorSequenceDirect l E f = ProEtale.VaryingRing.push R q f := by
    unfold pullbackTensorSequenceDirect
    rw [pullbackTensorSequenceRing_eq]
    rfl
  let ep := (((pullbackTensorSequenceAdjunction l E f).ofNatIsoRight (eqToIso he))).leftAdjointUniq
    (ProEtale.VaryingRing.moduleAdj R q f)
  let : (ProEtale.VaryingRing.pull R q f).Additive :=
    ProEtale.VaryingRing.pullAdditive R q f
  let : PreservesFiniteLimits (ProEtale.VaryingRing.pull R q f) :=
    ProEtale.VaryingRing.pullLimits R q f
  let : PreservesFiniteColimits (ProEtale.VaryingRing.pull R q f) :=
    ProEtale.VaryingRing.pullColimits R q f
  let ed := Functor.mapDerivedCategoryNatIso ep
  exact ((o.direct f).adj.ofNatIsoLeft ed).rightAdjointUniq
    (ProEtale.VaryingRing.adj R q f)

private theorem normalized_directTransition (W : Scheme.{u})
    (M : System l E W) (hM : IsNormalizedCoefficientSequence l E W M)
    {m n : ℕ} (h : n ≤ m) (P : normalizedDVRDerived l E W n) :
    Function.Bijective (fun g : (coefficientSequenceDerivedEvaluation l E W n).obj M ⟶ P ↦
      (compactSupportCoefficientTransition l E W h).app M ≫
        (pbcDerivedRestrict (compactSupportLevelSheafQuotient l E W m n h)).map g) := by
  let ε := finiteRestrictionIso l E W h
  have he : (fun g : (coefficientSequenceDerivedEvaluation l E W n).obj M ⟶ P ↦
      (compactSupportCoefficientTransition l E W h).app M ≫
        (pbcDerivedRestrict (compactSupportLevelSheafQuotient l E W m n h)).map g) =
      (fun z ↦ z ≫ ε.hom.app P) ∘
        (fun g ↦ (coefficientSequenceDerivedTransition l E W h).app M ≫
          (normalizedDVRRes l E W h).map g) := by
    funext g
    have hn := ε.hom.naturality g
    dsimp only [Function.comp_apply]
    rw [Category.assoc, hn, ← Category.assoc]
    exact congrArg (fun d ↦ d ≫
      (pbcDerivedRestrict (compactSupportLevelSheafQuotient l E W m n h)).map g)
      (NatTrans.congr_app (derivedTransition_direct l E W h) M).symm
  rw [he]
  have hb : Function.Bijective (fun z :
      (coefficientSequenceDerivedEvaluation l E W m).obj M ⟶
        (normalizedDVRRes l E W h).obj P ↦ z ≫ ε.hom.app P) := by
    constructor
    · intro x y hxy
      exact (cancel_mono (ε.hom.app P)).1 hxy
    · intro t
      refine ⟨t ≫ ε.inv.app P, ?_⟩
      simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  exact hb.comp (hM h P)

private theorem nativePush_normalized
    (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
    {X Y : Scheme.{u}} [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of K₀))] [IsProper f]
    (M : System l E X) (hM : Good l E X M) :
    IsNormalizedCoefficientSequence l E Y
      ((ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) (Compactification.ofIsProper f).i ⋙
        ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) (Compactification.ofIsProper f).g).obj M) := by
  let c := Compactification.ofIsProper f
  classical
  let N : coefficientSequenceDerived.{u, u} l E Y :=
    (ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) c.i ⋙
    ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.g).obj M
  let F (n : ℕ) := sfIntrinsicCompactSupport c
    (Padic.coefficientExtensionRing l E (n + 1))
  let L (n : ℕ) := (coefficientSequenceDerivedEvaluation l E X n).obj M
  let e (n : ℕ) : (coefficientSequenceDerivedEvaluation.{u, u} l E Y n).obj N ≅
      (F n).obj (L n) :=
    (compactSupportSystemEvaluation l E c n).app M
  obtain ⟨a, b, c₀, d₀, hab, hcd, hK⟩ := hM.2.1
  intro m n h P
  let Rx := pbcDerivedRestrict (compactSupportLevelSheafQuotient l E X m n h)
  let Ry := pbcDerivedRestrict (compactSupportLevelSheafQuotient l E Y m n h)
  let ax := pbcDerivedScalarAdjunction (compactSupportLevelSheafQuotient l E X m n h)
  let ay := pbcDerivedScalarAdjunction (compactSupportLevelSheafQuotient l E Y m n h)
  let β := (ax.homEquiv _ _).symm ((compactSupportCoefficientTransition l E X h).app M)
  have hβ : IsIso β := by
    apply (isIso_iff_coyoneda_map_bijective β).2
    intro P
    have hb := ((ax.homEquiv _ P).symm.bijective).comp
      (normalized_directTransition l E X M hM.1 h P)
    simpa only [Function.comp_def, β, Adjunction.homEquiv_naturality_right_symm] using hb
  let := hβ
  have hred : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X
      ((pbcDerivedExtend (compactSupportLevelSheafQuotient l E X m n h)).obj (L m)) :=
    finiteConstructible_iso l E X n (asIso β).symm (hK n).1
  let τ := (F m).map ((compactSupportCoefficientTransition l E X h).app M) ≫
    (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app (L n)
  let q := (ay.homEquiv _ _).symm τ
  let z := (ay.homEquiv _ _).symm ((F m).map (ax.unit.app (L m)) ≫
    (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app
      ((pbcDerivedExtend (compactSupportLevelSheafQuotient l E X m n h)).obj (L m)))
  have hz : IsIso z := finiteCompactSupportScalarComparison l E K₀ hl
    (m + 1) (Nat.succ_pos m) (n + 1) (Nat.succ_pos n) (Nat.add_le_add_right h 1)
    f c (L m) (hK m).1 hred
  let := hz
  have hτ : τ = ((F m).map (ax.unit.app (L m)) ≫
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app
        ((pbcDerivedExtend (compactSupportLevelSheafQuotient l E X m n h)).obj (L m))) ≫
      Ry.map ((F n).map β) := by
    have hn := (sfCompactSupportRestriction c
      (compactSupportLevelQuotient l E m n h)).hom.naturality β
    change (F m).map (Rx.map β) ≫
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app (L n) =
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app
        ((pbcDerivedExtend (compactSupportLevelSheafQuotient l E X m n h)).obj (L m)) ≫
        Ry.map ((F n).map β) at hn
    change (F m).map ((compactSupportCoefficientTransition l E X h).app M) ≫
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app
        (L n) = _
    rw [Category.assoc, ← hn, ← Category.assoc, ← (F m).map_comp]
    exact congrArg (fun d ↦ (F m).map d ≫
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app (L n))
      (by simpa only [Adjunction.homEquiv_unit] using
        ((ax.homEquiv _ _).apply_symm_apply
          ((compactSupportCoefficientTransition l E X h).app M)).symm)
  have hqeq : q = z ≫ (F n).map β :=
    (congrArg ((ay.homEquiv _ _).symm) hτ).trans
      (ay.homEquiv_naturality_right_symm _ _)
  have hq : IsIso q := by rw [hqeq]; infer_instance
  let := hq
  have ht : (compactSupportCoefficientTransition l E Y h).app N ≫ Ry.map (e n).hom =
      (e m).hom ≫ τ := by
    have hg := compactSupportNativeSystemTransition l E c h M
    simpa only [N, τ, L, e, F, Ry, pbcDerivedRestrict, pbcRestrict,
      compactSupportLevelSheafQuotient, Iso.app_hom, Category.assoc] using hg
  let qN := (ay.homEquiv _ _).symm ((compactSupportCoefficientTransition l E Y h).app N)
  have hqN : qN ≫ (e n).hom =
      (pbcDerivedExtend (compactSupportLevelSheafQuotient l E Y m n h)).map (e m).hom ≫ q := by
    calc
      qN ≫ (e n).hom = (ay.homEquiv _ _).symm
          ((compactSupportCoefficientTransition l E Y h).app N ≫ Ry.map (e n).hom) :=
        (ay.homEquiv_naturality_right_symm _ _).symm
      _ = (ay.homEquiv _ _).symm ((e m).hom ≫ τ) := congrArg _ ht
      _ = (pbcDerivedExtend (compactSupportLevelSheafQuotient l E Y m n h)).map
          (e m).hom ≫ q := ay.homEquiv_naturality_left_symm _ _
  have : IsIso (qN ≫ (e n).hom) := by rw [hqN]; infer_instance
  have : IsIso qN := IsIso.of_isIso_comp_right qN (e n).hom
  have hb : Function.Bijective (fun g :
      (coefficientSequenceDerivedEvaluation.{u, u} l E Y n).obj N ⟶ P ↦
      (compactSupportCoefficientTransition l E Y h).app N ≫ Ry.map g) := by
    have hb := ((ay.homEquiv _ P).bijective).comp
      ((isIso_iff_coyoneda_map_bijective qN).mp inferInstance P)
    simpa only [Function.comp_def, qN, Adjunction.homEquiv_naturality_right,
      Equiv.apply_symm_apply] using hb
  let ε := finiteRestrictionIso l E Y h
  have he : (fun g : (coefficientSequenceDerivedEvaluation.{u, u} l E Y n).obj N ⟶ P ↦
      (compactSupportCoefficientTransition l E Y h).app N ≫ Ry.map g) =
      (fun z ↦ z ≫ ε.hom.app P) ∘
        (fun g ↦ (coefficientSequenceDerivedTransition.{u, u} l E Y h).app N ≫
          (normalizedDVRRes l E Y h).map g) := by
    funext g
    have hn := ε.hom.naturality g
    dsimp only [Function.comp_apply]
    rw [Category.assoc, hn, ← Category.assoc]
    exact congrArg (fun d ↦ d ≫ Ry.map g) (NatTrans.congr_app
      (derivedTransition_direct l E Y h) N).symm
  rw [he] at hb
  exact Function.Bijective.of_comp_left (f := fun z ↦ z ≫ ε.hom.app P) hb
    (fun a b hab ↦ (cancel_mono (ε.hom.app P)).mp hab)

/-- One proper letter preserves the system domain and integral constructibility.
Source: Stacks 0F10, 0941; parent proof steps 7 and 8
(blueprint: lem-sf-proper-support-step-bounds).

Proof: choose a uniform relative fibre-dimension bound for the proper morphism.
The finite-ring compact-support bound with identity open gives constructibility and
common cohomology and Tor intervals, which the specified evaluation transports to
the system image. The existing bound needs no separatedness of the structure maps.
Identify the specified system image with the native varying-ring image by uniqueness
of adjoints. Input normalization makes every scalar-adjoint quotient transition an
isomorphism. Finite compact-support scalar comparison and the native coefficient
transition square then make the output quotient adjunct an isomorphism, which is
exactly output normalization. At each output level choose a bounded etale origin;
full faithfulness lifts the actual transitions and proves both compatibility squares.
For the independent integral input, identify the ringed image with the canonical
completed direct image. Integral direct-image constructibility, completeness of
completed direct image, and its reduction isomorphisms give the assertion. -/
theorem properSupportStep_bounds (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) {X Y : Over (Spec (CommRingCat.of D.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsProper f.left] (M : System l E X.left)
    (hM : Good l E X.left M) (K : Integral l E X.left)
    (hK : sfIntegralConstructible l E X.left K) :
    Good l E Y.left ((Operations.push l E o f.left).obj M) ∧
      sfIntegralConstructible l E Y.left ((ringedPush l E f.left).obj K) := by
  let : LocallyOfFiniteType (X.left ↘ Spec (.of D.k)) := inferInstanceAs
    (LocallyOfFiniteType X.hom)
  let : QuasiCompact (X.left ↘ Spec (.of D.k)) := inferInstanceAs (QuasiCompact X.hom)
  let : LocallyOfFiniteType (Y.left ↘ Spec (.of D.k)) := inferInstanceAs
    (LocallyOfFiniteType Y.hom)
  let : QuasiCompact (Y.left ↘ Spec (.of D.k)) := inferInstanceAs (QuasiCompact Y.hom)
  refine ⟨?_, ?_⟩
  · have hb := push_levelBounds l E D.k (primeUnit l D hl) o f.left M hM.2.1
    refine ⟨?_, hb, origins_of_levelBounds l E Y.left _ hb⟩
    let R := compactSupportSystemLevel l E
    let q := compactSupportSystemQuotient l E
    let ep : ProEtale.VaryingRing.J R q (𝟙 X.left) ⋙
        ProEtale.VaryingRing.P R q f.left ≅ Operations.push l E o f.left :=
      Functor.isoWhiskerRight (ProEtale.VaryingRing.jId R q X.left) _ ≪≫
        Functor.leftUnitor _ ≪≫ (nativePushIso l E o f.left).symm
    apply normalized_iso l E Y.left (ep.app M)
    exact nativePush_normalized l E D.k (primeUnit l D hl) f.left M hM
  · exact integral_of_iso l E Y.left ((ringedPushIso l E f.left).symm.app K)
      (completedPush_constructible l E D.k (primeUnit l D hl) f.left K hK)

end WeilConjectures.IntegralSystemRealization
