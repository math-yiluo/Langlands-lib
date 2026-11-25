/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorCoherenceData
public import WeilConjectures.SixFunctors.OpenTensorQuotient.OpenTensorQuotientAugmentation
public import WeilConjectures.SixFunctors.OpenRoos.OpenRoosUnitAdjunction
import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorOrdinaryTransport
import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorQuotientRealization
import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorPullRealization
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import all WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData

/-! # Open-factor data in the fixed coefficient presentation

Source: blueprint proposition-composition-base-change-rf-shriek--1, open-factor paragraph;
Bhatt--Scholze 3.4.10, 6.5.5, 6.5.8; Stacks 099N, 09BN, 0GL1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.IntegralOnSlice.abSheafify
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.PurCompactSupport
namespace WeilConjectures.OpenFactorCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem reflector_commutes
    {A B : Type*} [Category A] [Category B]
    (L : A ⥤ B) (R : B ⥤ A) (adj : L ⊣ R)
    (F : A ⥤ A) (η : 𝟭 A ⟶ F) (P : A → Prop)
    (G : B ⥤ B) (ε : 𝟭 B ⟶ G) (Q : B → Prop)
    (hF : ∀ X, P (F.obj X)) (hG : ∀ X, Q (G.obj X))
    (hA : ∀ X Y, P Y → Function.Bijective (fun f : F.obj X ⟶ Y ↦ η.app X ≫ f))
    (hB : ∀ X Y, Q Y → Function.Bijective (fun f : G.obj X ⟶ Y ↦ ε.app X ≫ f))
    (hL : ∀ X, P X → Q (L.obj X)) (hR : ∀ Y, Q Y → P (R.obj Y)) :
    ∃ d : L ⋙ G ≅ F ⋙ L, ∀ X, ε.app (L.obj X) ≫ d.hom.app X = L.map (η.app X) := by
  classical
  have hJ (X : A) (Y : B) (hY : Q Y) :
      Function.Bijective (fun f : L.obj (F.obj X) ⟶ Y ↦ L.map (η.app X) ≫ f) := by
    have hh := (adj.homEquiv X Y).symm.bijective.comp
      ((hA X (R.obj Y) (hR Y hY)).comp (adj.homEquiv (F.obj X) Y).bijective)
    have he : (fun f : L.obj (F.obj X) ⟶ Y ↦ L.map (η.app X) ≫ f) =
        (adj.homEquiv X Y).symm ∘ (fun f ↦ η.app X ≫ f) ∘
          adj.homEquiv (F.obj X) Y := by
      funext f
      apply (adj.homEquiv X Y).injective
      simp only [Function.comp_apply, Equiv.apply_symm_apply]
      exact adj.homEquiv_naturality_left (η.app X) f
    rw [he]
    exact hh
  let s (X : A) := ((hB (L.obj X) (L.obj (F.obj X)) (hL _ (hF X))).surjective
    (L.map (η.app X))).choose
  have hs (X : A) : ε.app (L.obj X) ≫ s X = L.map (η.app X) :=
    ((hB (L.obj X) (L.obj (F.obj X)) (hL _ (hF X))).surjective
      (L.map (η.app X))).choose_spec
  let t (X : A) := ((hJ X (G.obj (L.obj X)) (hG _)).surjective (ε.app (L.obj X))).choose
  have ht (X : A) : L.map (η.app X) ≫ t X = ε.app (L.obj X) :=
    ((hJ X (G.obj (L.obj X)) (hG _)).surjective (ε.app (L.obj X))).choose_spec
  let e (X : A) : G.obj (L.obj X) ≅ L.obj (F.obj X) :=
    { hom := s X
      inv := t X
      hom_inv_id := by
        apply (hB (L.obj X) _ (hG _)).injective
        dsimp only
        rw [← Category.assoc, hs, ht, Category.comp_id]
      inv_hom_id := by
        apply (hJ X _ (hL _ (hF X))).injective
        dsimp only
        rw [← Category.assoc, ht, hs, Category.comp_id] }
  let d : L ⋙ G ≅ F ⋙ L := NatIso.ofComponents e (by
    intro X Y f
    apply (hB (L.obj X) _ (hL _ (hF Y))).injective
    change ε.app (L.obj X) ≫ (G.map (L.map f) ≫ s Y) =
      ε.app (L.obj X) ≫ (s X ≫ L.map (F.map f))
    have hn := ε.naturality (L.map f)
    dsimp only [Functor.id_map] at hn
    rw [← Category.assoc, ← hn, Category.assoc, hs, ← Category.assoc, hs,
      ← L.map_comp, ← L.map_comp]
    exact congrArg L.map (η.naturality f))
  exact ⟨d, hs⟩

private theorem complete_iff_slice (F : FiniteFieldDatum.{u}) (hl : l ≠ F.p)
    (W : Scheme.{u}) (K : D l E W) :
    IsSfDerivedComplete l E W K ↔ IntegralOnSlice.IsComplete l E W none K := by
  constructor
  · intro hK
    have : Fact F.p.Prime := ⟨F.prime⟩
    let F₀ : FiniteFieldDatum.{0} :=
      { p := F.p
        a := 1
        q := F.p
        prime := F.prime
        exponent_pos := by decide
        cardinality_eq := by simp
        k₀ := ZMod F.p
        card_base := by simp [Nat.card_eq_fintype_card]
        k := AlgebraicClosure (ZMod F.p) }
    have hl₀ : l ≠ F₀.p := hl
    exact ⟨F₀, hl₀, (sfDerivedComplete_iff_legacy l E W F₀ hl₀ K).mp hK⟩
  · rintro ⟨G, hG, hK⟩
    exact (sfDerivedComplete_iff_legacy l E W G hG K).mpr hK

attribute [-instance] WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralReductionSiteEssentiallySmall
  SheafOfModules.localizedSystemExtensionAdditive SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived in
private theorem openUnit_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (openDerivedAdjunction (completed l E) j).unit := by
  obtain ⟨e, ⟨he⟩⟩ := openExtension_derivedSlicePresentation (completed l E) j
  let L := (SheafOfModules.localizedModuleExtension.{u} ((completed l E).ring X)
    (ProEt.mk j)).mapDerivedCategory
  let a := SheafOfModules.localizedModuleDerivedAdjunction.{u}
    ((completed l E).ring X) (ProEt.mk j)
  have : IsIso a.unit := SheafOfModules.localizedDerivedUnit_isIso j ((completed l E).ring X)
  have : L.Full := a.fullyFaithfulLOfIsIsoUnit.full
  have : L.Faithful := a.fullyFaithfulLOfIsIsoUnit.faithful
  have : (J l E j).Full := Functor.Full.of_iso he.symm
  have : (J l E j).Faithful := Functor.Faithful.of_iso he.symm
  exact (openDerivedAdjunction (completed l E) j).unit_isIso_of_L_fully_faithful

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived in
private theorem reduction_interval {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : D l E U) (n : ℕ) (a b : ℤ)
    (h : proEtaleCohomologicalSupport
      ((scalarReductionDerivedExtension l E U n).obj K) ⊆ Set.Icc a b) :
    proEtaleCohomologicalSupport ((scalarReductionDerivedExtension l E X n).obj
      ((J l E j).obj K)) ⊆ Set.Icc a b := by
  classical
  let A := Padic.coefficientExtensionRing l E (n + 1)
  have : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  let f := sfIntrinsicExtensionByZero j A
  let := sfIntrinsicExtensionByZero_additive j (Padic.coefficientExtensionRing l E (n + 1))
  let := sfIntrinsicExtensionByZero_preservesFiniteLimits j
    (Padic.coefficientExtensionRing l E (n + 1))
  let := sfIntrinsicExtensionByZero_preservesFiniteColimits j
    (Padic.coefficientExtensionRing l E (n + 1))
  let := proEtaleRingModules_hasDerivedCategory X (X.proEtaleConstantRing A)
  let := proEtaleRingModules_hasDerivedCategory U (U.proEtaleConstantRing A)
  let dFin : (openExtension (finite l E (n + 1) (Nat.le_add_left 1 n)) j).mapDerivedCategory ≅
      f.mapDerivedCategory :=
    @Functor.mapDerivedCategoryNatIso _ _ _ _ _ _ _ _ _ _
      (proEtaleRingOpenExtension_additive j
        ((finite l E (n + 1) (Nat.le_add_left 1 n)).ring X)
        ((finite l E (n + 1) (Nat.le_add_left 1 n)).ring U)
        ((finite l E (n + 1) (Nat.le_add_left 1 n)).pull j))
      (sfIntrinsicExtensionByZero_additive j A)
      (proEtaleRingOpenExtension_limits j
        ((finite l E (n + 1) (Nat.le_add_left 1 n)).ring X)
        ((finite l E (n + 1) (Nat.le_add_left 1 n)).ring U)
        ((finite l E (n + 1) (Nat.le_add_left 1 n)).pull j))
      (proEtaleRingOpenExtension_colimits j
        ((finite l E (n + 1) (Nat.le_add_left 1 n)).ring X)
        ((finite l E (n + 1) (Nat.le_add_left 1 n)).ring U)
        ((finite l E (n + 1) (Nat.le_add_left 1 n)).pull j))
      (sfIntrinsicExtensionByZero_preservesFiniteLimits j A)
      (sfIntrinsicExtensionByZero_preservesFiniteColimits j A) (finiteOpenIso l E n j)
  let d : (scalarReductionDerivedExtension l E X n).obj ((J l E j).obj K) ≅
      f.mapDerivedCategory.obj ((scalarReductionDerivedExtension l E U n).obj K) :=
    (finiteReductionIso l E X n).symm.app _ ≪≫
      (@asIso _ _ _ _
        ((openComparison (reduction l E (n + 1) (Nat.le_add_left 1 n)) j).app K)
        (openComparison_isIso (reduction l E (n + 1) (Nat.le_add_left 1 n)) j K)) ≪≫
      ((openExtension (finite l E (n + 1) (Nat.le_add_left 1 n)) j).mapDerivedCategory).mapIso
        ((finiteReductionIso l E U n).app K) ≪≫
      dFin.app _
  intro r hr
  by_contra hr'
  have hz : IsZero ((DerivedCategory.homologyFunctor _ r).obj
      ((scalarReductionDerivedExtension l E U n).obj K)) := by
    by_contra hn
    exact hr' (h hn)
  have hz' := (f.map_isZero hz).of_iso
    ((@DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2} _ _ _
      (proEtaleRingModules_hasDerivedCategory X (X.proEtaleConstantRing A)) r).mapIso d ≪≫
      ((f.mapDerivedCategoryHomologyFunctorIso r).app _).symm)
  exact hr hz'

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived in
/-- Transport the normalized slice open operations to the fixed completed coefficients.
Source: Stacks 099N(2),(5), 09BN and 0E8I; Bhatt--Scholze 6.5.8.
(blueprint: lem-sf-open-factor-open-realization).

Proof: the finite maps of o preserve constant sections and every quotient projection.
The completed projections are jointly monic, so o.completedMap is the fixed coefficient
map on the open slice. Transport the module equivalence through this identification;
the extension and restriction are then the published ringed open operations. The
scalar mate, applied termwise to complexes, gives tower and tower_unit, and tensor
generation gives tower_unique. Transported extension and restriction preserve
complete objects. The adjunction and the two reflector universal properties then
construct commutes and unit_commutes: the open extension of the source unit and
the target unit are both reflections into complete objects. Precomposition with
the target unit makes this comparison unique. The same strict quotient pullback
comparison gives Pull and its representative equation. Reflection and restriction
completeness make its unit invertible on complete inputs. The exact open adjunction's
unit is invertible; its inverse gives restrictionIso and section_unit, and its Hom
bijection gives fullyFaithful. Transport c.extensionComplete, c.restrictionComplete
and q.integralGeometry across the normalized identifications, using equivalence of
the two published Roos completeness predicates. The scalar comparison gives
reduction_iso. Finally the finite presentation comparison and exactness of intrinsic
open extension compute cohomology, giving interval for each individual n; this
also covers empty intervals without an assumption a ≤ b. Empty opens, identity
opens and zero complexes obey the same coefficient and unit formulas. -/
theorem openFactorOpenRealization
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (SX : CoefficientDerivedSystemCalculus l E X)
    (SU : CoefficientDerivedSystemCalculus l E U)
    (o : IntegralOpenReduction.Operations l E j)
    (st : IntegralOpenReduction.TensorComparison l E j o)
    (AX : OpenSemilinearTensor.OrdinaryReduction l E X)
    (AU : OpenSemilinearTensor.OrdinaryReduction l E U)
    (m : OpenSemilinearTensor.Comparison l E j o SX SU AX AU st)
    (c : IntegralOpenReduction.Comparison l E j o SX SU st)
    (q : OpenTensorQuotient.Comparison l E j o SX SU AX AU st m c)
    (F : FiniteFieldDatum.{u}) (hl : l ≠ F.p)
    [U.Over (Spec (.of F.k))] [X.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of F.k))] [QuasiCompact (U ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of F.k))] [QuasiCompact (X ↘ Spec (.of F.k))]
    [j.IsOver (Spec (.of F.k))]
    (rX : OpenRoos.ReflectorAssertions l E X) (rU : OpenRoos.ReflectorAssertions l E U) :
    Nonempty (Open l E j) := by
  classical
  obtain ⟨eJ₀, ⟨eP₀⟩⟩ := openFactorOrdinaryTransport l E j o
  let := proEtaleRingOpenExtension_additive j
    ((completed l E).ring X) ((completed l E).ring U) ((completed l E).pull j)
  let := proEtaleRingModulePullback_additive j
    ((completed l E).ring X) ((completed l E).ring U) ((completed l E).pull j)
  let := proEtaleRingOpenExtension_limits j
    ((completed l E).ring X) ((completed l E).ring U) ((completed l E).pull j)
  let := proEtaleRingOpenExtension_colimits j
    ((completed l E).ring X) ((completed l E).ring U) ((completed l E).pull j)
  let := proEtaleRingModulePullback_preservesFiniteLimits j
    ((completed l E).ring X) ((completed l E).ring U) ((completed l E).pull j)
  let := proEtaleRingModulePullback_preservesFiniteColimits j
    ((completed l E).ring X) ((completed l E).ring U) ((completed l E).pull j)
  let eJ : IntegralOpenReduction.shriek l E j o ≅ J l E j :=
    @Functor.mapDerivedCategoryNatIso _ _ _ _ _ _ _ _ _ _
      (Functor.additive_of_iso eJ₀.symm)
      (proEtaleRingOpenExtension_additive j
        ((completed l E).ring X) ((completed l E).ring U) ((completed l E).pull j))
      (preservesFiniteLimits_of_natIso eJ₀.symm)
      (preservesFiniteColimits_of_natIso eJ₀.symm)
      (proEtaleRingOpenExtension_limits j
        ((completed l E).ring X) ((completed l E).ring U) ((completed l E).pull j))
      (proEtaleRingOpenExtension_colimits j
        ((completed l E).ring X) ((completed l E).ring U) ((completed l E).pull j)) eJ₀
  let eP : IntegralOpenReduction.star l E j o ≅ star l E j :=
    @Functor.mapDerivedCategoryNatIso _ _ _ _ _ _ _ _ _ _
      (Functor.additive_of_iso eP₀.symm)
      (proEtaleRingModulePullback_additive j
        ((completed l E).ring X) ((completed l E).ring U) ((completed l E).pull j))
      (preservesFiniteLimits_of_natIso eP₀.symm)
      (preservesFiniteColimits_of_natIso eP₀.symm)
      (proEtaleRingModulePullback_preservesFiniteLimits j
        ((completed l E).ring X) ((completed l E).ring U) ((completed l E).pull j))
      (proEtaleRingModulePullback_preservesFiniteColimits j
        ((completed l E).ring X) ((completed l E).ring U) ((completed l E).pull j)) eP₀
  obtain ⟨t, ht, htu⟩ :=
    openFactorQuotientRealization l E j SX SU o st AX AU m c q
  obtain ⟨p⟩ := openFactorPullRealization l E j
  have huX (K : D l E X) : IsSfDerivedComplete l E X K ↔ IsIso ((eta l E X).app K) :=
    (complete_iff_slice l E F hl X K).trans (rX.2.2.1 K)
  have huU (K : D l E U) : IsSfDerivedComplete l E U K ↔ IsIso ((eta l E U).app K) :=
    (complete_iff_slice l E F hl U K).trans (rU.2.2.1 K)
  have hext (K : D l E U) (hK : IsSfDerivedComplete l E U K) :
      IsSfDerivedComplete l E X ((J l E j).obj K) := by
    have hc := c.extensionComplete ⟨K, (complete_iff_slice l E F hl U K).mp hK⟩
    have hi := (rX.2.2.1 _).mp hc
    exact (huX _).mpr ((NatTrans.isIso_app_iff_of_iso (eta l E X) (eJ.app K)).mp hi)
  have hres (K : D l E X) (hK : IsSfDerivedComplete l E X K) :
      IsSfDerivedComplete l E U ((star l E j).obj K) := by
    have hc := c.restrictionComplete ⟨K, (complete_iff_slice l E F hl X K).mp hK⟩
    have hi := (rU.2.2.1 _).mp hc
    exact (huU _).mpr ((NatTrans.isIso_app_iff_of_iso (eta l E U) (eP.app K)).mp hi)
  have hJ (K : D l E U) (hK : OpenRoos.Intrinsic l E U K) :
      OpenRoos.Intrinsic l E X ((J l E j).obj K) :=
    (rX.2.2.2 _).mp ((huX _).mp (hext K ((huU K).mpr ((rU.2.2.2 _).mpr hK))))
  have hP (K : D l E X) (hK : OpenRoos.Intrinsic l E X K) :
      OpenRoos.Intrinsic l E U ((star l E j).obj K) :=
    (rU.2.2.2 _).mp ((huU _).mp (hres K ((huX K).mpr ((rX.2.2.2 _).mpr hK))))
  obtain ⟨d, hd⟩ := reflector_commutes (J l E j) (star l E j)
    (openDerivedAdjunction (completed l E) j)
    (C l E U) (eta l E U) (OpenRoos.Intrinsic l E U)
    (C l E X) (eta l E X) (OpenRoos.Intrinsic l E X)
    rU.1 rX.1 rU.2.1 rX.2.1 hJ hP
  have : IsIso (openDerivedAdjunction (completed l E) j).unit := openUnit_isIso l E j
  let ff := (openDerivedAdjunction (completed l E) j).fullyFaithfulLOfIsIsoUnit
  refine ⟨{
    tower := t
    tower_unit := ht
    tower_unique := htu
    commutes := d
    unit_commutes := hd
    commutes_unique := ?_
    restriction_complete := hres
    extension_complete := hext
    pull := p
    pull_unit := ?_
    restrictionIso := (asIso (openDerivedAdjunction (completed l E) j).unit).symm
    section_unit := ?_
    fullyFaithful := fun K L _ _ ↦ ff.map_bijective K L
    constructible := fun K hK ↦ (sfIntegralConstructible l E X).prop_of_iso
      (eJ.app K) (q.integralGeometry.1 K hK)
    restriction_constructible := fun K hK ↦ (sfIntegralConstructible l E U).prop_of_iso
      (eP.app K) (q.integralGeometry.2.1 K hK)
    reduction_iso := fun K n _ ↦ openComparison_isIso
      (reduction l E (n + 1) (Nat.le_add_left 1 n)) j K
    interval := fun K n a b _ h ↦ reduction_interval l E j K n a b h }⟩
  · intro v hv
    apply NatTrans.ext
    funext K
    have hc : IntegralOnSlice.IsComplete l E U none ((C l E U).obj K) :=
      (rU.2.2.1 _).mpr ((rU.2.2.2 _).mpr (rU.1 K))
    have he : OpenRoos.Intrinsic l E X ((J l E j).obj ((C l E U).obj K)) :=
      (rX.2.2.2 _).mp ((huX _).mp (hext _ ((complete_iff_slice l E F hl U _).mpr hc)))
    apply (rX.2.1 ((J l E j).obj K) _ he).injective
    exact (hv K).trans (hd K).symm
  · intro K hK
    change IsIso ((eta l E U).app ((star l E j).obj K) ≫ p.comparison.hom.app K)
    exact IsIso.comp_isIso' ((huU _).mp (hres K hK))
      (NatIso.hom_app_isIso p.comparison K)
  · intro K
    change (asIso (openDerivedAdjunction (completed l E) j).unit).hom.app K ≫
      (asIso (openDerivedAdjunction (completed l E) j).unit).inv.app K =
        𝟙 ((𝟭 (D l E U)).obj K)
    exact (asIso (openDerivedAdjunction (completed l E) j).unit).hom_inv_id_app K

end WeilConjectures.OpenFactorCoherence
