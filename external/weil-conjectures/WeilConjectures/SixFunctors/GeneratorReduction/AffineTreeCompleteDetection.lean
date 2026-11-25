/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionOrdinaryModels
public import WeilConjectures.AlgebraicGeometry.QcqsOpenClosedTree.Path.QcqsOpenClosedTree
import all WeilConjectures.SixFunctors.IntegralOnSlice.QcqsOrdinaryRestrictionExact
import all WeilConjectures.SixFunctors.IntegralOnSlice.QcqsOrdinaryQuotientRestriction
import all WeilConjectures.SixFunctors.IntegralOnSlice.QcqsOrdinaryRestrictionModels
import all WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionUnitRestriction
import all WeilConjectures.SixFunctors.IntegralOnSlice.QcqsOrdinaryLocalDetection
import all WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionUnitTree
import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionUnitCriterion
import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionComparisonDescent

import WeilConjectures.SixFunctors.IntegralOnSlice.OrdinaryQuotientModuleComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleImmersionAlgebraicLimitsOfUniverses
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedPullbackUnderlyingOfUniverses
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import Mathlib.CategoryTheory.Sites.LocalProperties

/-! # Affine and finite open--closed detection of integral completeness

Source: Bhatt--Scholze, Lemma 6.5.8; Stacks Tags 099M, 09BL and 09BM.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.scalarReductionSourceDerived
  WeilConjectures.scalarReductionTargetDerived
  WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local instance 3000] WeilConjectures.integralTowerHasDerivedCategory
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
  AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures.IntegralOnSlice

-- The construction of the restriction models does not require qcqs on the target.
private theorem restrictionLimits
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {S V T : Scheme.{t}}
    (s : S ⟶ V) (i : V ⟶ T) [WeaklyEtale s] [IsImmersion i] :
    PreservesLimitsOfSize.{0, 0} (ordinaryPull l E (s ≫ i)) ∧
    IsIso (ordinaryCoefficientMap l E (s ≫ i)) := by
  let hf := abelianPush_isRightAdjoint.{t, u} s
  let hg := abelianPush_isRightAdjoint.{t, u} i
  let hc := abelianPush_isRightAdjoint.{t, u} (s ≫ i)
  let Bf := (abelianPush.{t, u} s).leftAdjoint
  let Bg := (abelianPush.{t, u} i).leftAdjoint
  let B := (abelianPush.{t, u} (s ≫ i)).leftAdjoint
  let af := Adjunction.ofIsRightAdjoint (abelianPush.{t, u} s)
  let ag := Adjunction.ofIsRightAdjoint (abelianPush.{t, u} i)
  let a := Adjunction.ofIsRightAdjoint (abelianPush.{t, u} (s ≫ i))
  let rf := Adjunction.ofIsRightAdjoint (ordinaryRingPush.{t, u} s)
  let rg := Adjunction.ofIsRightAdjoint (ordinaryRingPush.{t, u} i)
  let rc := Adjunction.ofIsRightAdjoint (ordinaryRingPush.{t, u} (s ≫ i))
  obtain ⟨hRg, hBg⟩ := proEtale_immersion_algebraicInverse_limits i
    (ordinaryRingInverse.{t, u} i) rg Bg ag
  let := hRg
  let := hBg
  let := weaklyEtale_limits s (ordinaryRingInverse.{t, u} s) rf
  let := weaklyEtale_limits s Bf af
  let := composite_limits s i (ordinaryRingInverse.{t, u} s) rf
    (ordinaryRingInverse.{t, u} i) rg (ordinaryRingInverse.{t, u} (s ≫ i)) rc
  let := composite_limits s i Bf af Bg ag B a
  have hcoeff := ordinaryCoefficientMap_isIso_of_preservesLimits l E (s ≫ i)
  let := hcoeff
  let R := completedIntegralCoefficientSheafUnrestricted l E T
  let A := completedIntegralCoefficientSheafUnrestricted l E S
  let F := ordinaryPull l E (s ≫ i)
  have : IsIso ((rc.homEquiv R A).symm (ordinaryCompletedRingMap l E (s ≫ i))) :=
    hcoeff
  obtain ⟨e⟩ := proEtale_ringedPullback_underlying_of_isIso (s ≫ i)
    (ordinaryRingInverse.{t, u} (s ≫ i)) rc B a R A
    (ordinaryCompletedRingMap l E (s ≫ i)) F (ordinaryAdjunction l E (s ≫ i))
  let := moduleForget_limits R
  let := moduleForget_limits A
  let V := SheafOfModules.toSheaf.{max u (t + 1)} A
  let : ReflectsLimitsOfSize.{0, 0} V := reflectsLimits_of_reflectsIsomorphisms
  let : PreservesLimitsOfSize.{0, 0} (F ⋙ V) := preservesLimits_of_natIso e.symm
  exact ⟨preservesLimits_of_reflects_of_preserves F V, hcoeff⟩

attribute [local irreducible] ordinaryPull ordinaryDerivedPull ordinaryComplexCounit
  ordinaryCoefficientMap tower completion completionComparison completionUnit

private theorem restrictionExact
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {S V T : Scheme.{t}} (s : S ⟶ V) (i : V ⟶ T)
    [WeaklyEtale s] [IsImmersion i] :
    PreservesFiniteLimits (ordinaryPull l E (s ≫ i)) ∧
      PreservesFiniteColimits (ordinaryPull l E (s ≫ i)) := by
  have := (restrictionLimits l E s i).1
  have : PreservesColimitsOfSize.{0, 0} (ordinaryPull l E (s ≫ i)) :=
    (ordinaryAdjunction l E (s ≫ i)).leftAdjoint_preservesColimits
  exact ⟨inferInstance, inferInstance⟩

attribute [local semireducible] tower in
private theorem restrictionUnit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {S V T : Scheme.{t}} (s : S ⟶ V) (i : V ⟶ T)
    [WeaklyEtale s] [IsImmersion i] (H : D l E T none) :
    IsIso ((ordinaryDerivedPull l E (s ≫ i)).map
        ((completionUnit l E T none).app H)) ↔
      IsIso ((completionUnit l E S none).app
        ((ordinaryDerivedPull l E (s ≫ i)).obj H)) := by
  have hlimits := (restrictionLimits l E s i).1
  have hc := (restrictionLimits l E s i).2
  let := hc
  obtain ⟨hlim, hcol⟩ := restrictionExact l E s i
  choose e he using fun n ↦ (ordinaryQuotientModuleComparison l E (s ≫ i) n).exists
  let τ := quotientTowerIso l E (s ≫ i) e he
  have haug := quotientLevelIso_augmentation l E (s ≫ i) e he
  obtain ⟨χ, hfst, hsnd⟩ := restrictionRoosModels (ordinaryPull l E (s ≫ i))
    (tower l E T none) (tower l E S none) τ
  have hgood := ordinaryPull_good l E (s ≫ i)
  obtain ⟨α, hα⟩ := ordinaryCompletionComparison_exists l E (s ≫ i) χ hgood
  have hu := ordinaryCompletionComparison_unit l E (s ≫ i) τ χ (fun P n ↦ haug n P) hfst hsnd
    hgood α hα H
  have hh := isIso_comp_right_iff
    ((ordinaryDerivedPull l E (s ≫ i)).map ((completionUnit l E T none).app H))
    (α.hom.app H)
  rw [hu] at hh
  exact hh.symm

private theorem coverReflects
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (S : Scheme.{t}) {I : Type t} (W : I → S.ProEt)
    (htop : (ProEt.topology S).CoversTop W) :
    JointlyReflectIsomorphisms (fun a ↦ ordinaryPull l E (W a).hom) := by
  constructor
  intro M N f hf
  let F := SheafOfModules.toSheaf (completedIntegralCoefficientSheafUnrestricted l E S)
  let (a : I) : (MorphismProperty.Over.map ⊤ (W a).prop).IsContinuous
      (ProEt.topology (W a).left) (ProEt.topology S) :=
    ProEt.isContinuous_overMap (W a).prop
  let R (a : I) := (MorphismProperty.Over.map ⊤ (W a).prop).sheafPushforwardContinuous
    AddCommGrpCat.{max u (t + 1)} (ProEt.topology (W a).left) (ProEt.topology S)
  have hr (a : I) : IsIso ((R a).map (F.map f)) := by
    let g : (W a).left ⟶ S := (W a).hom
    let : WeaklyEtale g := (W a).prop
    let : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).IsContinuous
        (ProEt.topology S) (ProEt.topology (W a).left) :=
      ProEt.isContinuous_overPullback g
    let L := ordinaryRingInverse.{t, u} g
    let aL := Adjunction.ofIsRightAdjoint (ordinaryRingPush.{t, u} g)
    have hlim := weaklyEtale_limits g L aL
    have hc := ordinaryCoefficientMap_isIso_of_preservesLimits l E g
    have hc' : IsIso ((aL.homEquiv
        (completedIntegralCoefficientSheafUnrestricted l E S)
        (completedIntegralCoefficientSheafUnrestricted l E (W a).left)).symm
          (ordinaryCompletedRingMap l E g)) := by
      simpa only [ordinaryCoefficientMap, aL] using hc
    let aB := (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
      (W a).prop trivial).sheafPushforwardContinuous
        (E := AddCommGrpCat.{max u (t + 1)})
        (ProEt.topology (W a).left) (ProEt.topology S)
    obtain ⟨e⟩ := proEtale_ringedPullback_underlying_of_isIso g L aL (R a) aB
      (completedIntegralCoefficientSheafUnrestricted l E S)
      (completedIntegralCoefficientSheafUnrestricted l E (W a).left)
      (ordinaryCompletedRingMap l E g) (ordinaryPull l E g) (ordinaryAdjunction l E g)
    have hfa : IsIso ((ordinaryPull l E g).map f) := hf a
    have hi : IsIso ((ordinaryPull l E g ⋙ SheafOfModules.toSheaf
        (completedIntegralCoefficientSheafUnrestricted l E (W a).left)).map f) :=
      by
        change IsIso ((SheafOfModules.toSheaf _).map ((ordinaryPull l E g).map f))
        infer_instance
    exact (NatIso.isIso_map_iff e f).mp hi
  have hlocal (a : I) (T : Over (W a)) :
      IsIso ((F.map f).hom.app (op T.left)) := by
    let := hr a
    let := ProEt.weaklyEtale_slice S (W a) T
    let V : (W a).left.ProEt := ProEt.mk T.hom.left
    have hi : IsIso (((R a).map (F.map f)).hom.app (op V)) := inferInstance
    change IsIso ((F.map f).hom.app
      (op ((MorphismProperty.Over.map ⊤ (W a).prop).obj V))) at hi
    let e : (MorphismProperty.Over.map ⊤ (W a).prop).obj V ≅ T.left :=
      MorphismProperty.Over.isoMk (Iso.refl _) (by
        change (𝟙 T.left.left) ≫ T.left.hom = T.hom.left ≫ (W a).hom
        simpa only [Category.id_comp] using (MorphismProperty.Over.w T.hom).symm)
    exact @NatTrans.isIso_app_of_iso _ _ _ _ _ _ (F.map f).hom _ _ e.op hi
  have : IsIso (F.map f) := by
    apply Sheaf.isIso_of_coversTop htop
    intro a
    rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
    intro T
    exact hlocal a T.unop
  exact isIso_of_reflects_iso f F

private theorem affineDetection
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{t}) {H K : D l E X none} (f : H ⟶ K)
    (h : ∀ (U : X.Opens), IsAffine U.toScheme →
      IsIso ((ordinaryDerivedPull l E U.ι).map f)) : IsIso f := by
  let W (U : X.affineOpens) : X.ProEt := ProEt.mk U.val.ι
  have hcover : Presieve.ofArrows W
      (fun a ↦ (MorphismProperty.Over.homMk (W a).hom (Category.comp_id _) :
        W a ⟶ ProEt.mk (𝟙 X))) ∈ ProEt.precoverage X (ProEt.mk (𝟙 X)) := by
    rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    exact ((X.openCoverOfIsOpenCover (fun U : X.affineOpens ↦ U.val)
      (iSup_affineOpens_eq_top X)).weaken
        (zariskiPrecoverage_le_propQCPrecoverage (P := @WeaklyEtale))).mem₀
  have htop : (ProEt.topology X).CoversTop W := by
    intro V
    let q : V ⟶ ProEt.mk (𝟙 X) :=
      MorphismProperty.Over.homMk V.hom (Category.comp_id _)
    apply (ProEt.topology X).superset_covering _
      ((ProEt.topology X).pullback_stable q (Precoverage.generate_mem_toGrothendieck hcover))
    intro Z b hb
    change (Sieve.ofArrows W (fun a ↦
      (MorphismProperty.Over.homMk (W a).hom (Category.comp_id _) :
        W a ⟶ ProEt.mk (𝟙 X)))) (b ≫ q) at hb
    exact Sieve.ofArrows_le_ofObjects W _ (b ≫ q) hb
  have hlim (U : X.affineOpens) : PreservesFiniteLimits (ordinaryPull l E (W U).hom) := by
    have h := (restrictionExact l E (𝟙 U.val.toScheme) U.val.ι).1
    change PreservesFiniteLimits (ordinaryPull l E U.val.ι)
    exact (congrArg (fun r ↦ PreservesFiniteLimits (ordinaryPull l E r))
      (Category.id_comp U.val.ι)) ▸ h
  have hcol (U : X.affineOpens) : PreservesFiniteColimits (ordinaryPull l E (W U).hom) := by
    have h := (restrictionExact l E (𝟙 U.val.toScheme) U.val.ι).2
    change PreservesFiniteColimits (ordinaryPull l E U.val.ι)
    exact (congrArg (fun r ↦ PreservesFiniteColimits (ordinaryPull l E r))
      (Category.id_comp U.val.ι)) ▸ h
  exact ordinaryExactJoint (fun U ↦ ordinaryPull l E (W U).hom)
    (coverReflects l E X W htop) f (fun U ↦
      (NatIso.isIso_map_iff (ordinaryExactComparison l E (W U).hom) f).mp
        (h U.val U.property))

private theorem finiteChartCover
    (S : Scheme.{t}) [CompactSpace S] [QuasiSeparatedSpace S]
    (c : ℕ) (A : Fin c → S.ProEt)
    (hc : ∀ a, CompactSpace (A a).left)
    (hq : ∀ a, QuasiSeparatedSpace (A a).left)
    (hs : ∀ x : S, ∃ a, x ∈ Set.range (A a).hom.base) :
    Presieve.ofArrows A
      (fun a ↦ (MorphismProperty.Over.homMk (A a).hom (Category.comp_id _) :
        A a ⟶ ProEt.mk (𝟙 S))) ∈ ProEt.precoverage S (ProEt.mk (𝟙 S)) := by
  let (a : Fin c) : CompactSpace (A a).left := hc a
  let (a : Fin c) : QuasiSeparatedSpace (A a).left := hq a
  rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
  let V : PreZeroHypercover S := ⟨Fin c, fun a ↦ (A a).left, fun a ↦ (A a).hom⟩
  have hV : QuasiCompactCover V :=
    ⟨fun {O} hO ↦ IsCompactOpenCovered.of_finite_of_isSpectralMap
      (fun a ↦ (V.f a).isSpectralMap) (fun x _ ↦ hs x) O.2 hO.isCompact⟩
  exact ⟨presieve₀_mem_qcPrecoverage_iff.mpr hV,
    (Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).mpr
      ⟨hs, fun a ↦ by
        change WeaklyEtale (A a).hom
        infer_instance⟩⟩

private theorem restrictionMapIso_congr
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {S T : Scheme.{t}} {r s : S ⟶ T} (h : r = s)
    {H K : D l E T none} (f : H ⟶ K) :
    IsIso ((ordinaryDerivedPull l E r).map f) ↔
      IsIso ((ordinaryDerivedPull l E s).map f) := by
  cases h
  exact Iff.rfl

private theorem treeQcqs {S : Scheme.{t}} (tree : QcqsOpenClosedTree S) :
    CompactSpace S ∧ QuasiSeparatedSpace S := by
  cases tree <;> exact ⟨inferInstance, inferInstance⟩

private theorem treeDetection
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{t}) [CompactSpace T] [QuasiSeparatedSpace T]
    {H K : D l E T none} (f : H ⟶ K)
    {S : Scheme.{t}} (tree : QcqsOpenClosedTree S) :
    ∀ (r : S ⟶ T) [IsImmersion r],
      (∀ (L : Scheme.{t}) (p : tree.Path L), p.IsLeaf → Nonempty L →
        ∃ (c : ℕ) (A : Fin c → L.ProEt),
          (∀ a, CompactSpace (A a).left) ∧
          (∀ a, QuasiSeparatedSpace (A a).left) ∧
          (∀ x : L, ∃ a, x ∈ Set.range (A a).hom.base) ∧
          ∀ a, IsIso ((ordinaryDerivedPull l E ((A a).hom ≫ p.toRoot ≫ r)).map f)) →
      IsIso ((ordinaryDerivedPull l E r).map f) := by
  induction tree with
  | leaf S =>
    intro r _ h
    by_cases hn : Nonempty S
    · let := hn
      obtain ⟨c, A, hc, hq, hs, hi⟩ := h S (.root _) trivial hn
      apply ((qcqsOrdinaryLocalDetection.{t, u, 0} l E T f).2.2 S r (Fin c) A hc hq
        (finiteChartCover S c A hc hq hs)).mpr
      intro a
      exact (restrictionMapIso_congr l E
        (show (A a).hom ≫ (QcqsOpenClosedTree.Path.root
          (QcqsOpenClosedTree.leaf S)).toRoot ≫ r = (A a).hom ≫ r by
          exact congrArg ((A a).hom ≫ ·) (Category.id_comp r)) f).mp (hi a)
    · have : IsEmpty S := ⟨fun x ↦ hn ⟨x⟩⟩
      exact emptyDerived_isIso l E S _
  | @split S U Z _ _ j i _ _ _ _ hc a b iha ihb =>
    intro r _ h
    obtain ⟨hU, hUq⟩ := treeQcqs a
    obtain ⟨hZ, hZq⟩ := treeQcqs b
    apply ((qcqsOrdinaryLocalDetection.{t, u, 0} l E T f).2.1 S U Z r j i
      (by rw [hc]; exact Set.compl_union_self _) (by rw [hc]; exact disjoint_compl_left)).mpr
    constructor
    · apply iha (j ≫ r)
      intro L p hp hn
      obtain ⟨c, A, hA, hq, hs, hi⟩ := h L (.openBranch j i hc a b p) hp hn
      refine ⟨c, A, hA, hq, hs, ?_⟩
      intro k
      exact (restrictionMapIso_congr l E
        (congrArg ((A k).hom ≫ ·) (Category.assoc p.toRoot j r)) f).mp (hi k)
    · apply ihb (i ≫ r)
      intro L p hp hn
      obtain ⟨c, A, hA, hq, hs, hi⟩ := h L (.closedBranch j i hc a b p) hp hn
      refine ⟨c, A, hA, hq, hs, ?_⟩
      intro k
      exact (restrictionMapIso_congr l E
        (congrArg ((A k).hom ≫ ·) (Category.assoc p.toRoot i r)) f).mp (hi k)

private theorem pathImmersion {T L : Scheme.{t}} {tree : QcqsOpenClosedTree T}
    (p : tree.Path L) : IsImmersion p.toRoot := by
  induction p with
  | root => exact inferInstanceAs (IsImmersion (𝟙 _))
  | @openBranch X U Z W _ _ j i _ _ _ _ h a b p ih =>
    let := ih
    change IsImmersion (p.toRoot ≫ j)
    infer_instance
  | @closedBranch X U Z W _ _ j i _ _ _ _ h a b p ih =>
    let := ih
    change IsImmersion (p.toRoot ≫ i)
    infer_instance

private theorem compositeRestrictionIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {S V T X : Scheme.{t}} (s : S ⟶ V) (i : V ⟶ T) (j : T ⟶ X)
    [WeaklyEtale s] [IsImmersion i] [IsImmersion j]
    {H K : D l E X none} (f : H ⟶ K) :
    IsIso ((ordinaryDerivedPull l E (s ≫ i ≫ j)).map f) ↔
      IsIso ((ordinaryDerivedPull l E (s ≫ i)).map
        ((ordinaryDerivedPull l E j).map f)) := by
  obtain ⟨hsl, hsc⟩ := restrictionExact l E s i
  have hj := restrictionExact l E (𝟙 T) j
  simp only [Category.id_comp] at hj
  obtain ⟨hjl, hjc⟩ := hj
  have hcomp := restrictionExact l E s (i ≫ j)
  rw [← Category.assoc] at hcomp
  obtain ⟨hcl, hcc⟩ := hcomp
  obtain ⟨e⟩ := ordinaryExactComp l E (s ≫ i) j
  exact (restrictionMapIso_congr l E (Category.assoc s i j).symm f).trans
    (NatIso.isIso_map_iff e f)

end WeilConjectures.IntegralOnSlice

namespace WeilConjectures.GeneratorReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Completeness can be detected on finite pro-etale covers of the leaves of a
finite constructible tree on every affine open. The object is arbitrary; it need
not be constructible, bounded, or a tensor product.

Source: Bhatt--Scholze, Lemma 6.5.8 and Remark 6.5.10;
Stacks Tags 099M, 09BL and 09BM, canonical quotient-completion locality.
(blueprint: lem-sf-affine-tree-complete-detection).

Proof: use invertibility of the canonical quotient-completion unit to test
completeness. Affine open restriction preserves products, finite quotient tensors,
transitions and the quotient augmentation, so it commutes with this unit. On each
finite tree, quasi-compact open and constructible closed inverse images also
preserve these operations, with the coefficient ring identified by its actual
finite limit projections. On a leaf, exact pro-etale restriction identifies every
cohomology sheaf of the unit cone with its restriction. The given finite family
covers on points and has qcqs domains, hence is a pro-etale covering and detects
vanishing of all those cohomology sheaves. On an empty leaf all sheaves are zero.
At an internal vertex the open--closed exact sequence makes its two restrictions
jointly conservative. Induction up the finite tree therefore gives invertibility
of the unit on that affine open. Affine opens cover the scheme, so exact sheaf
restriction and the cohomology criterion give its invertibility globally. Convert
back with the canonical-unit criterion. This argument imposes no invertibility of
ell on the scheme: it uses only completed coefficient rings and constructible
restriction, and it includes height-zero trees and the empty scheme. -/
theorem affineTreeCompleteDetection (X : Scheme.{t})
    (H : IntegralOnSlice.D.{t, u} l E X none)
    (h : ∀ (U : X.Opens), IsAffine U.toScheme →
      ∃ tree : QcqsOpenClosedTree U.toScheme,
        ∀ (S : Scheme.{t}) (p : tree.Path S), p.IsLeaf → Nonempty S →
          ∃ (c : ℕ) (A : Fin c → S.ProEt),
            (∀ i, CompactSpace (A i).left) ∧
            (∀ i, QuasiSeparatedSpace (A i).left) ∧
            (∀ x : S, ∃ i, x ∈ Set.range (A i).hom.base) ∧
            ∀ i : Fin c, IntegralOnSlice.IsComplete.{t, u} l E (A i).left none
              ((IntegralOnSlice.ordinaryDerivedPull.{t, u} l E
                ((A i).hom ≫ p.toRoot ≫ U.ι)).obj H)) :
    IntegralOnSlice.IsComplete.{t, u} l E X none H := by
  apply (IntegralOnSlice.canonicalCompletionUnitCriterion l E X H).mp
  apply IntegralOnSlice.affineDetection l E X
  intro U hU
  let : IsAffine U.toScheme := hU
  obtain ⟨tree, ht⟩ := h U hU
  let f := (IntegralOnSlice.ordinaryDerivedPull l E U.ι).map
    ((IntegralOnSlice.completionUnit l E X none).app H)
  apply ((IntegralOnSlice.qcqsOrdinaryLocalDetection.{t, u, 0} l E U.toScheme f).1
    U.toScheme (𝟙 U.toScheme)).mp
  apply IntegralOnSlice.treeDetection l E U.toScheme f tree (𝟙 U.toScheme)
  intro S p hp hn
  obtain ⟨c, A, hc, hq, hs, hA⟩ := ht S p hp hn
  refine ⟨c, A, hc, hq, hs, ?_⟩
  intro a
  have : IsImmersion p.toRoot := IntegralOnSlice.pathImmersion p
  have hu := (IntegralOnSlice.restrictionUnit l E (A a).hom (p.toRoot ≫ U.ι) H).mpr
    ((IntegralOnSlice.canonicalCompletionUnitCriterion l E (A a).left _).mpr (hA a))
  have hi := (IntegralOnSlice.compositeRestrictionIso l E (A a).hom p.toRoot U.ι
    ((IntegralOnSlice.completionUnit l E X none).app H)).mp hu
  exact (IntegralOnSlice.restrictionMapIso_congr l E
    (congrArg ((A a).hom ≫ ·) (Category.comp_id p.toRoot)).symm f).mp hi

end WeilConjectures.GeneratorReduction
