/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodOrdinaryQuotientTransitionCubeAux
import all WeilConjectures.TraceFormula.Integral.IntegralTowerInverseImageUnit
import all WeilConjectures.TraceFormula.Coherent.CoherentQuotientOrdinaryLift
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import all WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement

/-! # Ordinary quotient cube: the reindexing comparison

Helpers for `podOrdinaryQuotientTransitionCube`: relabelling along an isomorphism commutes with
ordinary limits of quotient systems, and the generator-normalized reindexing comparison of
ordinary quotient tensors.

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL, 06YY, 0941
(blueprint: lem-pod-ordinary-quotient-transition-cube).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

namespace OrdinaryQuotientCube


/-- The relabelling functor along an isomorphism has the base-change pushforward as a right
adjoint, whose unit restricts along the counit of the site adjunction. -/
theorem isoInverseAdjunction_exists {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (RY : Sheaf (ProEt.topology Y) RingCat.{u + 1})
    (RX : Sheaf (ProEt.topology X) RingCat.{u + 1})
    (c : (isoSectionwiseInverseImage g RingCat.{u + 1}).obj RY ⟶ RX)
    [IsIso c] :
    ∃ a : isoSectionwiseModuleInverseImage.{u, u} g c ⊣
      SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange g)
        (((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
          (inferInstance : WeaklyEtale g) trivial).sheafPushforwardContinuous
            (E := RingCat.{u + 1}) (ProEt.topology X) (ProEt.topology Y)).unit.app RY ≫
          (proEtaleSheafDirectImage g RingCat.{u + 1}).map c),
      ∀ (M : SheafOfModules.{u + 1} RY) (U : Y.ProEtᵒᵖ) (x : M.val.obj U),
        (a.unit.app M).val.app U x =
          M.val.map ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
            (inferInstance : WeaklyEtale g) trivial).counit.app U.unop).op x := by
  let F := proEtaleIsoPostcompose g
  let G := proEtaleBaseChange g
  let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
    (inferInstance : WeaklyEtale g) trivial
  let shAdj := adj.sheafPushforwardContinuous (E := RingCat.{u + 1})
    (ProEt.topology X) (ProEt.topology Y)
  let φ := inv c
  let ψ := shAdj.unit.app RY ≫ (proEtaleSheafDirectImage g RingCat.{u + 1}).map c
  have H₁ : Functor.whiskerRight (NatTrans.op adj.counit) RY.obj =
      ψ.hom ≫ G.op.whiskerLeft φ.hom := by
    ext U : 2
    simp [ψ, φ, shAdj, proEtaleSheafDirectImage, ProEtale.lowerStar, G,
      proEtaleBaseChange]
  have H₂ : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op adj.unit) RX.obj = 𝟙 RX.obj := by
    have hh : φ ≫ (F.sheafPushforwardContinuous RingCat _ _).map ψ ≫
        shAdj.counit.app RX = 𝟙 RX := by
      dsimp only [ψ]
      simp only [Functor.map_comp, Category.assoc]
      erw [shAdj.counit.naturality c]
      have ht := shAdj.left_triangle_components RY
      calc
        _ = φ ≫ ((F.sheafPushforwardContinuous RingCat _ _).map
            (shAdj.unit.app RY) ≫ shAdj.counit.app
              ((F.sheafPushforwardContinuous RingCat _ _).obj RY)) ≫ c := by
          simp only [Category.assoc, Functor.id_map]
          rfl
        _ = φ ≫ 𝟙 _ ≫ c := congrArg (fun h ↦ φ ≫ h ≫ c) ht
        _ = _ := by simp [φ]
    exact congrArg (fun f ↦ f.hom) hh
  exact ⟨SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂, fun _ _ _ ↦ rfl⟩

section GenericPush
variable {C D : Type*} [Category C] [Category D] {J : GrothendieckTopology C}
  {K : GrothendieckTopology D} (F : C ⥤ D) [F.IsContinuous J K]

/-- Restricting scalars after a pushforward is the pushforward along the composite ring map. -/
def pushforwardRestrictIso {S T : Sheaf J RingCat.{a}} {R : Sheaf K RingCat.{a}}
    (φ : T ⟶ (F.sheafPushforwardContinuous RingCat.{a} J K).obj R) (p : S ⟶ T) :
    SheafOfModules.pushforward.{b} φ ⋙ SheafOfModules.restrictScalars p ≅
      SheafOfModules.pushforward (p ≫ φ) :=
  Iso.refl _

end GenericPush

variable {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]

/-- The site adjunction between relabelling along `g` and base change. -/
abbrev siteAdj : proEtaleIsoPostcompose g ⊣ proEtaleBaseChange g :=
  MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g (inferInstance : WeaklyEtale g) trivial

/-- The completed coefficient map of the right adjoint of relabelling. -/
abbrev reindexRightRing :=
  ((siteAdj g).sheafPushforwardContinuous (E := RingCat.{u + 1}) (ProEt.topology X)
      (ProEt.topology Y)).unit.app (completedIntegralCoefficientSheafUnrestricted l E Y) ≫
    (proEtaleSheafDirectImage g RingCat.{u + 1}).map (isoReductionCompletedMap l E g).hom

/-- The right adjoint of relabelling completed modules along `g`. -/
abbrev completedPush : scalarReductionSource l E X ⥤ scalarReductionSource l E Y :=
  SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange g) (reindexRightRing l E g)

/-- The composite of a slice inclusion and sequence base change is continuous. -/
instance reindexSiteContinuous₁ (n : ℕ) :
    (Prod.sectR n Y.ProEt ⋙ integralComparisonSequenceBaseChange g).IsContinuous
      (ProEt.topology Y) (coefficientSequenceTopology (ProEt.topology X)) :=
  Functor.isContinuous_comp _ _ _ (coefficientSequenceTopology (ProEt.topology Y)) _

/-- The composite of base change and a slice inclusion is continuous. -/
instance reindexSiteContinuous₂ (n : ℕ) :
    (proEtaleBaseChange g ⋙ Prod.sectR n X.ProEt).IsContinuous
      (ProEt.topology Y) (coefficientSequenceTopology (ProEt.topology X)) :=
  Functor.isContinuous_comp _ _ _ (ProEt.topology X) _

/-- The two composite site functors agree. -/
def reindexSiteIso (n : ℕ) :
    proEtaleBaseChange g ⋙ Prod.sectR n X.ProEt ≅
      Prod.sectR n Y.ProEt ⋙ integralComparisonSequenceBaseChange g :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
    apply Prod.hom_ext
    · simp [integralComparisonSequenceBaseChange]
    · simp [integralComparisonSequenceBaseChange])


/-- The base-change constant map of the finite coefficient sheaves. -/
abbrev directConstMap (n : ℕ) :
    integralCoefficientSheaf.{u, u} l E Y n ⟶
      (proEtaleSheafDirectImage g RingCat.{u + 1}).obj (integralCoefficientSheaf.{u, u} l E X n) :=
  ⟨Functor.whiskerRight (coefficientProEtaleDirectRingMap.{u, u} g
    (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).hom
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

set_option backward.isDefEq.respectTransparency true in
/-- The constant-section comparison along `g` is the adjoint transpose of the base-change
constant map. -/
theorem constantMap_transpose (n : ℕ) :
    ((siteAdj g).sheafPushforwardContinuous (E := RingCat.{u + 1}) (ProEt.topology X)
        (ProEt.topology Y)).unit.app (integralCoefficientSheaf.{u, u} l E Y n) ≫
      (proEtaleSheafDirectImage g RingCat.{u + 1}).map
        (isoSectionwiseConstantMap.{u, u} g (CommRingCat.of (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E (n + 1))))) =
    directConstMap l E g n := by
  have h := towerFiniteCoefficientMap_eq l E g n
  unfold towerFiniteCoefficientMap at h
  let shAdj := (siteAdj g).sheafPushforwardContinuous (E := RingCat.{u + 1}) (ProEt.topology X)
    (ProEt.topology Y)
  have key : isoSectionwiseConstantMap.{u, u} g (CommRingCat.of (ULift.{u + 1}
      (Padic.coefficientExtensionRing l E (n + 1)))) =
      (shAdj.homEquiv _ _).symm ⟨Functor.whiskerRight (coefficientProEtaleDirectRingMap.{u, u} g
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩ := by
    rw [Adjunction.homEquiv_counit]
    exact h.symm
  have hd : shAdj.homEquiv _ _ (isoSectionwiseConstantMap.{u, u} g (CommRingCat.of
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) =
      ⟨Functor.whiskerRight (coefficientProEtaleDirectRingMap.{u, u} g
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩ := by
    rw [key]
    exact Equiv.apply_symm_apply _ _
  rw [Adjunction.homEquiv_unit] at hd
  exact hd

set_option backward.isDefEq.respectTransparency true in
/-- The completed relabelling comparison followed by the level-`n` projection. -/
theorem reindexRightRing_projection (n : ℕ) :
    reindexRightRing l E g ≫ (proEtaleSheafDirectImage g RingCat.{u + 1}).map
        (limit.π (integralCoefficientSheafSystem.{u, u} l E X) (op n)) =
      limit.π (integralCoefficientSheafSystem.{u, u} l E Y) (op n) ≫ directConstMap l E g n := by
  have hc := (isoReductionCompletedMap_existsUnique l E g).exists.choose_spec n
  have hn := ((siteAdj g).sheafPushforwardContinuous (E := RingCat.{u + 1}) (ProEt.topology X)
      (ProEt.topology Y)).unit.naturality
    (limit.π (integralCoefficientSheafSystem.{u, u} l E Y) (op n))
  rw [← constantMap_transpose]
  dsimp only [reindexRightRing]
  let u₁ := ((siteAdj g).sheafPushforwardContinuous (E := RingCat.{u + 1}) (ProEt.topology X)
    (ProEt.topology Y)).unit.app (completedIntegralCoefficientSheafUnrestricted l E Y)
  let G := proEtaleSheafDirectImage g RingCat.{u + 1}
  let πY := limit.π (integralCoefficientSheafSystem.{u, u} l E Y) (op n)
  let πX := limit.π (integralCoefficientSheafSystem.{u, u} l E X) (op n)
  let κ := isoSectionwiseConstantMap.{u, u} g (CommRingCat.of (ULift.{u + 1}
    (Padic.coefficientExtensionRing l E (n + 1))))
  have s1 := (Category.assoc u₁ (G.map (isoReductionCompletedMap l E g).hom) (G.map πX)).trans
    (congrArg (fun k ↦ u₁ ≫ k) (G.map_comp (isoReductionCompletedMap l E g).hom πX).symm)
  have s2 := congrArg (fun k ↦ u₁ ≫ G.map k) hc
  have s3 := (congrArg (fun k ↦ u₁ ≫ k)
    (G.map_comp ((isoSectionwiseInverseImage g RingCat.{u + 1}).map πY) κ)).trans
      (Category.assoc _ _ _).symm
  have s4 := (congrArg (fun k ↦ k ≫ G.map κ) hn.symm).trans (Category.assoc _ _ _)
  exact s1.trans (s2.trans (s3.trans s4))

set_option backward.isDefEq.respectTransparency true in
/-- Direct image of sequence modules commutes with evaluation and completed restriction. -/
def reindexLevelIso (n : ℕ) :
    integralComparisonSequenceDirectImage l E g ⋙ coefficientSequenceEvaluation l E Y n ⋙
        scalarReductionRestriction l E Y n ≅
      coefficientSequenceEvaluation l E X n ⋙ scalarReductionRestriction l E X n ⋙
        completedPush l E g :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (SheafOfModules.pushforwardComp _ _) _ ≪≫
    pushforwardRestrictIso _ _ _ ≪≫
    SheafOfModules.pushforwardCongr₂ _ (reindexSiteIso g n) (by
      ext1
      apply NatTrans.ext
      funext V
      ext r
      have hA := congrArg (fun k ↦ RingCat.Hom.hom k r) (towerRestrictionRing_app l E Y n V)
      have hX (y) := congrArg (fun k ↦ RingCat.Hom.hom k y)
        (towerRestrictionRing_app l E X n (op ((proEtaleBaseChange g).obj V.unop)))
      have hk := congrArg (fun k ↦ RingCat.Hom.hom (k.hom.app V) r)
        (reindexRightRing_projection l E g n)
      have hD (z) : RingCat.Hom.hom (((sheafPushforwardContinuousNatTrans (reindexSiteIso g n).hom
          RingCat.{u + 1} (ProEt.topology Y) (coefficientSequenceTopology (ProEt.topology X))).app
            ((sheafCompose (coefficientSequenceTopology (ProEt.topology X))
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
                (coefficientSequenceCommRingSheaf l E X))).hom.app V) z = z := by
        simp only [reindexSiteIso, comp_obj, sheafPushforwardContinuousNatTrans_app_hom,
          ObjectProperty.ι_obj, whiskerRight_app, op_obj, NatTrans.op_app]
        erw [CategoryTheory.Functor.map_id]
        rfl
      simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, RingCat.hom_comp,
        RingHom.coe_comp, Function.comp_apply, hD]
      refine Eq.trans (b := RingCat.Hom.hom ((directConstMap l E g n).hom.app V)
        (RingCat.Hom.hom ((towerRestrictionRing l E Y n).hom.app V) r)) rfl ?_
      refine Eq.trans ?_ (Eq.trans (b := RingCat.Hom.hom ((towerRestrictionRing l E X n).hom.app
        (op ((proEtaleBaseChange g).obj V.unop)))
          (RingCat.Hom.hom ((reindexRightRing l E g).hom.app V) r)) rfl rfl)
      exact (congrArg (RingCat.Hom.hom ((directConstMap l E g n).hom.app V)) hA).trans
        (hk.symm.trans (hX _).symm)) ≪≫
    (SheafOfModules.pushforwardComp _ _).symm ≪≫
    isoWhiskerRight (pushforwardRestrictIso _ _ _).symm _ ≪≫
    Functor.associator _ _ _

/-- The level comparison `reindexLevelIso` is the identity on sections. -/
theorem reindexLevelIso_hom_heq (n : ℕ) (Z : coefficientSequenceModules l E X) (V : Y.ProEtᵒᵖ)
    (x : ((integralComparisonSequenceDirectImage l E g ⋙ coefficientSequenceEvaluation l E Y n ⋙
      scalarReductionRestriction l E Y n).obj Z).val.obj V) :
    HEq (((reindexLevelIso l E g n).hom.app Z).val.app V x) x := by
  refine HEq.trans (b := Z.val.presheaf.map (𝟙 (op (n, (proEtaleBaseChange g).obj V.unop)))
    (id (α := Z.val.presheaf.obj (op (n, (proEtaleBaseChange g).obj V.unop))) x)) HEq.rfl ?_
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- The level-`n` comparison between direct image of sequence modules and completed
base change. -/
def reindexRestrictionLevel (n : ℕ) :
    integralComparisonSequenceDirectImage l E g ⋙ coefficientSequenceRestriction l E Y ⋙
        (evaluation ℕᵒᵖ (scalarReductionSource l E Y)).obj (op n) ≅
      coefficientSequenceRestriction l E X ⋙
        (evaluation ℕᵒᵖ (scalarReductionSource l E X)).obj (op n) ⋙ completedPush l E g :=
  isoWhiskerLeft (integralComparisonSequenceDirectImage l E g)
      (eqToIso (coefficientSequenceRestriction_evaluation l E Y n)) ≪≫
    reindexLevelIso l E g n ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (eqToIso (coefficientSequenceRestriction_evaluation l E X n).symm)
      (completedPush l E g) ≪≫ Functor.associator _ _ _

/-- The level comparison `reindexRestrictionLevel` is the identity on sections. -/
theorem reindexRestrictionLevel_hom_heq (n : ℕ) (Z : coefficientSequenceModules l E X)
    (V : Y.ProEtᵒᵖ)
    (x : (((coefficientSequenceRestriction l E Y).obj
      ((integralComparisonSequenceDirectImage l E g).obj Z)).obj (op n)).val.obj V) :
    HEq (((reindexRestrictionLevel l E g n).hom.app Z).val.app V x) x := by
  simp only [reindexRestrictionLevel, Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app, eqToIso.hom, eqToHom_app,
    eqToHom_map, Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply,
    Category.id_comp, Category.comp_id]
  exact (sheafOfModules_eqToHom_heq _ V _).trans
    ((reindexLevelIso_hom_heq l E g n _ V _).trans (sheafOfModules_eqToHom_heq _ V x))

/-- The inverse level comparison is the identity on sections. -/
theorem reindexRestrictionLevel_inv_heq (n : ℕ) (Z : coefficientSequenceModules l E X)
    (V : Y.ProEtᵒᵖ)
    (x : ((completedPush l E g).obj
      (((coefficientSequenceRestriction l E X).obj Z).obj (op n))).val.obj V) :
    HEq (((reindexRestrictionLevel l E g n).inv.app Z).val.app V x) x := by
  have h := reindexRestrictionLevel_hom_heq l E g n Z V
    (((reindexRestrictionLevel l E g n).inv.app Z).val.app V x)
  have hx : ((reindexRestrictionLevel l E g n).hom.app Z).val.app V
      (((reindexRestrictionLevel l E g n).inv.app Z).val.app V x) = x :=
    congrArg (fun k ↦ k.val.app V x) ((reindexRestrictionLevel l E g n).inv_hom_id_app Z)
  rw [hx] at h
  exact h.symm

omit [IsIso g] in
/-- Restriction maps of a sequence direct image are restrictions along base change. -/
theorem directImage_presheaf_map (Z : coefficientSequenceModules l E X)
    {A B : (ℕ × Y.ProEt)ᵒᵖ} (f : A ⟶ B)
    (y : ((integralComparisonSequenceDirectImage l E g).obj Z).val.presheaf.obj A) :
    ((integralComparisonSequenceDirectImage l E g).obj Z).val.presheaf.map f y =
      Z.val.presheaf.map ((integralComparisonSequenceBaseChange g).op.map f) y := rfl

/-- The level comparisons `reindexRestrictionLevel` commute with quotient transitions. -/
theorem reindexRestrictionLevel_naturality (Z : coefficientSequenceModules l E X) {m n : ℕ}
    (h : n ≤ m) :
    ((coefficientSequenceRestriction l E Y).obj
        ((integralComparisonSequenceDirectImage l E g).obj Z)).map (homOfLE h).op ≫
        (reindexRestrictionLevel l E g n).hom.app Z =
      (reindexRestrictionLevel l E g m).hom.app Z ≫
        (completedPush l E g).map
          (((coefficientSequenceRestriction l E X).obj Z).map (homOfLE h).op) := by
  ext V x
  apply eq_of_heq
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply]
  have hx : HEq x (cast (integralComparisonRestrictedSectionType l E Y
      ((integralComparisonSequenceDirectImage l E g).obj Z) m V) x) := (cast_heq _ _).symm
  have hmap : (integralComparisonSequenceBaseChange g).map
      (Prod.mkHom (homOfLE h) (𝟙 V.unop)) = Prod.mkHom (homOfLE h) (𝟙 _) := by
    simp [integralComparisonSequenceBaseChange]
  refine (reindexRestrictionLevel_hom_heq l E g n Z V _).trans ?_
  refine (restriction_transition_apply_heq l E Y _ h V x _ hx).trans ?_
  refine HEq.trans ?_ (restriction_transition_apply_heq l E X Z h
    (op ((proEtaleBaseChange g).obj V.unop)) _ _
    ((reindexRestrictionLevel_hom_heq l E g m Z V x).trans hx)).symm
  refine heq_of_eq ?_
  rw [directImage_presheaf_map, Functor.op_map, Quiver.Hom.unop_op, hmap]
  rfl

/-- Direct image of sequence modules commutes with the completed restriction towers. -/
def reindexRestrictionTower :
    integralComparisonSequenceDirectImage l E g ⋙ coefficientSequenceRestriction l E Y ≅
      coefficientSequenceRestriction l E X ⋙
        (whiskeringRight ℕᵒᵖ _ _).obj (completedPush l E g) :=
  NatIso.ofComponents (fun Z ↦ NatIso.ofComponents
      (fun n ↦ (reindexRestrictionLevel l E g n.unop).app Z) (by
        intro m n f
        have hf : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
        rw [hf]
        exact reindexRestrictionLevel_naturality l E g Z (leOfHom f.unop)))
    (fun f ↦ by
      ext n : 2
      exact (reindexRestrictionLevel l E g n.unop).hom.naturality f)

/-- The relabelling adjunction for completed modules along `g`. -/
def reindexAdj : isoReductionIntegralInverse l E g ⊣ completedPush l E g :=
  (isoInverseAdjunction_exists g _ _ (isoReductionCompletedMap l E g).hom).choose

/-- The unit of the relabelling adjunction restricts along the site counit. -/
theorem reindexAdj_unit (M : scalarReductionSource l E Y) (U : Y.ProEtᵒᵖ) (x : M.val.obj U) :
    ((reindexAdj l E g).unit.app M).val.app U x =
      M.val.map ((siteAdj g).counit.app U.unop).op x :=
  (isoInverseAdjunction_exists g _ _ (isoReductionCompletedMap l E g).hom).choose_spec M U x

/-- The right adjoint of relabelling preserves sequential limits. -/
instance completedPush_preservesLimits :
    PreservesLimitsOfShape ℕᵒᵖ (completedPush l E g) :=
  (reindexAdj l E g).rightAdjoint_preservesLimits.preservesLimitsOfShape

/-- Direct image of sequence modules commutes with the ordinary limit of quotient systems. -/
def reindexLimitIso :
    integralComparisonSequenceDirectImage l E g ⋙ CompletionUnit.ordinaryLimit l E Y ≅
      CompletionUnit.ordinaryLimit l E X ⋙ completedPush l E g :=
  limitCommIso _ _ _ _ (reindexRestrictionTower l E g)


/-- Heterogeneously equal functions commute with casts. -/
theorem heq_apply_cast {α α' : Type a} {β β' : Type b}
    (hα : α = α') (hβ : β = β') (f : α → β) (k : α' → β')
    (h : HEq f k) (x : α') :
    f (cast hα.symm x) = cast hβ.symm (k x) := by
  cases hα
  cases hβ
  exact congrFun (eq_of_heq h) x

omit [IsIso g] in
/-- On sections, vertical restrictions of a completed restriction are sequence restrictions. -/
theorem restriction_site_section (W : Scheme.{u})
    (M : coefficientSequenceModules l E W) (n : ℕ)
    {U V : W.ProEt} (f : U ⟶ V) (x : M.val.obj (op (n, V))) :
    (((coefficientSequenceRestriction l E W).obj M).obj (op n)).val.map f.op
        (integralComparisonRestrictedSection l E W M n (op V) x) =
      integralComparisonRestrictedSection l E W M n (op U)
        (M.val.map (Prod.mkHom (𝟙 n) f).op x) := by
  apply heq_apply_cast (integralComparisonRestrictedSectionType l E W M n (op V))
    (integralComparisonRestrictedSectionType l E W M n (op U)) _ _ ?_ x
  rw [← integralComparisonRestrictionCurried_eq l E W]
  rfl

omit [IsIso g] in
/-- Unit generators are compatible with vertical restrictions. -/
theorem unitSection_restrict (W : Scheme.{u}) (M : CompletionUnit.OrdinaryModel l E W)
    (N : scalarReductionSource l E W) (n : ℕ) {U U' : W.ProEt} (f : U' ⟶ U)
    (x : N.val.obj (op U)) :
    (M.tensor.obj N).val.map (Prod.mkHom (𝟙 n) f).op
        (PodQuotientTransition.unitSection l E W M N n (op U) x) =
      PodQuotientTransition.unitSection l E W M N n (op U') (N.val.map f.op x) := by
  apply restrictedSection_injective l E W _ n (op U')
  rw [← restriction_site_section, ← unit_restrictedSection_apply, ← unit_restrictedSection_apply,
]
  exact (PresheafOfModules.naturality_apply (M.adjunction.unit.app N ≫
    limit.π ((coefficientSequenceRestriction l E W).obj (M.tensor.obj N)) (op n)).val f.op x).symm

omit [IsIso g] in
/-- Unit generators are natural in the completed module. -/
theorem unitSection_map (W : Scheme.{u}) (M : CompletionUnit.OrdinaryModel l E W)
    {N N' : scalarReductionSource l E W} (φ : N ⟶ N') (n : ℕ) (U : W.ProEtᵒᵖ)
    (x : N.val.obj U) :
    (M.tensor.map φ).val.app (op (n, U.unop))
        (PodQuotientTransition.unitSection l E W M N n U x) =
      PodQuotientTransition.unitSection l E W M N' n U (φ.val.app U x) := by
  apply restrictedSection_injective l E W _ n U
  have h : M.adjunction.unit.app N ≫
      limit.π ((coefficientSequenceRestriction l E W).obj (M.tensor.obj N)) (op n) ≫
        ((coefficientSequenceRestriction l E W).map (M.tensor.map φ)).app (op n) =
      φ ≫ M.adjunction.unit.app N' ≫
        limit.π ((coefficientSequenceRestriction l E W).obj (M.tensor.obj N')) (op n) := by
    rw [← limMap_π, ← Category.assoc, ← Category.assoc]
    congr 1
    exact (M.adjunction.unit.naturality φ).symm
  have hx := congrArg (fun k ↦ k.val.app U x) h
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ConcreteCategory.comp_apply] at hx
  rw [← restriction_map_section, ← unit_restrictedSection_apply, ← unit_restrictedSection_apply]
  exact hx

set_option backward.isDefEq.respectTransparency true in
/-- The ordinary reindexing comparison of quotient tensors along an isomorphism, normalized on
unit generators. It is conjugate to the commutation of relabelling with ordinary limits. -/
theorem reindexComparison_exists (MY : CompletionUnit.OrdinaryModel l E Y)
    (MX : CompletionUnit.OrdinaryModel l E X) :
    ∃ β : MY.tensor ⋙ integralComparisonSequencePullback l E g ≅
        isoReductionIntegralInverse l E g ⋙ MX.tensor,
      PodQuotientTransition.ReindexNormalized l E g MY MX β := by
  let pE : integralComparisonSequencePullback l E g ⊣ integralComparisonSequenceDirectImage l E g :=
    Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E g)
  obtain ⟨a, ha, -⟩ := normalizedAdjointComparison
    (MY.tensor ⋙ integralComparisonSequencePullback l E g) _ _ _ (MY.adjunction.comp pE)
    ((reindexAdj l E g).comp MX.adjunction) (reindexLimitIso l E g)
  refine ⟨a, ?_⟩
  have key (N : scalarReductionSource l E Y) (n : ℕ) (V : Y.ProEtᵒᵖ) (x : N.val.obj V) :
      (a.hom.app N).val.app (op (n, (proEtaleBaseChange g).obj V.unop))
          (integralComparisonSequenceGenerator l E g (MY.tensor.obj N) n V.unop
            (PodQuotientTransition.unitSection l E Y MY N n V x)) =
        PodQuotientTransition.unitSection l E X MX ((isoReductionIntegralInverse l E g).obj N) n
          (op ((proEtaleBaseChange g).obj V.unop))
          (N.val.map ((siteAdj g).counit.app V.unop).op x) := by
    have h := congrArg (· ≫ limit.π ((coefficientSequenceRestriction l E Y).obj
      ((integralComparisonSequenceDirectImage l E g).obj
        (MX.tensor.obj ((isoReductionIntegralInverse l E g).obj N)))) (op n)) (ha N)
    simp only [Adjunction.comp_unit_app, Category.assoc, Functor.comp_map, Functor.comp_obj,
      lim_map, limMap_π, limMap_π_assoc, reindexLimitIso, limitCommIso_inv_π,
      reindexRestrictionTower, NatIso.ofComponents_inv_app, Iso.app_inv] at h
    have e := congrArg (fun k ↦ k.val.app V x) h
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ConcreteCategory.comp_apply] at e
    rw [unit_restrictedSection_apply, restriction_map_section] at e
    have hr := restriction_map_section l E Y
      ((integralComparisonSequenceDirectImage l E g).map (a.hom.app N)) n V
      (integralComparisonSequenceGenerator l E g (MY.tensor.obj N) n V.unop
        (PodQuotientTransition.unitSection l E Y MY N n V x))
    have hu := reindexAdj_unit l E g N V x
    have hπ := unit_restrictedSection_apply l E X MX ((isoReductionIntegralInverse l E g).obj N) n
      (op ((proEtaleBaseChange g).obj V.unop)) (N.val.map ((siteAdj g).counit.app V.unop).op x)
    exact eq_of_heq ((cast_heq _ _).symm.trans ((heq_of_eq (hr.symm.trans e.symm)).trans
      ((reindexRestrictionLevel_inv_heq l E g n _ V _).trans ((heq_of_eq
        ((congrArg (fun z ↦ (limit.π ((coefficientSequenceRestriction l E X).obj
          (MX.tensor.obj ((isoReductionIntegralInverse l E g).obj N))) (op n)).val.app
            (op ((proEtaleBaseChange g).obj V.unop))
          ((MX.adjunction.unit.app ((isoReductionIntegralInverse l E g).obj N)).val.app
            (op ((proEtaleBaseChange g).obj V.unop)) z)) hu).trans hπ)).trans (cast_heq _ _)))))
  intro N n U x
  have hk := key N n (op ((proEtaleIsoPostcompose g).obj U)) x
  simp only [Opposite.unop_op] at hk
  have h1 := PresheafOfModules.naturality_apply (a.hom.app N).val
    (Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U)).op
    (integralComparisonSequenceGenerator l E g (MY.tensor.obj N) n
      ((proEtaleIsoPostcompose g).obj U)
      (PodQuotientTransition.unitSection l E Y MY N n (op ((proEtaleIsoPostcompose g).obj U)) x))
  have h2 := unitSection_restrict l E X MX ((isoReductionIntegralInverse l E g).obj N) n
    (proEtaleIsoCommaArrow g U)
    (N.val.map ((siteAdj g).counit.app ((proEtaleIsoPostcompose g).obj U)).op x)
  have h3 : ((isoReductionIntegralInverse l E g).obj N).val.map (proEtaleIsoCommaArrow g U).op
      (N.val.map ((siteAdj g).counit.app ((proEtaleIsoPostcompose g).obj U)).op x) = x := by
    have ht := (siteAdj g).left_triangle_components U
    refine (PresheafOfModules.map_comp_apply N.val
      ((siteAdj g).counit.app ((proEtaleIsoPostcompose g).obj U)).op
      ((proEtaleIsoPostcompose g).map (proEtaleIsoCommaArrow g U)).op x).symm.trans ?_
    rw [← op_comp]
    erw [ht]
    rw [op_id]
    exact congrArg (fun f ↦ f x) (N.val.presheaf.map_id (op ((proEtaleIsoPostcompose g).obj U)))
  exact h1.trans ((congrArg _ hk).trans (h2.trans (congrArg _ h3)))

end OrdinaryQuotientCube
end WeilConjectures
