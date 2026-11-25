/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import all WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.IntegralOrdinaryLimitModel
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! # Ordinary quotient pullback and composition

Source: blueprint fix-prop-coherence, maps-used sentence; Stacks 03D7 and 0941.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option Elab.async false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted constantSheaf
  Functor.leftAdjoint presheafToSheaf Functor.ofSequence Functor.ofOpSequence
  pullbackTensorSequenceRing completedIntegralCommRingProjectionUnrestricted
  sfCompletedCoefficientMap pullbackTensorSequenceDirectEvaluation ordinaryLimitProjection
  coefficientSequenceCommRingSystem coefficientSequenceCommRingPresheaf
  coefficientSequenceCommRingSheaf proEtaleRingDirectImageMap
  completedIntegralCommRingSheafUnrestricted
attribute [local implicit_reducible] MorphismProperty Scheme.ProEt Scheme.instCategoryProEt
  CategoryTheory.Category.opposite Quiver.opposite CategoryTheory.CategoryStruct.opposite
  proEtaleRingModuleDirectImage
  PurCompactSupport.completed pullbackTensorOrdinaryLimit
  integralCoefficientSheaf integralCoefficientCommRingSheaf
  Functor.sheafPushforwardContinuous Prod.sectR SheafOfModules.pushforward
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars
  coefficientSequenceEvaluation coefficientProEtaleModuleDirectImage
  proEtaleConstantModuleDirectImage proEtaleConstantDirectImageMap coefficientProEtaleDirectRingMap
  pullbackTensorSequenceBase pullbackTensorSequenceDirect SheafOfModules.restrictScalars

private theorem projection_formula (a : OrdinaryLimitModel l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : coefficientSequenceModules l E X) (n : ℕ) (V : Y.ProEt)
    (x : ((pullbackTensorSequenceDirect l E f ⋙
      pullbackTensorOrdinaryLimit l E Y).obj M).val.obj (op V)) :
    ordinaryLimitProjection l E X M n ((proEtaleBaseChange f).obj V)
      (((a.comparison f).hom.app M).val.app (op V) x) =
    ordinaryLimitProjection l E Y ((pullbackTensorSequenceDirect l E f).obj M) n V x := by
  have h := a.projections f M n V x
  unfold integralPushSection finitePushSection at h
  have hd := directEvaluation_sections l E f n M V
    (ordinaryLimitProjection l E Y ((pullbackTensorSequenceDirect l E f).obj M) n V x)
  exact h.trans (eq_of_heq hd)

private theorem projection_natural (X : Scheme.{u})
    (M : coefficientSequenceModules l E X) (n : ℕ) {U V : X.ProEt} (k : U ⟶ V)
    (x : ((pullbackTensorOrdinaryLimit l E X).obj M).val.obj (op V)) :
    ordinaryLimitProjection l E X M n U
        (((pullbackTensorOrdinaryLimit l E X).obj M).val.map k.op x) =
      M.val.map (Prod.mkHom (𝟙 n) k).op
        (ordinaryLimitProjection l E X M n V x) := by
  unfold ordinaryLimitProjection restrictionSection
  exact PresheafOfModules.naturality_apply
    (limit.π ((coefficientSequenceRestriction l E X).obj M) (op n) ≫
      (eqToIso (coefficientSequenceRestriction_evaluation l E X n)).hom.app M).val k.op x

private theorem projection_map (X : Scheme.{u})
    {M N : coefficientSequenceModules l E X} (k : M ⟶ N) (n : ℕ) (U : X.ProEt)
    (x : ((pullbackTensorOrdinaryLimit l E X).obj M).val.obj (op U)) :
    ordinaryLimitProjection l E X N n U
        (((pullbackTensorOrdinaryLimit l E X).map k).val.app (op U) x) =
      k.val.app (op (n, U)) (ordinaryLimitProjection l E X M n U x) := by
  have h := limMap_π ((coefficientSequenceRestriction l E X).map k) (op n)
  have hs := (eqToIso (coefficientSequenceRestriction_evaluation l E X n)).hom.naturality k
  change ((coefficientSequenceRestriction l E X).map k).app (op n) ≫ _ = _ at hs
  have he : (pullbackTensorOrdinaryLimit l E X).map k ≫
      limit.π ((coefficientSequenceRestriction l E X).obj N) (op n) ≫
        (eqToIso (coefficientSequenceRestriction_evaluation l E X n)).hom.app N =
    limit.π ((coefficientSequenceRestriction l E X).obj M) (op n) ≫
      (eqToIso (coefficientSequenceRestriction_evaluation l E X n)).hom.app M ≫
      (coefficientSequenceEvaluation l E X n ⋙ scalarReductionRestriction l E X n).map k := by
    change limMap ((coefficientSequenceRestriction l E X).map k) ≫ _ ≫ _ = _
    rw [← Category.assoc, h, Category.assoc, hs]
  unfold ordinaryLimitProjection restrictionSection
  exact congrArg (fun q ↦ q.val.app (op U) x) he

private noncomputable def directComp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (PurCompactSupport.modulePushComposition_existsUnique
    (PurCompactSupport.completed l E) f g
    (PurCompactSupport.completedPull_comp l E f g)).exists.choose

private theorem conjugate_reduction (a : OrdinaryLimitModel l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    conjugateIsoEquiv
      ((pullbackTensorOrdinaryAdjunction l E Y).comp (pullbackTensorSequenceAdjunction l E f))
      ((proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).pull f)).comp
          (pullbackTensorOrdinaryAdjunction l E X)) (a.reductionPull l E f) =
      a.comparison f := by
  change (conjugateIsoEquiv _ _
    ((conjugateIsoEquiv _ _).symm (a.comparison f).symm)).symm = _
  rw [Equiv.apply_symm_apply]
  rfl

private theorem direct_projection_coherence
    (o : Operations l E) (a : OrdinaryLimitModel l E) (c : Compositors l E o)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : coefficientSequenceModules l E X) (n : ℕ) (U : Z.ProEt)
    (x : ((pullbackTensorSequenceDirect l E f ⋙ pullbackTensorSequenceDirect l E g ⋙
      pullbackTensorOrdinaryLimit l E Z).obj M).val.obj (op U)) :
    ordinaryLimitProjection l E X M n ((proEtaleBaseChange (f ≫ g)).obj U)
      (((directComp l E f g).hom.app ((pullbackTensorOrdinaryLimit l E X).obj M)).val.app
        (op U)
        (((proEtaleRingModuleDirectImage g ((PurCompactSupport.completed l E).ring Z)
          ((PurCompactSupport.completed l E).ring Y)
          ((PurCompactSupport.completed l E).pull g)).map
            ((a.comparison f).hom.app M)).val.app (op U)
          (((a.comparison g).hom.app ((pullbackTensorSequenceDirect l E f).obj M)).val.app
            (op U) x))) =
      ordinaryLimitProjection l E X M n ((proEtaleBaseChange (f ≫ g)).obj U)
        (((a.comparison (f ≫ g)).hom.app M).val.app (op U)
          (((pullbackTensorOrdinaryLimit l E Z).map ((c.ordinaryDirect f g).hom.app M)).val.app
            (op U) x)) := by
  let B := (pullbackTensorOrdinaryLimit l E X).obj M
  let N := (pullbackTensorSequenceDirect l E f).obj M
  let gU := (proEtaleBaseChange g).obj U
  let k : (proEtaleBaseChange (f ≫ g)).obj U ⟶ (proEtaleBaseChange f).obj gU :=
    (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).hom.app U
  let xg : ((pullbackTensorOrdinaryLimit l E Y).obj N).val.obj (op gU) :=
    ((a.comparison g).hom.app N).val.app (op U) x
  let xf : B.val.obj (op ((proEtaleBaseChange f).obj gU)) :=
    ((a.comparison f).hom.app M).val.app (op gU) xg
  let r := ordinaryLimitProjection l E Z ((pullbackTensorSequenceDirect l E g).obj N) n U x
  have h1 := congrArg
    (ordinaryLimitProjection l E X M n ((proEtaleBaseChange (f ≫ g)).obj U))
    ((PurCompactSupport.modulePushComposition_existsUnique
      (PurCompactSupport.completed l E) f g
      (PurCompactSupport.completedPull_comp l E f g)).exists.choose_spec B U xf)
  have h2 := projection_natural l E X M n k xf
  have h3 := congrArg (fun z ↦ M.val.map (Prod.mkHom (𝟙 n) k).op z)
    (projection_formula l E a f M n gU xg)
  have h4 := congrArg (fun z ↦ M.val.map (Prod.mkHom (𝟙 n) k).op z)
    (projection_formula l E a g N n U x)
  have h5 := (c.sections f g M n U r).symm
  have h6 := (projection_map l E Z ((c.ordinaryDirect f g).hom.app M) n U x).symm
  have h7 := (projection_formula l E a (f ≫ g) M n U
    (((pullbackTensorOrdinaryLimit l E Z).map
      ((c.ordinaryDirect f g).hom.app M)).val.app (op U) x)).symm
  apply eq_of_heq
  exact (heq_of_eq h1).trans ((heq_of_eq h2).trans ((heq_of_eq h3).trans
    ((heq_of_eq h4).trans ((heq_of_eq h5).trans ((heq_of_eq h6).trans (heq_of_eq h7))))))

private theorem direct_coherence (o : Operations l E) (a : OrdinaryLimitModel l E)
    (c : Compositors l E o) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Functor.isoWhiskerLeft (pullbackTensorSequenceDirect l E f) (a.comparison g) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (a.comparison f)
          (proEtaleRingModuleDirectImage g ((PurCompactSupport.completed l E).ring Z)
            ((PurCompactSupport.completed l E).ring Y)
            ((PurCompactSupport.completed l E).pull g)) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (pullbackTensorOrdinaryLimit l E X) (directComp l E f g) =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (c.ordinaryDirect f g) (pullbackTensorOrdinaryLimit l E Z) ≪≫
        a.comparison (f ≫ g) := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  let D := proEtaleRingModuleDirectImage (f ≫ g)
    ((PurCompactSupport.completed l E).ring Z)
    ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).pull (f ≫ g))
  let : D.IsRightAdjoint := (proEtaleRingModuleAdjunction (f ≫ g)
    ((PurCompactSupport.completed l E).ring Z)
    ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).pull (f ≫ g))).isRightAdjoint
  let : PreservesLimitsOfSize.{0, 0} D := (proEtaleRingModuleAdjunction (f ≫ g)
    ((PurCompactSupport.completed l E).ring Z)
    ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).pull (f ≫ g))).rightAdjoint_preservesLimits
  apply (isLimitOfPreserves D
    (limit.isLimit ((coefficientSequenceRestriction l E X).obj M))).hom_ext
  intro n
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  apply eq_of_heq
  refine (ordinaryLimitProjection_heq l E X M n.unop
    ((proEtaleBaseChange (f ≫ g)).obj U.unop) _).symm.trans
    ((heq_of_eq ?_).trans (ordinaryLimitProjection_heq l E X M n.unop
      ((proEtaleBaseChange (f ≫ g)).obj U.unop) _))
  exact direct_projection_coherence l E o a c f g M n.unop U.unop x

/-- Ordinary coefficient reduction preserves the geometric pullback compositor.
Source: blueprint latest, sec-six-functors/sk-thm-sf-compatibility/
fix-prop-coherence.proof.md, maps-used sentence; Stacks 03D7, 03D8 and 0941.
(blueprint: lem-sf-ordinary-reduction-pull-composition).

Proof: take the ordinary right-adjoint conjugates. The ringed direct-image compositor
is fixed by restriction along pullbackComp, as is c.ordinaryDirect by c.sections.
Postcompose the two resulting maps into the coefficient limit with each limit projection.
The equations a.projections give the same finite projection followed by the same
restriction along pullbackComp on both sides. Naturality of the limit projections
moves this restriction past the projection. Ordinary limit projections are jointly
monic, so the direct-image/limit square commutes. Compatibility of adjoint conjugation
with pasting gives the displayed quotient/pullback square, using c.conjugate.
This is an equality of ordinary sheaf maps, before complexes or derived localization;
identity morphisms and zero sheaves are covered by the same projection calculation. -/
theorem ordinaryReductionPullComposition
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (o : Operations l E) (a : OrdinaryLimitModel l E) (c : Compositors l E o)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : scalarReductionSource l E Z) :
    (pullbackTensorOrdinaryReduction l E X).map
        (((conjugateIsoEquiv
          ((proEtaleRingModuleAdjunction g ((PurCompactSupport.completed l E).ring Z)
            ((PurCompactSupport.completed l E).ring Y)
            ((PurCompactSupport.completed l E).pull g)).comp
          (proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
            ((PurCompactSupport.completed l E).ring X)
            ((PurCompactSupport.completed l E).pull f)))
          (proEtaleRingModuleAdjunction (f ≫ g) ((PurCompactSupport.completed l E).ring Z)
            ((PurCompactSupport.completed l E).ring X)
            ((PurCompactSupport.completed l E).pull (f ≫ g)))).symm
          (PurCompactSupport.modulePushComposition_existsUnique
            (PurCompactSupport.completed l E) f g
            (PurCompactSupport.completedPull_comp l E f g)).exists.choose).hom.app M) ≫
        (a.reductionPull l E f).hom.app ((integralOrdinaryPull l E g).obj M) ≫
        (pullbackTensorSequenceInverse l E f).map ((a.reductionPull l E g).hom.app M) =
      (a.reductionPull l E (f ≫ g)).hom.app M ≫
        (c.ordinaryPull f g).hom.app ((pullbackTensorOrdinaryReduction l E Z).obj M) := by
  let rf := proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull f)
  let rg := proEtaleRingModuleAdjunction g ((PurCompactSupport.completed l E).ring Z)
    ((PurCompactSupport.completed l E).ring Y) ((PurCompactSupport.completed l E).pull g)
  let rh := proEtaleRingModuleAdjunction (f ≫ g) ((PurCompactSupport.completed l E).ring Z)
    ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull (f ≫ g))
  let rx := pullbackTensorOrdinaryAdjunction l E X
  let ry := pullbackTensorOrdinaryAdjunction l E Y
  let rz := pullbackTensorOrdinaryAdjunction l E Z
  let sf := pullbackTensorSequenceAdjunction l E f
  let sg := pullbackTensorSequenceAdjunction l E g
  let sh := pullbackTensorSequenceAdjunction l E (f ≫ g)
  let γ := (conjugateIsoEquiv (rg.comp rf) rh).symm (directComp l E f g)
  let lhs := Functor.isoWhiskerRight γ (pullbackTensorOrdinaryReduction l E X) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (integralOrdinaryPull l E g) (a.reductionPull l E f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (a.reductionPull l E g) (pullbackTensorSequenceInverse l E f) ≪≫
    Functor.associator _ _ _
  let rhs := a.reductionPull l E (f ≫ g) ≪≫
    Functor.isoWhiskerLeft (pullbackTensorOrdinaryReduction l E Z) (c.ordinaryPull f g)
  have he : lhs = rhs := by
    apply (conjugateIsoEquiv (rz.comp (sg.comp sf)) (rh.comp rx)).injective
    dsimp only [lhs, rhs]
    rw [conjugateIsoEquiv_trans _ ((rg.comp rf).comp rx) _]
    rw [conjugateIsoEquiv_trans _ (rg.comp (rf.comp rx)) _]
    rw [conjugateIsoEquiv_trans _ (rg.comp (ry.comp sf)) _]
    rw [conjugateIsoEquiv_trans _ ((rg.comp ry).comp sf) _]
    rw [conjugateIsoEquiv_trans _ ((rz.comp sg).comp sf) _]
    rw [conjugateIsoEquiv_trans _ (rz.comp sh) _]
    simp only [conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_isoWhiskerRight,
      conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_associator, γ,
      Equiv.apply_symm_apply]
    dsimp only [rf, rg, rh, rx, ry, rz, sf, sg, sh]
    rw [conjugate_reduction, conjugate_reduction, conjugate_reduction, c.conjugate]
    apply Iso.ext
    apply NatTrans.ext
    funext N
    have hd := congr_app (congrArg Iso.hom (direct_coherence l E o a c f g)) N
    simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom,
      Category.id_comp, Category.comp_id, Category.assoc] using hd
  have h := congr_app (congrArg Iso.hom he) M
  simpa only [lhs, rhs, γ, directComp, rf, rg, rh, Iso.symm_hom, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc] using h

end WeilConjectures.IntegralSystemRealization
