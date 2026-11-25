/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Pur.PurSequenceAdjointResolutionData
import all WeilConjectures.AlgebraicGeometry.SmoothPurity.SequenceSiteCompletionProjectionSupplement
import WeilConjectures.AlgebraicGeometry.Constant.ConstantSequenceModuleEquivalenceOfUniverses
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Factoring the ordinary projection through the constant completed ring

Source: Stacks 0940, section-derived-limits, and 03D7, change of rings.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u c v r
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory
namespace WeilConjectures
open SemilinearSections

private def sequenceRingMap
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    {A B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r}} (α : A ⟶ B) :
    SheafOfModules.systemSequenceRing.{c, v, r} A ⟶
      SheafOfModules.systemSequenceRing.{c, v, r} B :=
  ⟨Functor.whiskerLeft (prodOpEquiv (C := ℕ) (D := C)).functor
    (Functor.uncurry.map (Functor.whiskerRight α (sheafToPresheaf J CommRingCat.{r})))⟩

private def ringedIdentityScalars
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} {A B : Sheaf J RingCat.{r}} (φ : A ⟶ B) :
    RingedToposMorphismOfUniverses B A where
  inverse := 𝟭 _
  direct := 𝟭 _
  adj := Adjunction.id
  leftExact := inferInstance
  ringMap := (sheafCompose J (forget RingCat.{r})).map φ
  ring_zero := by
    intro T z hz U x
    change (φ.hom.app U).hom (z.hom.app U x) = 0
    rw [hz]
    exact map_zero _
  ring_one := by
    intro T z hz U x
    change (φ.hom.app U).hom (z.hom.app U x) = 1
    rw [hz]
    exact map_one _
  ring_add := by
    intro T x y z hz U t
    change (φ.hom.app U).hom (z.hom.app U t) = _
    rw [hz]
    exact map_add _ _ _
  ring_mul := by
    intro T x y z hz U t
    change (φ.hom.app U).hom (z.hom.app U t) = _
    rw [hz]
    exact map_mul _ _ _
  modules := SheafOfModules.restrictScalars φ
  additive := inferInstance
  underlying := Iso.refl _
  module_linear := by
    intro M T a x y z hz U t
    exact hz U t

section ConstantGeometry
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (A : Sheaf J CommRingCat.{max c v r})

private abbrev constantTowers :=
  CategoryTheory.ConstantCompletion.independentConstantSequenceEquivalence.{c, v, r} A

private def constantUnderlyingTower :
    (constantTowers.{c, v, r} J A).functor ⋙
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj (completionUnderlying.{c, v, max c v r} J A) ≅
        completionUnderlying.{c, v, max c v r} (coefficientSequenceTopology J)
          (SheafOfModules.systemSequenceRing.{c, v, max c v r} ((Functor.const ℕᵒᵖ).obj A)) ⋙
            seqSetsTower.{c, v, max c v r} J :=
  NatIso.ofComponents (fun N ↦ NatIso.ofComponents (fun n ↦ Iso.refl _)
    (by intros; ext V x; rfl)) (by intros; ext n V x; rfl)

private def constantUnderlyingDirect :
    ((constantTowers.{c, v, r} J A).functor ⋙ lim) ⋙ completionUnderlying.{c, v, max c v r} J A ≅
      completionUnderlying.{c, v, max c v r} (coefficientSequenceTopology J)
        (SheafOfModules.systemSequenceRing.{c, v, max c v r} ((Functor.const ℕᵒᵖ).obj A)) ⋙
          (seqSetsTower.{c, v, max c v r} J ⋙ lim) :=
  Functor.isoWhiskerLeft (constantTowers.{c, v, r} J A).functor
    (preservesLimitNatIso (completionUnderlying.{c, v, max c v r} J A)) ≪≫
      Functor.isoWhiskerRight (constantUnderlyingTower.{c, v, r} J A) lim

private theorem constantUnderlyingDirect_projection
    (N : SheafOfModules.systemSequenceModules.{c, v, max c v r}
      ((Functor.const ℕᵒᵖ).obj A)) (n : ℕ) :
    (constantUnderlyingDirect.{c, v, r} J A).hom.app N ≫
      limit.π ((seqSetsTower.{c, v, max c v r} J).obj
        ((completionUnderlying.{c, v, max c v r} (coefficientSequenceTopology J)
          (SheafOfModules.systemSequenceRing.{c, v, max c v r}
            ((Functor.const ℕᵒᵖ).obj A))).obj N)) (op n) =
      (completionUnderlying.{c, v, max c v r} J A).map
        (limit.π ((constantTowers.{c, v, r} J A).functor.obj N) (op n)) ≫
          ((constantUnderlyingTower.{c, v, r} J A).hom.app N).app (op n) := by
  dsimp only [constantUnderlyingDirect, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  erw [Category.assoc, limMap_π, ← Category.assoc, preservesLimitIso_hom_π]

private theorem constant_transpose_component
    (N : SheafOfModules.systemSequenceModules.{c, v, max c v r}
      ((Functor.const ℕᵒᵖ).obj A))
    (H : Sheaf J (Type (max c v r)))
    (a : H ⟶ (completionUnderlying.{c, v, max c v r} J A).obj
      (limit ((constantTowers.{c, v, r} J A).functor.obj N)))
    (n : ℕ) (V : Cᵒᵖ) (x : H.obj.obj V) :
    (((seqAdjunction J).homEquiv H _).symm
      (a ≫ (constantUnderlyingDirect.{c, v, r} J A).hom.app N)).hom.app (op (n, V.unop)) x =
        (limit.π ((constantTowers.{c, v, r} J A).functor.obj N) (op n)).val.app V
          (a.hom.app V x) := by
  rw [seqAdjunction_homEquiv]
  change ((a ≫ (constantUnderlyingDirect.{c, v, r} J A).hom.app N) ≫
    limit.π _ (op n)).hom.app V x = _
  have h := congrArg (fun f ↦ (a ≫ f).hom.app V x)
    (constantUnderlyingDirect_projection.{c, v, r} J A N n)
  exact h

private def constantRingMap :
    (seqConstant.{c, v, max c v r} J).obj
      ((sheafCompose J (forget RingCat.{max c v r})).obj (ring J A)) ⟶
      (sheafCompose (coefficientSequenceTopology J) (forget RingCat.{max c v r})).obj
        (ring (coefficientSequenceTopology J)
          (SheafOfModules.systemSequenceRing.{c, v, max c v r} ((Functor.const ℕᵒᵖ).obj A))) :=
  ⟨{ app := fun _ ↦ ↾id
     naturality := by intros; ext x; rfl }⟩

private def constantGeometry :
    RingedToposMorphismOfUniverses
      (ring (coefficientSequenceTopology J)
        (SheafOfModules.systemSequenceRing.{c, v, max c v r}
          ((Functor.const ℕᵒᵖ).obj A))) (ring J A) where
  inverse := seqConstant.{c, v, max c v r} J
  direct := seqSetsTower.{c, v, max c v r} J ⋙ lim
  adj := seqAdjunction J
  leftExact := inferInstance
  ringMap := constantRingMap.{c, v, r} J A
  ring_zero := by intro T z hz U x; exact hz (op U.unop.2) x
  ring_one := by intro T z hz U x; exact hz (op U.unop.2) x
  ring_add := by intro T x y z hz U t; exact hz (op U.unop.2) t
  ring_mul := by intro T x y z hz U t; exact hz (op U.unop.2) t
  modules := (constantTowers.{c, v, r} J A).functor ⋙ lim
  additive := by
    have :=
      (CategoryTheory.ConstantCompletion.independentConstantSequenceEquivalence_additive.{c, v, r}
        A).1
    constructor
    intro M N f g
    apply limit.hom_ext
    intro n
    change lim.map ((constantTowers.{c, v, r} J A).functor.map (f + g)) ≫ _ = _
    simp only [lim_map, limMap_π, Functor.map_add, Preadditive.add_comp,
      Preadditive.comp_add, NatTrans.app_add, Functor.comp_map]
  underlying := constantUnderlyingDirect.{c, v, r} J A
  module_linear := by
    intro N T a x y z hz U t
    obtain ⟨⟨n, V⟩⟩ := U
    change T.obj.obj (op V) at t
    let av : (ring (coefficientSequenceTopology J)
        (SheafOfModules.systemSequenceRing.{c, v, max c v r}
          ((Functor.const ℕᵒᵖ).obj A))).obj.obj (op (n, V)) := a.hom.app (op V) t
    change _ = av •
      (_ : N.val.obj (op (n, V))) + (_ : N.val.obj (op (n, V)))
    let p := (limit.π ((constantTowers.{c, v, r} J A).functor.obj N) (op n)).val.app (op V)
    let xv : (limit ((constantTowers.{c, v, r} J A).functor.obj N)).val.obj (op V) :=
      x.hom.app (op V) t
    let yv : (limit ((constantTowers.{c, v, r} J A).functor.obj N)).val.obj (op V) :=
      y.hom.app (op V) t
    have hz0 := constant_transpose_component.{c, v, r} J A N T z n (op V) t
    have hx0 := constant_transpose_component.{c, v, r} J A N T x n (op V) t
    have hy0 := constant_transpose_component.{c, v, r} J A N T y n (op V) t
    have hlin := (p.hom.map_add (av • xv) yv).trans
      (congrArg (fun z ↦ z + p.hom yv) (p.hom.map_smul av xv))
    exact hz0.trans ((congrArg p.hom (hz (op V) t)).trans
      (hlin.trans (congrArg₂ (fun (x y : N.val.obj (op (n, V))) ↦ av • x + y)
        hx0.symm hy0.symm)))
end ConstantGeometry

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

private def coefficientCone :
    (Functor.const ℕᵒᵖ).obj (completedIntegralCommRingSheafUnrestricted l E W) ⟶
      coefficientSequenceCommRingSystem l E W :=
  NatTrans.ofOpSequence (fun n ↦ completedIntegralCommRingProjectionUnrestricted l E W n)
    (by
      intro n
      dsimp only [Functor.const_obj_obj, Functor.const_obj_map,
        coefficientSequenceCommRingSystem, Functor.ofOpSequence_obj]
      rw [Functor.ofOpSequence_map_homOfLE_succ, Category.id_comp]
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext V
      apply (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}).map_injective
      change (limit.π (integralCoefficientSheafSystem l E W) (op n)).hom.app V =
        (limit.π (integralCoefficientSheafSystem l E W) (op (n + 1))).hom.app V ≫
          (integralCoefficientSheafTransition l E W n).hom.app V
      have h := congrArg (fun k ↦ k.hom.app V)
        (limit.w (integralCoefficientSheafSystem l E W) (homOfLE (Nat.le_succ n)).op)
      simpa only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ,
        ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] using h.symm)

attribute [local irreducible] CategoryTheory.constantSheaf
  completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted
private def quotientScalarMap : purSequenceConstantRing l E W ⟶ purSequenceQuotientRing l E W :=
  (sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (sequenceRingMap (coefficientCone l E W))

private abbrev firstFactor := ringedIdentityScalars (quotientScalarMap l E W)

private abbrev secondFactor :=
  constantGeometry.{t + 1, t, u} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)

private abbrev completedTowers :=
  constantTowers.{t + 1, t, u} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)

private theorem firstFactor_restriction :
    (firstFactor l E W).modules ⋙ (completedTowers l E W).functor =
      coefficientSequenceRestriction l E W := by
  unfold coefficientSequenceRestriction
  apply (coefficientSequenceRestriction_exists l E W).unique ?_
    (coefficientSequenceRestriction_exists l E W).exists.choose_spec
  refine ⟨?_, ?_, ?_⟩
  · intro N n
    have he : coefficientSequenceEvaluation l E W n =
        SheafOfModules.systemSequenceEvaluation (coefficientSequenceCommRingSystem l E W) n :=
      seqEval_eq (Scheme.ProEt.topology W)
        (fun n ↦ integralCoefficientCommRingSheaf l E W n)
        (coefficientSequenceCommRingTransition l E W) n
    rw [he]
    rfl
  · intro N m n h V
    rfl
  · intro N N' f n V
    rfl

private def inverseComparison (O : PurSequenceOrdinaryAdjoints l E W) :
    O.p.inverse ≅ (seqConstant (Scheme.ProEt.topology W)) :=
  ((fullyFaithfulSheafToPresheaf
    (coefficientSequenceTopology (Scheme.ProEt.topology W)) (Type (max u (t + 1)))).whiskeringRight
      (Sheaf (Scheme.ProEt.topology W) (Type (max u (t + 1))))).preimageIso O.constant

private def directComparison (O : PurSequenceOrdinaryAdjoints l E W) :
    O.p.direct ≅ (firstFactor l E W).direct ⋙ (secondFactor l E W).direct :=
  O.p.adj.rightAdjointUniq ((seqAdjunction (Scheme.ProEt.topology W)).ofNatIsoLeft
    (inverseComparison l E W O).symm)

private def towerEvaluation (n : ℕ) :
    (completedTowers l E W).functor ⋙
      (CategoryTheory.evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n) ≅
        SheafOfModules.systemSequenceEvaluation
          ((Functor.const ℕᵒᵖ).obj (completedIntegralCommRingSheafUnrestricted l E W)) n :=
  NatIso.ofComponents (fun N ↦ Iso.refl _) (by intros; rfl)

/-- The ringed factorization, once the ordinary adjoints have been constructed.
Source: Stacks 0940, section-derived-limits, and 03D7, change of rings
(blueprint: lem-pur-sequence-constant-ring-factorization).

Proof: the completed-ring projections form a morphism from the constant completed
ring to the quotient ring on the sequence site. Take identity inverse and direct
images on sheaves of sets and restriction along that ring map on modules; this is
the first ringed morphism. Take constant inverse image and limit direct image,
with identity structural ring map, for the second. Realize constant-ring module
sheaves as towers using the explicit strict-system equivalence. Its evaluation
maps are identities on sections and its horizontal arrows are the original
restrictions. Restriction along the quotient ring map therefore gives exactly the
recorded coefficient restriction tower. The second module direct image is its
inverse limit. The supplied constant-inverse-image comparison identifies the
original inverse image with the composite; uniqueness of right adjoints gives
the direct-image comparison. The original coordinate structural-map equation
proves the ring composition equation by sectionwise extensionality. The original
limit comparison and the restriction-tower comparison give the module composition
comparison. Finally scalar restriction leaves additive sheaves unchanged, so
kernels and sheafified cokernels are unchanged and both exactness fields hold.
This uses no surjectivity or flatness of any quotient map. -/
theorem purSequenceConstantRingFactorization (O : PurSequenceOrdinaryAdjoints l E W) :
    Nonempty (PurSequenceRingedFactorization l E W O) := by
  refine ⟨{
    a := firstFactor l E W
    g := secondFactor l E W
    a_identity := Iso.refl _
    g_constant := Iso.refl _
    a_quotient := ?_
    g_ring := ?_
    inverse_comp := inverseComparison l E W O
    direct_comp := directComparison l E W O
    ring_comp := ?_
    modules_comp := O.limit ≪≫
      Functor.isoWhiskerRight (eqToIso (firstFactor_restriction l E W)).symm lim
    towers := completedTowers l E W
    evaluation := towerEvaluation l E W
    sections := ?_
    transitions := ?_
    restriction := eqToIso (firstFactor_restriction l E W)
    limit := Iso.refl _
    exact_limits := ?_
    exact_colimits := ?_
  }⟩
  · intro n V x
    rfl
  · intro n V x
    rfl
  · ext U x
    obtain ⟨⟨n, V⟩⟩ := U
    exact O.quotient n (op V) x
  · intro N n V
    rfl
  · intro N m n h V
    rfl
  · exact (SheafOfModules.systemScalarRestriction_exact
      (sequenceRingMap (coefficientCone l E W))).1
  · exact (SheafOfModules.systemScalarRestriction_exact
      (sequenceRingMap (coefficientCone l E W))).2

end WeilConjectures
