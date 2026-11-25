/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodOrdinaryQuotientTransitionCubeAux2
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems

/-! # Ordinary quotient cube: the cube on unit generators

The ordinary scalar/reindexing cube on a single completed module, checked on scalar-one
tensors of unit generators.

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
variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

namespace OrdinaryQuotientCube

/-- Scalar-one tensors are natural in the sequence module. -/
theorem tensorSection_one_map (W : Scheme.{u}) {M M' : coefficientSequenceModules l E W}
    (f : M ⟶ M') (U : (ℕ × W.ProEt)ᵒᵖ) (z : M.val.obj U) :
    ((integralComparisonSequenceScalarModel l E L ι W).E.map f).val.app U
        (integralComparisonSequenceTensorSection l E L ι W M U 1 z) =
      integralComparisonSequenceTensorSection l E L ι W M' U 1 (f.val.app U z) := by
  rw [← sequenceScalarAdjunction_unit, ← sequenceScalarAdjunction_unit]
  have h := congrArg (fun k ↦ k.val.app U z)
    ((sequenceScalarAdjunction l E L ι W).choose.unit.naturality f)
  exact h.symm

/-- Scalar-one tensors are compatible with restrictions of the sequence site. -/
theorem tensorSection_one_restrict (W : Scheme.{u}) (M : coefficientSequenceModules l E W)
    {U U' : (ℕ × W.ProEt)ᵒᵖ} (h : U ⟶ U') (z : M.val.obj U) :
    ((integralComparisonSequenceScalarModel l E L ι W).E.obj M).val.presheaf.map h
        (integralComparisonSequenceTensorSection l E L ι W M U 1 z) =
      integralComparisonSequenceTensorSection l E L ι W M U' 1 (M.val.presheaf.map h z) := by
  rw [← sequenceScalarAdjunction_unit, ← sequenceScalarAdjunction_unit]
  exact (congrArg (fun k ↦ k z) (((PresheafOfModules.toPresheaf _).map
    ((sequenceScalarAdjunction l E L ι W).choose.unit.app M).val).naturality h)).symm

/-- Pullback generators are natural in the sequence module. -/
theorem generator_map {X Y : Scheme.{u}} (g : X ⟶ Y) {M M' : coefficientSequenceModules l E Y}
    (f : M ⟶ M') (n : ℕ) (V : Y.ProEt) (z : M.val.obj (op (n, V))) :
    ((integralComparisonSequencePullback l E g).map f).val.app
        (op (n, (proEtaleBaseChange g).obj V))
        (integralComparisonSequenceGenerator l E g M n V z) =
      integralComparisonSequenceGenerator l E g M' n V (f.val.app (op (n, V)) z) := by
  have h := congrArg (fun k ↦ k.val.app (op (n, V)) z)
    ((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E g)).unit.naturality f)
  exact h.symm

/-- Pullback generators of scalar-one tensors under the scalar/pullback associator. -/
theorem scalarPullback_generator {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : coefficientSequenceModules l E Y) (n : ℕ) (V : Y.ProEt) (x : M.val.obj (op (n, V))) :
    ((integralComparisonSequenceScalarPullback l E L ι g).hom.app M).val.app
        (op (n, (proEtaleBaseChange g).obj V))
        (integralComparisonSequenceTensorSection l E L ι X
          ((integralComparisonSequencePullback l E g).obj M)
          (op (n, (proEtaleBaseChange g).obj V)) 1
          (integralComparisonSequenceGenerator l E g M n V x)) =
      integralComparisonSequenceGenerator l L g
        ((integralComparisonSequenceScalarModel l E L ι Y).E.obj M) n V
        (integralComparisonSequenceTensorSection l E L ι Y M (op (n, V)) 1 x) :=
  (integralComparisonSequenceScalarPullback_existsUnique l E L ι g).exists.choose_spec M n V x

/-- The inverse of an isomorphism of sheaves of modules on a known section. -/
theorem iso_inv_apply_of_hom_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{a}} {A B : SheafOfModules.{b} R} (φ : A ≅ B) (U : Cᵒᵖ)
    {x : A.val.obj U} {y : B.val.obj U} (h : φ.hom.val.app U x = y) :
    φ.inv.val.app U y = x := by
  rw [← h]
  exact congrArg (fun k ↦ k.val.app U x) φ.hom_inv_id

/-- The inverse of a natural isomorphism of module functors on a known section. -/
theorem natIso_inv_apply_of_hom_apply {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology D} {R : Sheaf J RingCat.{a}} {F G : C ⥤ SheafOfModules.{b} R}
    (φ : F ≅ G) (N : C) (U : Dᵒᵖ) {x : (F.obj N).val.obj U} {y : (G.obj N).val.obj U}
    (h : (φ.hom.app N).val.app U x = y) : (φ.inv.app N).val.app U y = x :=
  iso_inv_apply_of_hom_apply (φ.app N) U h

/-- Module restriction maps are the underlying abelian restriction maps. -/
theorem module_map_eq_presheaf_map {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat.{a}}
    (M : PresheafOfModules.{b} R) {U V : Cᵒᵖ} (f : U ⟶ V) (x : M.obj U) :
    M.map f x = M.presheaf.map f x := rfl

/-- A morphism of sheaves of modules commutes with restriction, in presheaf form. -/
theorem presheaf_naturality_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{a}} {A B : SheafOfModules.{b} R} (φ : A ⟶ B) {U V : Cᵒᵖ}
    (f : U ⟶ V) (x : A.val.obj U) :
    φ.val.app V (A.val.presheaf.map f x) = B.val.presheaf.map f (φ.val.app U x) :=
  congrArg (fun k ↦ k x) (((PresheafOfModules.toPresheaf _).map φ.val).naturality f)

set_option backward.isDefEq.respectTransparency true in
/-- The ordinary cube on one completed module, checked on unit generators. -/
theorem cube_component {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (MEY : CompletionUnit.OrdinaryModel l E Y) (MEX : CompletionUnit.OrdinaryModel l E X)
    (MLY : CompletionUnit.OrdinaryModel l L Y) (MLX : CompletionUnit.OrdinaryModel l L X)
    (b : isoReductionIntegralInverse l E g ⋙ integralOrdinaryScalar l E L ι X ≅
      integralOrdinaryScalar l E L ι Y ⋙ isoReductionIntegralInverse l L g)
    (hb : ∀ (N : scalarReductionSource l E Y) (U : X.ProEt)
      (x : N.val.obj (op ((proEtaleIsoPostcompose g).obj U)))
      (a : (completedIntegralCoefficientSheafUnrestricted l L Y).obj.obj
        (op ((proEtaleIsoPostcompose g).obj U))),
      (b.hom.app N).val.app (op U)
          (integralOrdinaryTensorSection l E L ι X
            ((isoReductionIntegralInverse l E g).obj N) (op U)
            ((isoReductionCompletedMap l L g).hom.hom.app (op U) a) x) =
        integralOrdinaryTensorSection l E L ι Y N
          (op ((proEtaleIsoPostcompose g).obj U)) a x)
    (αX : MEX.tensor ⋙ (integralComparisonSequenceScalarModel l E L ι X).E ≅
        integralOrdinaryScalar l E L ι X ⋙ MLX.tensor)
    (αY : MEY.tensor ⋙ (integralComparisonSequenceScalarModel l E L ι Y).E ≅
        integralOrdinaryScalar l E L ι Y ⋙ MLY.tensor)
    (βE : MEY.tensor ⋙ integralComparisonSequencePullback l E g ≅
        isoReductionIntegralInverse l E g ⋙ MEX.tensor)
    (βL : MLY.tensor ⋙ integralComparisonSequencePullback l L g ≅
        isoReductionIntegralInverse l L g ⋙ MLX.tensor)
    (hαX : PodQuotientTransition.ScalarNormalized l E L ι X MEX MLX αX)
    (hαY : PodQuotientTransition.ScalarNormalized l E L ι Y MEY MLY αY)
    (hβE : PodQuotientTransition.ReindexNormalized l E g MEY MEX βE)
    (hβL : PodQuotientTransition.ReindexNormalized l L g MLY MLX βL)
    (N : scalarReductionSource l E Y) :
    αX.inv.app ((isoReductionIntegralInverse l E g).obj N) ≫
        (integralComparisonSequenceScalarModel l E L ι X).E.map (βE.inv.app N) ≫
        (integralComparisonSequenceScalarPullback l E L ι g).hom.app (MEY.tensor.obj N) =
      MLX.tensor.map (b.hom.app N) ≫ βL.inv.app ((integralOrdinaryScalar l E L ι Y).obj N) ≫
        (integralComparisonSequencePullback l L g).map (αY.inv.app N) := by
  rw [← cancel_epi (αX.hom.app ((isoReductionIntegralInverse l E g).obj N)),
    Iso.hom_inv_id_app_assoc]
  apply scalar_quotient_unit_ext l E L ι X MEX ((isoReductionIntegralInverse l E g).obj N)
  intro n U x
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply]
  have h1 : (isoReductionCompletedMap l L g).hom.hom.app (op U.unop) 1 = 1 :=
    map_one ((isoReductionCompletedMap l L g).hom.hom.app (op U.unop)).hom
  have hb1 : (b.hom.app N).val.app U
      (integralOrdinaryTensorSection l E L ι X ((isoReductionIntegralInverse l E g).obj N) U 1 x) =
      integralOrdinaryTensorSection l E L ι Y N
        (op ((proEtaleIsoPostcompose g).obj U.unop)) 1 x := by
    have := hb N U.unop x 1
    erw [h1] at this
    exact this
  have hβ := natIso_inv_apply_of_hom_apply βL _ _
    (hβL ((integralOrdinaryScalar l E L ι Y).obj N) n U.unop
      (integralOrdinaryTensorSection l E L ι Y N (op ((proEtaleIsoPostcompose g).obj U.unop)) 1 x))
  rw [hαX _ n U x]
  dsimp only [Functor.comp_obj] at hβ ⊢
  have hα := natIso_inv_apply_of_hom_apply αY N _
    (hαY N n (op ((proEtaleIsoPostcompose g).obj U.unop)) x)
  dsimp only [Functor.comp_obj] at hα
  rw [unitSection_map, hb1, hβ]
  have hβE' := natIso_inv_apply_of_hom_apply βE N _
    (hβE N n U.unop x)
  dsimp only [Functor.comp_obj] at hβE'
  have r1 := (presheaf_naturality_apply ((integralComparisonSequencePullback l L g).map
    (αY.inv.app N)) (Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U.unop)).op
    (integralComparisonSequenceGenerator l L g
      (MLY.tensor.obj ((integralOrdinaryScalar l E L ι Y).obj N)) n
      ((proEtaleIsoPostcompose g).obj U.unop)
      (PodQuotientTransition.unitSection l L Y MLY ((integralOrdinaryScalar l E L ι Y).obj N) n
        (op ((proEtaleIsoPostcompose g).obj U.unop))
        (integralOrdinaryTensorSection l E L ι Y N
          (op ((proEtaleIsoPostcompose g).obj U.unop)) 1 x)))).trans
    (congrArg _ ((generator_map l L g (αY.inv.app N) n
      ((proEtaleIsoPostcompose g).obj U.unop) _).trans
      (congrArg _ hα)))
  have l1 := tensorSection_one_map l E L ι X (βE.inv.app N) (op (n, U.unop))
    (PodQuotientTransition.unitSection l E X MEX ((isoReductionIntegralInverse l E g).obj N) n U x)
  have l3 := (tensorSection_one_restrict l E L ι X
    ((integralComparisonSequencePullback l E g).obj (MEY.tensor.obj N))
    (Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U.unop)).op
    (integralComparisonSequenceGenerator l E g (MEY.tensor.obj N) n
      ((proEtaleIsoPostcompose g).obj U.unop)
      (PodQuotientTransition.unitSection l E Y MEY N n
        (op ((proEtaleIsoPostcompose g).obj U.unop)) x))).symm
  have l4 := presheaf_naturality_apply
    ((integralComparisonSequenceScalarPullback l E L ι g).hom.app (MEY.tensor.obj N))
    (Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U.unop)).op
    (integralComparisonSequenceTensorSection l E L ι X
      ((integralComparisonSequencePullback l E g).obj (MEY.tensor.obj N))
      (op (n, (proEtaleBaseChange g).obj ((proEtaleIsoPostcompose g).obj U.unop))) 1
      (integralComparisonSequenceGenerator l E g (MEY.tensor.obj N) n
        ((proEtaleIsoPostcompose g).obj U.unop)
        (PodQuotientTransition.unitSection l E Y MEY N n
          (op ((proEtaleIsoPostcompose g).obj U.unop)) x)))
  have l5 := congrArg (((integralComparisonSequencePullback l L g).obj
      ((integralComparisonSequenceScalarModel l E L ι Y).E.obj (MEY.tensor.obj N))).val.presheaf.map
        (Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U.unop)).op)
    (scalarPullback_generator l E L ι g (MEY.tensor.obj N) n ((proEtaleIsoPostcompose g).obj U.unop)
      (PodQuotientTransition.unitSection l E Y MEY N n
        (op ((proEtaleIsoPostcompose g).obj U.unop)) x))
  exact (congrArg _ (l1.trans ((congrArg _ hβE').trans l3))).trans (l4.trans (l5.trans r1.symm))

end OrdinaryQuotientCube
end WeilConjectures
