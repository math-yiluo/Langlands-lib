/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Finite.IntegralFiniteScalarPullOrdinary
import WeilConjectures.SixFunctors.IntegralSystemRealization.Finite.FiniteScalarRestrictionDirectSections
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! # Finite scalar pullback in the canonical quotient coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  WeilConjectures.pullbackTensorCalculus
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
attribute [local implicit_reducible] WeilConjectures.PurCompactSupport.completed
attribute [local implicit_reducible] WeilConjectures.integralCoefficientSheaf
  WeilConjectures.integralCoefficientCommRingSheaf
attribute [local instance] WeilConjectures.coefficientFiniteExtensionAdditive
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem finite_mate_projection
    {A B C D J K : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category J] [Category K]
    {F : A ⥤ B} {R : B ⥤ A} {RX : B ⥤ D} {LX : D ⥤ B}
    {RY : A ⥤ C} {LY : C ⥤ A} {S : C ⥤ D} {T : D ⥤ C}
    {EX : D ⥤ K} {EY : C ⥤ J} {V : J ⥤ K} {U : K ⥤ J}
    {QX : B ⥤ K} {UX : K ⥤ B} {QY : A ⥤ J} {UY : J ⥤ A}
    (a : F ⊣ R) (b : RX ⊣ LX) (c : RY ⊣ LY) (d : S ⊣ T)
    (e : V ⊣ U) (x : QX ⊣ UX) (y : QY ⊣ UY)
    (px : LX ⟶ EX ⋙ UX) (py : LY ⟶ EY ⋙ UY)
    (v : T ⋙ LY ⟶ LX ⋙ R) (de : T ⋙ EY ⟶ EX ⋙ U)
    (δ : U ⋙ UY ≅ UX ⋙ R)
    (q : F ⋙ RX ⟶ RY ⋙ S) (ρX : QX ⟶ RX ⋙ EX) (ρY : QY ⟶ RY ⋙ EY)
    (ev : EY ⋙ V ≅ S ⋙ EX) (ν : F ⋙ QX ⟶ QY ⋙ V)
    (hq : ∀ M, (a.comp b).homEquiv M _ (q.app M) =
      (c.comp d).unit.app M ≫ v.app (S.obj (RY.obj M)))
    (hx : ∀ M, x.homEquiv M _ (ρX.app M) = b.unit.app M ≫ px.app (RX.obj M))
    (hy : ∀ M, y.homEquiv M _ (ρY.app M) = c.unit.app M ≫ py.app (RY.obj M))
    (he : ∀ N, e.homEquiv _ _ (ev.hom.app N) =
      EY.map (d.unit.app N) ≫ de.app (S.obj N))
    (hν : ∀ M, (a.comp x).homEquiv M _ (ν.app M) =
      (y.comp e).unit.app M ≫ δ.hom.app (V.obj (QY.obj M)))
    (hp : ∀ Z, v.app Z ≫ R.map (px.app Z) =
      py.app (T.obj Z) ≫ UY.map (de.app Z) ≫ δ.hom.app (EX.obj Z))
    (M : A) :
    ρX.app (F.obj M) ≫ EX.map (q.app M) ≫ ev.inv.app (RY.obj M) =
      ν.app M ≫ V.map (ρY.app M) := by
  apply (cancel_mono (ev.hom.app (RY.obj M))).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  apply ((a.comp x).homEquiv M _).injective
  erw [Category.comp_id]
  conv_lhs => rw [Adjunction.comp_homEquiv]
  change a.homEquiv M _ (x.homEquiv _ _ (ρX.app (F.obj M) ≫ EX.map (q.app M))) = _
  rw [x.homEquiv_naturality_right, hx]
  have hpx := px.naturality (q.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hpx
  rw [Category.assoc, ← hpx]
  change a.homEquiv M _
    (b.unit.app (F.obj M) ≫ LX.map (q.app M) ≫ px.app (S.obj (RY.obj M))) = _
  rw [← Category.assoc, a.homEquiv_naturality_right]
  have hqm := hq M
  rw [Adjunction.comp_homEquiv] at hqm
  change a.homEquiv M _ (b.homEquiv _ _ (q.app M)) = _ at hqm
  rw [← b.homEquiv_unit, hqm, Category.assoc, hp]
  rw [Adjunction.comp_unit_app]
  simp only [Category.assoc]
  have hpy := py.naturality (d.unit.app (RY.obj M))
  dsimp only [Functor.comp_map] at hpy
  rw [reassoc_of% hpy, ← reassoc_of% (hy M), ← UY.map_comp_assoc, ← he]
  rw [Adjunction.homEquiv_naturality_right, hν]
  rw [Category.assoc, ← δ.hom.naturality]
  simp only [Adjunction.homEquiv_unit, Adjunction.comp_unit_app,
    Functor.comp_map, Functor.map_comp, Category.assoc]
  have hu := e.unit.naturality (ρY.app M)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hu
  rw [← UY.map_comp_assoc, hu]
  simp only [Functor.map_comp, Functor.comp_obj, Category.assoc]

private def finiteProjection (W : Scheme.{u}) (n : ℕ) :
    pullbackTensorOrdinaryLimit l E W ⟶
      coefficientSequenceEvaluation l E W n ⋙ scalarReductionRestriction l E W n :=
  Functor.whiskerLeft (coefficientSequenceRestriction l E W) (lim.π (op n)) ≫
    (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom

/-- Finite evaluation of the ordinary reduction and pullback mate.
Source: Stacks Tags 06YY and 0D6E (blueprint: lem-sf-integral-reduction-pull-ordinary-square). -/
theorem integralReductionPullOrdinarySquare (a : OrdinaryLimitModel l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) (M : integralTowerModules l E Y) :
    (pullbackTensorReductionEvaluation l E X n).hom.app ((integralOrdinaryPull l E f).obj M) ≫
        (coefficientSequenceEvaluation l E X n).map ((a.reductionPull l E f).hom.app M) ≫
        (pullbackTensorSequenceInverseEvaluation l E f n).inv.app
          ((pullbackTensorOrdinaryReduction l E Y).obj M) =
      (ordinaryFiniteScalarPull l E f n).hom.app M ≫
        (integralOperationsLevelPullback l E f n).map
          ((pullbackTensorReductionEvaluation l E Y n).hom.app M) := by
  let ar := proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull f)
  let ax := pullbackTensorFiniteAdjunction l E X n
  let ay := pullbackTensorFiniteAdjunction l E Y n
  let bx := pullbackTensorOrdinaryAdjunction l E X
  let by_ := pullbackTensorOrdinaryAdjunction l E Y
  let s := pullbackTensorSequenceAdjunction l E f
  let e := coefficientProEtaleModuleAdjunction.{u, u} f
    (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1))))
  apply finite_mate_projection ar bx by_ s e ax ay
    (finiteProjection l E X n) (finiteProjection l E Y n)
    (a.comparison f).hom (pullbackTensorSequenceDirectEvaluation l E f n).hom
    (finiteScalarRestrictionDirect l E f n)
    (a.reductionPull l E f).hom
    (pullbackTensorReductionEvaluation l E X n).hom
    (pullbackTensorReductionEvaluation l E Y n).hom
    (pullbackTensorSequenceInverseEvaluation l E f n)
    (ordinaryFiniteScalarPull l E f n).hom
  · intro N
    have hc : conjugateIsoEquiv (by_.comp s) (ar.comp bx)
        (a.reductionPull l E f) = a.comparison f := by
      change (conjugateIsoEquiv _ _
        ((conjugateIsoEquiv _ _).symm (a.comparison f).symm)).symm = _
      rw [Equiv.apply_symm_apply]
      rfl
    have h := unit_conjugateEquiv (by_.comp s) (ar.comp bx)
      (a.reductionPull l E f).hom N
    rw [← conjugateIsoEquiv_apply_hom, hc] at h
    exact h.symm
  · intro N
    exact (pullbackTensorReductionEvaluation_existsUnique l E X n).exists.choose_spec N
  · intro N
    exact (pullbackTensorReductionEvaluation_existsUnique l E Y n).exists.choose_spec N
  · intro N
    exact (pullbackTensorSequenceInverseEvaluation_existsUnique l E f n).exists.choose_spec N
  · intro N
    exact ordinaryFiniteScalarPull_transpose l E f n N
  · intro Z
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext x
    have h := a.projections f Z n V.unop x
    apply eq_of_heq
    exact (heq_of_eq h).trans (finiteScalarRestrictionDirect_sections l E f n
      ((coefficientSequenceEvaluation l E X n).obj Z) V.unop _).symm

/-- Finite evaluation of the ordinary reduction and pullback mate.
Source: Stacks Tags 06YY and 0D6E (blueprint: lem-sf-integral-reduction-pull-ordinary-square). -/
theorem integralReductionPullOrdinaryComplex (a : OrdinaryLimitModel l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).map
        (a.reductionPullComplex l E f P) ≫
      (pullbackTensorInverseEvaluationComplex l E f n).inv.app
        (((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P) ≫
      ((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).map
        ((pullbackTensorReductionEvaluationComplex l E Y n).inv.app P) =
    (pullbackTensorReductionEvaluationComplex l E X n).inv.app
        (((integralOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj P) ≫
      ordinaryFiniteScalarPullComplex l E f n P := by
  apply HomologicalComplex.hom_ext
  intro i
  change (coefficientSequenceEvaluation l E X n).map
      ((a.reductionPull l E f).hom.app (P.X i)) ≫
      (pullbackTensorSequenceInverseEvaluation l E f n).inv.app
        ((pullbackTensorOrdinaryReduction l E Y).obj (P.X i)) ≫
      (integralOperationsLevelPullback l E f n).map
        ((pullbackTensorReductionEvaluation l E Y n).inv.app (P.X i)) =
    (pullbackTensorReductionEvaluation l E X n).inv.app
        ((integralOrdinaryPull l E f).obj (P.X i)) ≫
      (ordinaryFiniteScalarPull l E f n).hom.app (P.X i)
  apply (cancel_epi ((pullbackTensorReductionEvaluation l E X n).hom.app _)).1
  erw [reassoc_of% (integralReductionPullOrdinarySquare l E a f n (P.X i))]
  simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  erw [(integralOperationsLevelPullback l E f n).map_id, Category.comp_id]

end WeilConjectures.IntegralSystemRealization
