/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarPullbackQuotientFormula
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarPullbackLevelReduction
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarFiniteReductionMaps
import all WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import all WeilConjectures.SixFunctors.SequenceModuleEvaluation.SequenceModulePullbackEvaluation
import all WeilConjectures.TraceFormula.Ordinary.OrdinaryQuotientPullbackSuccessor
import all WeilConjectures.TraceFormula.Ordinary.OrdinaryQuotientPullbackTowerComparison
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems

/-! # The strict quotient square for scalar change and pullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ScalarExtensionTower

attribute [local irreducible] HasDerivedCategory.standard
  integralOrdinaryScalar integralOrdinaryTensorSection integralComparisonSequenceScalarModel
  coefficientSequenceRestriction integralComparisonSequenceScalarPullback
  completedIntegralCommRingSheafUnrestricted unrestrictedIntegralTensorSection

attribute [local implicit_reducible] integralOperationsPullbackTowerFunctor
  integralOperationsPullbackLevel integralOperationsRestrict
  integralCoefficientCommRingSheaf integralCoefficientSheaf
  integralOperationsLevelPullback unrestrictedIntegralReductionFunctor
  integralComparisonSequencePullback integralComparisonSequenceDirectImage

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

private theorem section_cast_cancel {A B : AddCommGrpCat.{u + 1}} (h : A = B) (x : A) :
    (eqToHom h.symm) ((eqToHom h) x) = x := by
  subst h
  rfl

private theorem strict_pullback_evaluation_section (Y : Scheme.{u})
    (M : coefficientSequenceModules l E Y) (n : ℕ) (U : Y.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E Y n).obj M).val.obj U) :
    coefficientEvaluationSection l E Y M n U
      (integralComparisonSequenceSection l E Y M n U x) = x := by
  exact section_cast_cancel _ _

private theorem strict_pullback_scalar_section (X : Scheme.{u})
    {N N' : integralTowerModules l E X} (g : N ⟶ N')
    (t : integralOrdinaryScalar l E L ι X ≅ completedOrdinaryScalarExtension l E L ι X)
    (ht : ∀ (N : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj U) (x : N.val.obj U),
      (t.hom.app N).val.app U (integralOrdinaryTensorSection l E L ι X N U s x) =
        completedScalarTensorSection l E L ι X N U s x)
    (U : X.ProEtᵒᵖ) (x : N.val.obj U) (y : N'.val.obj U) (h : g.val.app U x = y) :
    (t.hom.app N').val.app U
      (((integralOrdinaryScalar l E L ι X).map g).val.app U
        (integralOrdinaryTensorSection l E L ι X N U 1 x)) =
      completedScalarTensorSection l E L ι X N' U 1 y := by
  exact (congrArg ((t.hom.app N').val.app U)
    ((scalar_map_tensor l E L ι X g U 1 x).trans
      (congrArg (integralOrdinaryTensorSection l E L ι X N' U 1) h))).trans (ht N' U 1 y)

/-- The strict scalar/pullback quotient square on every level and transition.
Source: Stacks 03D3, 06YY and 07A4, the nested generator calculation.
(blueprint: lem-pur-scalar-pullback-strict-tower).

Proof: test each degree and quotient level on 1 tensor f-star(1 tensor x).
The inverse of qE sends the inner generator to the pullback of the section
specified by kappa inverse. Naturality of ordinary scalar tensors and the
normalization of t convert its outer tensor to the completed scalar model.
The coordinates of a reduce its coefficient modulo l^n. The normalized system
scalar/pullback associator sends the result to the pullback of the unit scalar
tensor. The formula hq then gives f-star(1 tensor (1 tensor x)), exactly the
normalization of scalarPullbackLevel. Three adjunctions and local surjectivity
of the quotient coefficient map detect equality on these generators. The maps
are already strict tower maps, so degreewise equality retains all transitions. -/
theorem scalarPullbackStrictTower {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E Y n).obj P.obj)
    (qE : (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequencePullback l E f).mapHomologicalComplex
          (.up ℤ)).obj C)).asFunctor ≅
      (integralOperationsPullbackTowerFunctor l E f).obj P.obj)
    (hqE : ∀ (n : ℕ) (i : ℤ) (U : Y.ProEt)
      (x : (C.X i).val.obj (op (n, U))),
      ((qE.hom.app (op n)).f i).val.app (op ((Scheme.proEtaleBaseChange f).obj U))
        (integralComparisonRestrictedSection l E X
          ((integralComparisonSequencePullback l E f).obj (C.X i)) n
          (op ((Scheme.proEtaleBaseChange f).obj U))
          (integralComparisonSequenceGenerator l E f (C.X i) n U x)) =
        integralOperationsPullbackGenerator l E f n
          (((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj).X i) U
          (((κ n).hom.f i).val.app (op U)
            (coefficientEvaluationSection l E Y (C.X i) n (op U) x)))
    (q : (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequencePullback l L f).mapHomologicalComplex (.up ℤ)).obj
          (((integralComparisonSequenceScalarModel l E L ι Y).E.mapHomologicalComplex
            (.up ℤ)).obj C))).asFunctor ≅
      (integralOperationsPullbackTowerFunctor l L f).obj
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P.obj))
    (hq : ScalarPullbackQuotientFormula l E L ι f P C κ q)
    (t : integralOrdinaryScalar l E L ι X ≅ completedOrdinaryScalarExtension l E L ι X)
    (ht : ∀ (N : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj U) (x : N.val.obj U),
      (t.hom.app N).val.app U (integralOrdinaryTensorSection l E L ι X N U s x) =
        completedScalarTensorSection l E L ι X N U s x)
    (a : (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequencePullback l E f).mapHomologicalComplex
          (.up ℤ)).obj C)).asFunctor ⋙ completedOrdinaryScalarComplex l E L ι X ⟶
      (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel l E L ι X).E.mapHomologicalComplex (.up ℤ)).obj
          (((integralComparisonSequencePullback l E f).mapHomologicalComplex
            (.up ℤ)).obj C))).asFunctor)
    (ha : ∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj U)
      (x : (((integralComparisonSequencePullback l E f).obj (C.X i)).val.obj
        (op (n, U.unop)))),
      ((a.app (op n)).f i).val.app U
        (completedScalarTensorSection l E L ι X
          (((coefficientSequenceRestriction l E X).obj
            ((integralComparisonSequencePullback l E f).obj (C.X i))).obj (op n)) U s
          (integralComparisonRestrictedSection l E X
            ((integralComparisonSequencePullback l E f).obj (C.X i)) n U x)) =
        integralComparisonRestrictedSection l L X
          ((integralComparisonSequenceScalarModel l E L ι X).E.obj
            ((integralComparisonSequencePullback l E f).obj (C.X i))) n U
          (integralComparisonSequenceTensorSection l E L ι X
            ((integralComparisonSequencePullback l E f).obj (C.X i)) (op (n, U.unop))
            ((completedIntegralCommRingProjectionUnrestricted l L X n).hom.app U s) x)) :
    let H := ((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj C
    let CE := ((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj H
    let σ := (NatIso.mapHomologicalComplex
      (integralComparisonSequenceScalarPullback l E L ι f) (.up ℤ)).hom.app C
    let τ := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
      (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).map σ)
    Functor.whiskerRight qE.inv
        ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)) ≫
      Functor.whiskerLeft CE.asFunctor (NatIso.mapHomologicalComplex t (.up ℤ)).hom ≫
      a ≫ τ ≫ q.hom = (scalarPullbackTower l E L ι f).app P.obj := by
  intro H CE σ τ
  apply NatTrans.ext
  funext n
  apply HomologicalComplex.hom_ext
  intro i
  dsimp only [NatTrans.comp_app, HomologicalComplex.comp_f,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  with_unfolding_all
    apply scalar_pullback_hom_ext l E L ι f n.unop n.unop
      (scalarFiniteRingMap l E L ι X n.unop) (scalarProjectionRingSquare l E L ι X n.unop)
      (P.obj.X i)
      ((integralOperationsLevelPullback l L f n.unop).obj
        ((unrestrictedIntegralReductionFunctor l L Y n.unop).obj
          ((integralOrdinaryScalar l E L ι Y).obj (P.obj.X i))))
  intro U x
  let z := integralComparisonSequenceSection l E Y (C.X i) n.unop (op U)
    (((κ n.unop).inv.f i).val.app (op U)
      (unrestrictedIntegralTensorSection l E Y n.unop (P.obj.X i) (op U) 1 x))
  let w := integralComparisonRestrictedSection l E X
    ((integralComparisonSequencePullback l E f).obj (C.X i)) n.unop
    (op ((Scheme.proEtaleBaseChange f).obj U))
    (integralComparisonSequenceGenerator l E f (C.X i) n.unop U z)
  have hz : ((κ n.unop).hom.f i).val.app (op U)
      (coefficientEvaluationSection l E Y (C.X i) n.unop (op U) z) =
      unrestrictedIntegralTensorSection l E Y n.unop (P.obj.X i) (op U) 1 x := by
    have hc : coefficientEvaluationSection l E Y (C.X i) n.unop (op U) z =
        (((κ n.unop).inv.f i).val.app (op U)
          (unrestrictedIntegralTensorSection l E Y n.unop (P.obj.X i) (op U) 1 x)) :=
      strict_pullback_evaluation_section l E Y (C.X i) n.unop (op U) _
    rw [hc]
    exact congrArg (fun g ↦ (g.f i).val.app (op U)
      (unrestrictedIntegralTensorSection l E Y n.unop (P.obj.X i) (op U) 1 x))
        (κ n.unop).inv_hom_id
  have hqEw : ((qE.hom.app n).f i).val.app _ w =
      integralOperationsPullbackGenerator l E f n.unop _ U
        (unrestrictedIntegralTensorSection l E Y n.unop (P.obj.X i) (op U) 1 x) :=
    (hqE n.unop i U z).trans
      (congrArg (integralOperationsPullbackGenerator l E f n.unop _ U) hz)
  have hqEinv : ((qE.inv.app n).f i).val.app _
      (integralOperationsPullbackGenerator l E f n.unop _ U
        (unrestrictedIntegralTensorSection l E Y n.unop (P.obj.X i) (op U) 1 x)) = w := by
    have hi := congrArg (fun g ↦ ((g.app n).f i).val.app _ w) qE.hom_inv_id
    have hj := congrArg (fun y ↦ ((qE.inv.app n).f i).val.app _ y) hqEw.symm
    with_unfolding_all exact hj.trans hi
  have hlevel := (scalarPullbackTower_existsUnique l E L ι f).exists.choose_spec P.obj n.unop
  have hnorm := (scalarPullbackLevel_existsUnique l E L ι f n.unop).exists.choose_spec
    P.obj i U x
  with_unfolding_all
    change ((q.hom.app n).f i).val.app _
      (((τ.app n).f i).val.app _
        (((a.app n).f i).val.app _
          ((t.hom.app _).val.app _
            (((integralOrdinaryScalar l E L ι X).map ((qE.inv.app n).f i)).val.app _
              (integralOrdinaryTensorSection l E L ι X _
                (op ((Scheme.proEtaleBaseChange f).obj U)) 1
                (integralOperationsPullbackGenerator l E f n.unop _ U
                  (unrestrictedIntegralTensorSection l E Y n.unop (P.obj.X i) (op U) 1 x))))))) = _
  have hscalar := strict_pullback_scalar_section l E L ι X ((qE.inv.app n).f i) t ht
    (op ((Scheme.proEtaleBaseChange f).obj U)) _ w hqEinv
  refine (congrArg (fun y ↦ ((q.hom.app n).f i).val.app _
    (((τ.app n).f i).val.app _ (((a.app n).f i).val.app _ y))) hscalar).trans ?_
  refine (congrArg (fun y ↦ ((q.hom.app n).f i).val.app _
    (((τ.app n).f i).val.app _ y))
    (ha n.unop i (op ((Scheme.proEtaleBaseChange f).obj U)) 1
      (integralComparisonSequenceGenerator l E f (C.X i) n.unop U z))).trans ?_
  simp only [map_one]
  change ((q.hom.app n).f i).val.app _
    (((((coefficientSequenceRestriction l L X).map (σ.f i)).app n).val.app _)
      (integralComparisonRestrictedSection l L X _ n.unop _
        (integralComparisonSequenceTensorSection l E L ι X _
          (op (n.unop, (Scheme.proEtaleBaseChange f).obj U)) 1
          (integralComparisonSequenceGenerator l E f (C.X i) n.unop U z)))) = _
  erw [OrdinaryTowerProof.restriction_map_section]
  have hσ := (integralComparisonSequenceScalarPullback_existsUnique l E L ι f).exists.choose_spec
    (C.X i) n.unop U z
  change ((q.hom.app n).f i).val.app _
    (integralComparisonRestrictedSection l L X _ n.unop _
      (((integralComparisonSequenceScalarPullback l E L ι f).hom.app (C.X i)).val.app _
        (integralComparisonSequenceTensorSection l E L ι X _
          (op (n.unop, (Scheme.proEtaleBaseChange f).obj U)) 1
          (integralComparisonSequenceGenerator l E f (C.X i) n.unop U z)))) = _
  have hs := congrArg (fun y ↦ ((q.hom.app n).f i).val.app
      (op ((Scheme.proEtaleBaseChange f).obj U))
      (integralComparisonRestrictedSection l L X _ n.unop
        (op ((Scheme.proEtaleBaseChange f).obj U)) y)) hσ
  have hq' := hq n.unop i U x
  have htower := congrArg (fun g ↦ (g.f i).val.app
      (op ((Scheme.proEtaleBaseChange f).obj U))
      (integralOrdinaryTensorSection l E L ι X _
        (op ((Scheme.proEtaleBaseChange f).obj U)) 1
        (integralOperationsPullbackGenerator l E f n.unop _ U
          (unrestrictedIntegralTensorSection l E Y n.unop (P.obj.X i) (op U) 1 x)))) hlevel
  with_unfolding_all exact hs.trans (hq'.trans (hnorm.symm.trans htower.symm))

end WeilConjectures.ScalarExtensionTower
