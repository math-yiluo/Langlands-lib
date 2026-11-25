/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition

import all WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement

/-! # Consecutive reduction for integral scalar pullback comparisons

Source: Stacks 03D2, 03EL, and 07A4; Bhatt--Scholze, Definition 3.4.10.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory Opposite
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] integralOrdinaryScalar integralOrdinaryTensorSection
  integralCompletedScalarMap
  completedIntegralCoefficientSheafUnrestricted HasDerivedCategory.standard
  unrestrictedIntegralReductionFunctor unrestrictedIntegralTransition
  integralOperationsPullbackTransition
  AlgebraicGeometry.Scheme.coefficientProEtaleModuleAdjunction
  AlgebraicGeometry.Scheme.coefficientProEtaleModulePullback Functor.leftAdjoint

private theorem scalar_pullback_hom_ext {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (m n : ℕ)
    (q : integralCoefficientSheaf l E X m ⟶ integralCoefficientSheaf l L X n)
    (hq : integralOperationsProjection l E X m ≫ q =
      (sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (integralCompletedScalarMap l E L ι X) ≫
          integralOperationsProjection l L X n)
    (M : integralTowerModules l E Y) (N : integralOperationsFiniteModules l L X n)
    (a b : (integralOrdinaryScalar l E L ι X).obj
        ((SheafOfModules.restrictScalars (integralOperationsProjection l E X m)).obj
          ((integralOperationsLevelPullback l E f m).obj
            ((unrestrictedIntegralReductionFunctor l E Y m).obj M))) ⟶
      (SheafOfModules.restrictScalars (integralOperationsProjection l L X n)).obj N)
    (hab : ∀ (V : Y.ProEt) (x : M.val.obj (op V)),
      a.val.app (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V))
          (integralOrdinaryTensorSection l E L ι X _
            (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V)) 1
            (integralOperationsPullbackGenerator l E f m _ V
              (unrestrictedIntegralTensorSection l E Y m M (op V) 1 x))) =
      b.val.app (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V))
          (integralOrdinaryTensorSection l E L ι X _
            (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V)) 1
            (integralOperationsPullbackGenerator l E f m _ V
              (unrestrictedIntegralTensorSection l E Y m M (op V) 1 x)))) : a = b := by
  let adj := scalarAdjunction l E L ι X
  apply (adj.homEquiv _ _).injective
  let π := integralOperationsProjection l E X m
  let β := (sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (integralCompletedScalarMap l E L ι X) ≫
      integralOperationsProjection l L X n
  let A := (integralOperationsLevelPullback l E f m).obj
    ((unrestrictedIntegralReductionFunctor l E Y m).obj M)
  let a' : (SheafOfModules.restrictScalars π).obj A ⟶
      (SheafOfModules.restrictScalars β).obj N := adj.homEquiv _ _ a
  let b' : (SheafOfModules.restrictScalars π).obj A ⟶
      (SheafOfModules.restrictScalars β).obj N := adj.homEquiv _ _ b
  let : Presheaf.IsLocallySurjective (AlgebraicGeometry.Scheme.ProEt.topology X) π.hom :=
    completedProjection_locallySurjective l E X m
  let lift := SheafOfModules.IntegralScalarProof.liftMap π β q hq A N
  have hl : lift a' = lift b' := by
    apply ((integralOperationsPullbackAdjunction l E f m).homEquiv _ _).injective
    apply tensorSection_ext (completedIntegralCommRingProjectionUnrestricted l E Y m)
      (unrestrictedIntegralReductionFunctor l E Y m) (unrestrictedReduction_obj l E Y m)
    intro V x
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    with_unfolding_all
      change a'.val.app _ (integralOperationsPullbackGenerator l E f m _ V.unop
        (unrestrictedIntegralTensorSection l E Y m M V 1 x)) =
          b'.val.app _ (integralOperationsPullbackGenerator l E f m _ V.unop
            (unrestrictedIntegralTensorSection l E Y m M V 1 x))
    with_unfolding_all
      change a.val.app _ ((adj.unit.app _).val.app _ _) =
        b.val.app _ ((adj.unit.app _).val.app _ _)
    dsimp only [adj]
    rw [scalarAdjunction_unit]
    exact hab V.unop x
  ext U x
  with_unfolding_all exact congrArg (fun k ↦ k.val.app U x) hl

/-- Normalized scalar pullback level maps commute with a single quotient reduction.
Source: Stacks, Modules on Sites, Tags 03D2 and 03EL; Cohomology on Sites,
Tag 07A4; Bhatt--Scholze, Definition 3.4.10.
(blueprint: lem-pur-integral-scalar-pullback-level-reduction).
Proof: in each degree use the scalar-extension adjunction to remove the outer
ordinary scalar tensor. The finite-reduction adjunction and the pullback
Kan-extension adjunction then reduce equality to generators
1 tensor f-star(1 tensor x) over the base-changed objects. The hypothesis fixes
the action of each level map on these generators. The recorded pullback
transition reduces its input generator, and the quotient tensor transition sends
1 tensor x to 1 tensor x. Naturality of the scalar tensor unit therefore makes
both routes equal to f-star(1 tensor (1 tensor x)) at level n. Completed-ring
linearity extends this to all finite coefficients, since the completed projection
onto the finite quotient is locally surjective. Kan-extension generation,
sheafification and separatedness identify the module maps; chain-map and
natural-transformation extensionality identify the transformations. No flatness
or nonempty-site assumption occurs. -/
theorem integralScalarPullbackLevelReduction {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y)
    (α : ∀ n : ℕ, integralOperationsPullbackLevel l E f n ⋙
        (integralOrdinaryScalar l E L ι X).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        integralOperationsPullbackLevel l L f n)
    (hα : ∀ (n : ℕ) (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (V : Y.ProEt)
        (x : (P.X i).val.obj (op V)),
        (((α n).app P).f i).val.app (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V))
          (integralOrdinaryTensorSection l E L ι X
            (((integralOperationsPullbackLevel l E f n).obj P).X i)
            (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V)) 1
            (integralOperationsPullbackGenerator l E f n
              (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V
              (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) 1 x))) =
        integralOperationsPullbackGenerator l L f n
          (((unrestrictedIntegralFiniteComplex l L Y n).obj
            (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)).X i) V
          (unrestrictedIntegralTensorSection l L Y n
            ((integralOrdinaryScalar l E L ι Y).obj (P.X i)) (op V) 1
            (integralOrdinaryTensorSection l E L ι Y (P.X i) (op V) 1 x))) (n : ℕ) :
    Functor.whiskerRight (integralOperationsPullbackTransition l E f n)
        ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (ComplexShape.up ℤ)) ≫
      α n =
    α (n + 1) ≫ Functor.whiskerLeft
      ((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (ComplexShape.up ℤ))
      (integralOperationsPullbackTransition l L f n) := by
  let c := sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let q := integralCoefficientSheafTransition l E X n ≫
    c.map (integralScalarQuotientSheafMap l E L ι X n)
  have hq : integralOperationsProjection l E X (n + 1) ≫ q =
      c.map (integralCompletedScalarMap l E L ι X) ≫
        integralOperationsProjection l L X n := by
    dsimp only [q]
    have hs : integralOperationsProjection l E X (n + 1) ≫
        integralCoefficientSheafTransition l E X n = integralOperationsProjection l E X n :=
      integralProjection_step l E X n
    rw [← Category.assoc, hs]
    have hc : integralCompletedScalarMap l E L ι X ≫
        completedIntegralCommRingProjectionUnrestricted l L X n =
        completedIntegralCommRingProjectionUnrestricted l E X n ≫
          integralScalarQuotientSheafMap l E L ι X n := by
      simpa only [integralCompletedScalarMap, integralScalarRho] using
        (integralCompletedScalarMap_existsUnique l E L ι X).exists.choose_spec n
    exact (c.map_comp _ _).symm.trans
      ((congrArg c.map hc.symm).trans (c.map_comp _ _))
  have hτ (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
      (P : CochainComplex (integralTowerModules l F Y) ℤ) (i : ℤ) (V : Y.ProEt)
      (x : (P.X i).val.obj (op V)) :
      (((integralOperationsPullbackTransition l F f n).app P).f i).val.app
          (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V))
        (integralOperationsPullbackGenerator l F f (n + 1) _ V
          (unrestrictedIntegralTensorSection l F Y (n + 1) (P.X i) (op V) 1 x)) =
      integralOperationsPullbackGenerator l F f n
        (((unrestrictedIntegralFiniteComplex l F Y n).obj P).X i) V
        (unrestrictedIntegralTensorSection l F Y n (P.X i) (op V) 1 x) := by
    have hp := (integralOperationsPullbackTransition_existsUnique l F f n).exists.choose_spec
      P i V (unrestrictedIntegralTensorSection l F Y (n + 1) (P.X i) (op V) 1 x)
    have hr : (((unrestrictedIntegralTransition l F Y n).app P).f i).val.app (op V)
        (unrestrictedIntegralTensorSection l F Y (n + 1) (P.X i) (op V) 1 x) =
        unrestrictedIntegralTensorSection l F Y n (P.X i) (op V) 1 x := by
      simpa only [unrestrictedIntegralTransition, map_one] using
        (unrestrictedIntegralTransition_existsUnique l F Y n).exists.choose_spec P i (op V) 1 x
    with_unfolding_all
      simpa only [integralOperationsPullbackTransition, hr] using hp
  apply NatTrans.ext
  funext P
  apply HomologicalComplex.hom_ext
  intro i
  apply scalar_pullback_hom_ext l E L ι f (n + 1) n q hq (P.X i)
  intro V x
  change (((α n).app P).f i).val.app _
      (((integralOrdinaryScalar l E L ι X).map
        (((integralOperationsPullbackTransition l E f n).app P).f i)).val.app _
          (integralOrdinaryTensorSection l E L ι X _ _ 1
            (integralOperationsPullbackGenerator l E f (n + 1) _ V
              (unrestrictedIntegralTensorSection l E Y (n + 1) (P.X i) (op V) 1 x)))) =
    (((integralOperationsPullbackTransition l L f n).app
      (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P)).f i).val.app _
        ((((α (n + 1)).app P).f i).val.app _
          (integralOrdinaryTensorSection l E L ι X _ _ 1
            (integralOperationsPullbackGenerator l E f (n + 1) _ V
              (unrestrictedIntegralTensorSection l E Y (n + 1) (P.X i) (op V) 1 x))))
  erw [scalar_map_tensor, hτ E P i V x, hα n P i V x, hα (n + 1) P i V x]
  exact (hτ L
    (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P) i V
    (integralOrdinaryTensorSection l E L ι Y (P.X i) (op V) 1 x)).symm

end WeilConjectures
