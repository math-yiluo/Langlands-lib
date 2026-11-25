/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Integral.IntegralResidueTensorPresentation
public import WeilConjectures.CategoryTheory.ModuleObjects.ResidueOrdinary.IntegralResidueOrdinaryMonoidal
public import WeilConjectures.AlgebraicGeometry.IntegralResidueOrdinaryTensorSquare
public import WeilConjectures.CategoryTheory.Integral.IntegralResidueTensorModel
public import WeilConjectures.AlgebraicGeometry.IntegralResidueTensorPullPresentation

/-! # Ordinary pullback data and the derived residue tensor square

Source: Bhatt--Scholze, Lemma 6.5.9(3) and Remark 6.8.15.
(blueprint: def-weil-pbc-integral-residue-tensor-pull-presentation)
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance instEssentiallySmallProfinite_integralResidueTensorPullPresentation
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

attribute [local instance 20000] CategoryTheory.tensorPresentationMonoidal

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local instance 20000] sheafBraidedCategory

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- Pullback identifies the restricted residue regular coefficient in degree zero.
The isomorphism is constructed using exact pullback and its ordinary unit comparison.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(blueprint: def-weil-pbc-integral-residue-tensor-pull-presentation) -/
@[irreducible] noncomputable def residueExchangeCoefficientPullIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (residueExchangeUpperStar (integralCoeff ℓ E) f).obj
        (residueExchangeCoefficient ℓ E Y) ≅ residueExchangeCoefficient ℓ E X :=
  residueRestrictedRegularPullIso (integralCoeff ℓ E)
    (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E))
    (integralReductionMap ℓ E) f

/-- The pulled coefficient comparison commutes with the named pullback counit.

The coefficient isomorphism is the exact single-object comparison followed by
the ordinary coefficient pullback. Its counit equation is the generic exact-F
single comparison equation, applied to these fixed ordinary modules.

Source: Bhatt--Scholze, Remark 6.8.15; exact pullback and the fixed single comparisons.
(blueprint: def-weil-pbc-integral-residue-tensor-pull-presentation) -/
theorem residueExchangeCoefficientPullIso_counit
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    let F := (f)^*⟦integralCoeff ℓ E⟧
    let B := Functor.tensorModelCoefficient (residueExchangeOrdinaryCoefficient ℓ E Y)
    let B' := residueExchangeOrdinaryCoefficient ℓ E X
    let A := Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)
    let e := residueOrdinaryRestrictedRegularPullIso (integralCoeff ℓ E) A
      (integralReductionMap ℓ E) f
    let eH := (F.mapHomotopyCategoryFactors (.up ℤ)).app
        ((CochainComplex.singleFunctor _ 0).obj
          (residueExchangeOrdinaryCoefficient ℓ E Y)) ≪≫
      (HomotopyCategory.quotient _ (.up ℤ)).mapIso
        ((F.mapCochainComplexSingleFunctor 0).app
          (residueExchangeOrdinaryCoefficient ℓ E Y) ≪≫
            (HomologicalComplex.single _ (.up ℤ) 0).mapIso e)
    (residueExchangeCoefficientPullIso ℓ E f).inv ≫
      (residueExchangeUpperStar (integralCoeff ℓ E) f).map
        (Functor.tensorModelCoefficientIso (residueExchangeOrdinaryCoefficient ℓ E Y)).hom ≫
      (residueExchangeUpperStarCounit (integralCoeff ℓ E) f).app B =
      (Functor.tensorModelCoefficientIso B').hom ≫ DerivedCategory.Qh.map eH.inv := by
  intro F B B' A e eH
  have h := Functor.tensorModelCoefficientIso_counit F
    (residueExchangeOrdinaryCoefficient ℓ E Y) B' e
  dsimp only at h
  unfold residueExchangeCoefficientPullIso
  rw [residueRestrictedRegularPullIso_def]
  unfold residueExchangeUpperStar residueExchangeUpperStarCounit
  dsimp only [id]
  simpa only [F, B, B', A, e, eH] using h

/-- The tensor presentation on X, with its coefficient identified with pullback from Y.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(blueprint: def-weil-pbc-integral-residue-tensor-pull-presentation) -/
@[irreducible] noncomputable def residueExchangeTensorPullIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    residueExchangeReduction ℓ E X ⋙ residueExchangeRestriction ℓ E X ≅
      tensorRight ((residueExchangeUpperStar (integralCoeff ℓ E) f).obj
        (residueExchangeCoefficient ℓ E Y)) :=
  residueExchangeTensorIso ℓ E X ≪≫
    (curriedTensor (residueExchangeDerived (integralCoeff ℓ E) X)).flip.mapIso
      (residueExchangeCoefficientPullIso ℓ E f).symm

end AlgebraicGeometry.ProEtale.CondensedRing
