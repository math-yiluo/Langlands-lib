/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicRealizationData

/-! # Normalized native realization before descent and smallness

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14
(blueprint: def-sf-locally-finite-adic-normalized-functor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option linter.all false

attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

attribute [local irreducible] sections CoefficientPresentation.integralMap
  completedTensorComparison

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

/-- Coefficient presentations and a triangulated common-stage functor with the specified
integral tensor formula and completion-map normalization. No Hom bijectivity, essential
image, or smallness is assumed. Those are separate properties to prove.
Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14, parent proof steps 2--5
(blueprint: def-sf-locally-finite-adic-normalized-functor). -/
structure FunctorData where
  [commutative : IsCommMonObj (abRing l X)]
  [sectionsAdditive : (sections l X).Additive]
  [sectionsLimits : PreservesFiniteLimits (sections l X)]
  [sectionsColimits : PreservesFiniteColimits (sections l X)]
  coefficient : ∀ E : Index l (PadicAlgCl l),
    CoefficientPresentation l X (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E)
  coefficient_scalar : ∀ (E L : Index l (PadicAlgCl l)) (h : E ≤ L),
    completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
        (Coefficient.{u} l (PadicAlgCl l) L)
        (coefficientInclusion l (PadicAlgCl l) E L h) X ≫
      (coefficient L).integralMap l X = (coefficient E).integralMap l X
  J : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X ⥤
    DerivedCategory (ProEtale.AdicSheaf l X)
  [additive : J.Additive]
  [shift : J.CommShift ℤ]
  triangulated : J.IsTriangulated
  integral : ∀ E : Index l (PadicAlgCl l),
    sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
      GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙
        J ⋙ (sections l X).mapDerivedCategory ≅
      ObjectProperty.ι (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X) ⋙
        pbcDerivedExtend.{u} ((coefficient E).integralMap l X)

/-- The completion-map transition equation for the given functor data.
Source: Bhatt--Scholze, Proposition 6.8.14, parent proof step 5
(blueprint: def-sf-locally-finite-adic-normalized-functor). -/
def FunctorData.commonField (R : FunctorData l X) : Prop :=
  letI := R.commutative
  letI := R.sectionsAdditive
  letI := R.sectionsLimits
  letI := R.sectionsColimits
  ∀ (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X),
    HEq
      ((sections l X).mapDerivedCategory.map
          (R.J.map ((StageSystem.isoToStage
            (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X)
            ⟨E, (sfRationalConstructibleLocalization l
              (Coefficient.{u} l (PadicAlgCl l) E) X).obj K⟩ h).hom)))
      ((R.integral E).hom.app K ≫
        (pbcReductionNormalization
          (completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L)
            (coefficientInclusion l (PadicAlgCl l) E L h) X)
          ((R.coefficient L).integralMap l X) ((R.coefficient E).integralMap l X)
          (R.coefficient_scalar E L h) K.obj).inv ≫
        (pbcDerivedExtend ((R.coefficient L).integralMap l X)).map
          ((completedTensorComparison l X (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L)
            (coefficientInclusion l (PadicAlgCl l) E L h)).app K.obj) ≫
        (R.integral L).inv.app
          ((GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) X
            E L h).obj K))

/-- The functor construction with its specified common-field transition equation.
Source: Bhatt--Scholze, Proposition 6.8.14, parent proof steps 2--5
(blueprint: def-sf-locally-finite-adic-normalized-functor). -/
structure NormalizedFunctor extends FunctorData l X where
  common_field : FunctorData.commonField l X toFunctorData

end WeilConjectures.LocallyFiniteAdicRealization
