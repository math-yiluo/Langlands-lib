/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore

/-! The normalized finite component of the coherent tensor tower. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.all false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients

namespace WeilConjectures

attribute [local irreducible] Scheme.residueField
  HasDerivedCategory.standard CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory

open CategoryTheory.Limits CategoryTheory.Functor Opposite

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The explicit finite component used by the normalized coherent tensor tower.
Source: Stacks 0941 and 07A4 (blueprint: def-pur-completed-pullback-tower-realizations).
-/
def pullbackTensorTensorTowerLevel (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    (pullbackTensorRestrictedTower l E W
      ((coefficientTotalTensor.{u, u + 1, u}
        (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj
        ((((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P),
          (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj Q))) ).obj
            (op n) ≅
      ((integralOperationsTensorTowerFunctor l E W).obj (P,Q)).obj (op n) :=
  pullbackTensorRestrictedLevel l E W _ n ≪≫
  ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).mapIso
    (coefficientEvaluationTensorIso l E W n _ _) ≪≫
  ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).mapIso
    ((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n)).mapIso
        (Iso.prod ((pullbackTensorReductionEvaluationComplex l E W n).app P).symm
          ((pullbackTensorReductionEvaluationComplex l E W n).app Q).symm))

end WeilConjectures
