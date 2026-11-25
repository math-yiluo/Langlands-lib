/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexCoefficientTransition
public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels

/-! # Unit generators for quotient comparison functors

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL, 06YY, 0941
(blueprint: def-pod-quotient-transition-generators).
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

namespace PodQuotientTransition

/-- The unit generator of an ordinary whole quotient system.
Source: Stacks 06YY, 0941
(blueprint: def-pod-quotient-transition-generators). -/
def unitSection (W : Scheme.{u}) (M : CompletionUnit.OrdinaryModel l E W)
    (N : scalarReductionSource l E W) (n : ℕ) (U : W.ProEtᵒᵖ)
    (x : N.val.obj U) : (M.tensor.obj N).val.obj (op (n, U.unop)) :=
  integralComparisonSequenceSection l E W (M.tensor.obj N) n U
    (((M.evaluation n).inv.app N).val.app U
      (unrestrictedIntegralTensorSection l E W n N U 1 x))

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Ordinary scalar comparison is fixed on the nested tensor units.
Source: Stacks 06YY, 0941
(blueprint: def-pod-quotient-transition-generators). -/
def ScalarNormalized (W : Scheme.{u})
    (ME : CompletionUnit.OrdinaryModel l E W) (ML : CompletionUnit.OrdinaryModel l L W)
    (α : ME.tensor ⋙ (integralComparisonSequenceScalarModel l E L ι W).E ≅
      integralOrdinaryScalar l E L ι W ⋙ ML.tensor) : Prop :=
  ∀ (N : scalarReductionSource l E W) (n : ℕ) (U : W.ProEtᵒᵖ) (x : N.val.obj U),
    (α.hom.app N).val.app (op (n, U.unop))
        (integralComparisonSequenceTensorSection l E L ι W (ME.tensor.obj N)
          (op (n, U.unop)) 1 (unitSection l E W ME N n U x)) =
      unitSection l L W ML ((integralOrdinaryScalar l E L ι W).obj N) n U
        (integralOrdinaryTensorSection l E L ι W N U 1 x)

/-- Ordinary reindexing comparison is fixed on quotient unit generators.
The comma arrow identifies the base change of g(U) with U.
Source: Stacks 03EL, 06YY, 0941
(blueprint: def-pod-quotient-transition-generators). -/
def ReindexNormalized {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (MY : CompletionUnit.OrdinaryModel l E Y) (MX : CompletionUnit.OrdinaryModel l E X)
    (β : MY.tensor ⋙ integralComparisonSequencePullback l E g ≅
      isoReductionIntegralInverse l E g ⋙ MX.tensor) : Prop :=
  ∀ (N : scalarReductionSource l E Y) (n : ℕ) (U : X.ProEt)
    (x : N.val.obj (op ((proEtaleIsoPostcompose g).obj U))),
    (β.hom.app N).val.app (op (n, U))
        (((integralComparisonSequencePullback l E g).obj (MY.tensor.obj N)).val.map
          (Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U)).op
          (integralComparisonSequenceGenerator l E g (MY.tensor.obj N) n
            ((proEtaleIsoPostcompose g).obj U)
            (unitSection l E Y MY N n (op ((proEtaleIsoPostcompose g).obj U)) x))) =
      unitSection l E X MX ((isoReductionIntegralInverse l E g).obj N) n (op U) x

end PodQuotientTransition
end WeilConjectures
