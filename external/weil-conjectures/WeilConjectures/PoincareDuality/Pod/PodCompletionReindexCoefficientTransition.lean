/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexFamily.PodCompletionReindexCoherence
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
public import WeilConjectures.PoincareDuality.Integral.IntegralPullbackComparisonRealization

/-! # Coherence of the specified ordinary reindexing comparisons

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 03EL, 07A4, 0941
(blueprint: def-pod-completion-reindex-coefficient-transition).
All equations below refer to the displayed family's own reduction, limit and tensor maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

section Coefficients
variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Reduction of the specified scalar completion arrow, then the whole-system counit.
This fixes the scalar comparison before evaluating any finite quotient.
Source: Stacks 06YY, 0941 (blueprint: def-pod-completion-reindex-coefficient-transition). -/
def podScalarReduction (W : Scheme.{u}) (ρ : IntegralComparisonRoosModel l L W)
    (S : IntegralComparisonScalarModel l E L ι W (podReindexCalculus l E W) ρ) :
    integralOrdinaryDerivedScalar l E L ι W ⋙ (podReindexCalculus l L W).reduction ⟶
      (podReindexCalculus l E W).reduction ⋙ integralComparisonDerivedSequenceScalar l E L ι W :=
  whiskerRight (scalarCompletion l E L ι W) (podReindexCalculus l L W).reduction ≫
    integralComparisonScalarCounit l E L ι W (podReindexCalculus l E W)
      (podReindexCalculus l L W) ρ S

/-- The scalar/limit comparison is the same scalar completion and coherent counit formula.
Its definition applies to ambient systems, without asserting invertibility there.
Source: Stacks 06YY, 0941 (blueprint: def-pod-completion-reindex-coefficient-transition). -/
def podScalarLimit (W : Scheme.{u}) (ρ : IntegralComparisonRoosModel l L W)
    (S : IntegralComparisonScalarModel l E L ι W (podReindexCalculus l E W) ρ)
    (N : coefficientSequenceDerived l E W) :
    (integralOrdinaryDerivedScalar l E L ι W).obj ((coefficientSequenceLimit l E W).obj N) ⟶
      (coefficientSequenceLimit l L W).obj
        ((integralComparisonDerivedSequenceScalar l E L ι W).obj N) :=
  (scalarCompletion l E L ι W).app ((coefficientSequenceLimit l E W).obj N) ≫
    S.realization.hom.app ((coefficientSequenceLimit l E W).obj N) ≫
    (coefficientSequenceLimit l L W).map
      ((integralComparisonDerivedSequenceScalar l E L ι W).map
        ((podReindexCalculus l E W).adjunction.counit.app N))

/-- Canonical scalar/pullback transports for the very selected D and T at E and L.
The ordinary map is fixed by the local balanced-tensor formula in Laws.
Source: blueprint Step 5; Stacks 03EL, 06YY, 0941
(blueprint: def-pod-completion-reindex-coefficient-transition). -/
structure PodReindexCoefficientTransition {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (D' : PodCompletionReindex l L g) where
  /-- Scalar/reindexing on module sheaves, before localization. -/
  ordinary : isoReductionIntegralInverse l E g ⋙ integralOrdinaryScalar l E L ι X ≅
    integralOrdinaryScalar l E L ι Y ⋙ isoReductionIntegralInverse l L g
  /-- Quotient/Roos-normalized scalar realization at the source. -/
  source : IntegralComparisonScalarModel l E L ι Y (podReindexCalculus l E Y) D'.sourceRoos
  /-- The same normalized scalar realization at the target. -/
  target : IntegralComparisonScalarModel l E L ι X (podReindexCalculus l E X) D'.targetRoos
  /-- Finite free scalar extension preserves the specified complete constructible inputs. -/
  sourceConstructible : ∀ M : sfIntegralConstructibleCategory l E Y,
    sfIntegralConstructible l L Y ((integralOrdinaryDerivedScalar l E L ι Y).obj M.obj)

namespace PodReindexCoefficientTransition
variable {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  (D : PodCompletionReindex l E g) (D' : PodCompletionReindex l L g)
  (T : PodCompletedTensorReindex l E g D) (T' : PodCompletedTensorReindex l L g D')
  (S : PodReindexCoefficientTransition l E L ι g D D')

/-- The derived comparison is the localization of that same ordinary map.
Source: Stacks 015F (blueprint: def-pod-completion-reindex-coefficient-transition). -/
def derived : podOrdinaryReindex l E g ⋙ integralOrdinaryDerivedScalar l E L ι X ≅
    integralOrdinaryDerivedScalar l E L ι Y ⋙ podOrdinaryReindex l L g :=
  Functor.mapDerivedCategoryCompIso (isoReductionIntegralInverse l E g)
    (integralOrdinaryScalar l E L ι X) ≪≫
    Functor.mapDerivedCategoryNatIso S.ordinary ≪≫
    (Functor.mapDerivedCategoryCompIso (integralOrdinaryScalar l E L ι Y)
      (isoReductionIntegralInverse l L g)).symm

/-- Coefficient transition is fixed on pure tensors and commutes with the item's
own reduction, limit and tensor identifications. Identity embeddings are included.
Source: blueprint Step 5; Stacks 03EL, 06YY, 0941
(blueprint: def-pod-completion-reindex-coefficient-transition). -/
def Laws : Prop :=
  (∀ (M : scalarReductionSource l E Y) (U : X.ProEt)
    (x : M.val.obj (op ((proEtaleIsoPostcompose g).obj U)))
    (a : (completedIntegralCoefficientSheafUnrestricted l L Y).obj.obj
      (op ((proEtaleIsoPostcompose g).obj U))),
    (S.ordinary.hom.app M).val.app (op U)
      (integralOrdinaryTensorSection l E L ι X ((isoReductionIntegralInverse l E g).obj M)
        (op U) ((isoReductionCompletedMap l L g).hom.hom.app (op U) a) x) =
      integralOrdinaryTensorSection l E L ι Y M
        (op ((proEtaleIsoPostcompose g).obj U)) a x) ∧
  (∀ K : DerivedCategory (scalarReductionSource l E Y),
    (podScalarReduction l E L ι X D'.targetRoos S.target).app
        ((podOrdinaryReindex l E g).obj K) ≫
      (integralComparisonDerivedSequenceScalar l E L ι X).map (D.reduction.inv.app K) ≫
      (integralComparisonSystemScalarPullback l E L ι g).hom.app
        ((podReindexCalculus l E Y).reduction.obj K) =
    (podReindexCalculus l L X).reduction.map ((S.derived l E L ι g D D').hom.app K) ≫
      D'.reduction.inv.app ((integralOrdinaryDerivedScalar l E L ι Y).obj K) ≫
      (integralComparisonDerivedSequencePullback l L g).map
        ((podScalarReduction l E L ι Y D'.sourceRoos S.source).app K)) ∧
  (∀ N : coefficientSequenceDerived l E Y,
    (integralOrdinaryDerivedScalar l E L ι X).map (D.limit.hom.app N) ≫
      podScalarLimit l E L ι X D'.targetRoos S.target
        ((integralComparisonDerivedSequencePullback l E g).obj N) ≫
      (coefficientSequenceLimit l L X).map
        ((integralComparisonSystemScalarPullback l E L ι g).hom.app N) =
    (S.derived l E L ι g D D').hom.app ((coefficientSequenceLimit l E Y).obj N) ≫
      (podOrdinaryReindex l L g).map
        (podScalarLimit l E L ι Y D'.sourceRoos S.source N) ≫
      D'.limit.hom.app ((integralComparisonDerivedSequenceScalar l E L ι Y).obj N)) ∧
  (∀ M N : sfIntegralConstructibleCategory l E Y,
    (integralOrdinaryDerivedScalar l E L ι X).map (T.tensor M N).hom ≫
      (scalarTensorOrdinary l E L ι X).hom.app
        ((podOrdinaryReindex l E g).obj M.obj, (podOrdinaryReindex l E g).obj N.obj) ≫
      (integralCompletedTensor l L X).map
        (Prod.mkHom ((S.derived l E L ι g D D').hom.app M.obj)
          ((S.derived l E L ι g D D').hom.app N.obj)) =
    (S.derived l E L ι g D D').hom.app
        ((integralCompletedTensor l E Y).obj (M.obj,N.obj)) ≫
      (podOrdinaryReindex l L g).map ((scalarTensorOrdinary l E L ι Y).hom.app (M.obj,N.obj)) ≫
      (T'.tensor ⟨_, S.sourceConstructible M⟩ ⟨_, S.sourceConstructible N⟩).hom)

end PodReindexCoefficientTransition
end Coefficients

end WeilConjectures
