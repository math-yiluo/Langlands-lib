/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorPullModel
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.SixFunctors.Constructible.ConstructibleTensorCompletion

/-! # Normalized comparison of tensor and quotient completion

Source: Bhatt--Scholze, Definition 3.4.10, Lemma 6.5.5; Stacks 099N
(blueprint: def-sf-tensor-completion-comparison).
The comparison retains the two actual coordinates of the quotient Roos augmentation.

## Main definitions

- `Tensor`: the normalized completion comparison for the existing tensor.
- `Tensor.chi`: its quotient-augmentation morphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.PurCompactSupport
namespace WeilConjectures.OpenFactorCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The first and shifted coordinates of the actual quotient-unit chain map.
Source: Bhatt--Scholze 3.4.10, 6.5.5
(blueprint: def-sf-tensor-completion-comparison). -/
def IsTensorChain (W : Scheme.{u})
    (chain : constructibleTensorTotal l E W ⟶
      integralOperationsTensorComplexFunctor.{u, u} l E W) : Prop :=
  (∀ (P Q : Cx l E W) (p q : ℤ) (n : ℕ) (V : W.ProEtᵒᵖ)
      (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
    (((chain.app (P, Q) ≫ CochainComplex.mappingCocone.fst
      (constructibleTensorBoundary l E W P Q) ≫
      Pi.π (fun k ↦ (integralOperationsTensorLevel.{u, u} l E W k).obj (P, Q)) n).f
        (p + q)).val.app V) (constructibleTensorTotalSection l E W P Q p q V x y) =
      integralOperationsTotalTensorSection.{u, u} l E W n P Q p q V
        (unrestrictedIntegralTensorSection.{u, u} l E W n (P.X p) V 1 x)
        (unrestrictedIntegralTensorSection.{u, u} l E W n (Q.X q) V 1 y)) ∧
  (∀ (P Q : Cx l E W) (i j : ℤ) (h : i + -1 = j),
    (chain.app (P, Q)).f i ≫ (CochainComplex.mappingCocone.snd
      (constructibleTensorBoundary l E W P Q)).v i j h = 0)

/-- The comparison is the localization of that same normalized chain map.
Source: Bhatt--Scholze 3.4.10, 6.5.5
(blueprint: def-sf-tensor-completion-comparison). -/
def IsTensorCompletion (W : Scheme.{u})
    (ordinary : ProEtaleTensorModel W ((completed l E).ring W))
    (good : ∀ P : Cx l E W,
      proEtaleFlatRepresentatives W ((completed l E).ring W) P →
        integralOperationsGoodComplex.{u, u} l E W P)
    (comparison : ordinary.tensor ⋙ C l E W ≅ integralCompletedTensor.{u, u} l E W)
    (chain : constructibleTensorTotal l E W ⟶
      integralOperationsTensorComplexFunctor.{u, u} l E W) : Prop :=
  ∀ (P Q : Cx l E W)
      (hP : proEtaleFlatRepresentatives W ((completed l E).ring W) P)
      (hQ : proEtaleFlatRepresentatives W ((completed l E).ring W) Q),
    ordinary.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) ≫
        (eta l E W).app (ordinary.tensor.obj (DerivedCategory.Q.obj P,
          DerivedCategory.Q.obj Q)) ≫ comparison.hom.app
            (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (integralCompletedTensorComparison.{u, u} l E W).hom.app (⟨P, good P hP⟩, ⟨Q, good Q hQ⟩) =
      DerivedCategory.Q.map (chain.app (P, Q))

set_option genSizeOf false in
set_option genInjectivity false in
/-- The tensor comparison retains both coordinates of the quotient Roos augmentation.
Source: Bhatt--Scholze 3.4.10 and 6.5.5
(blueprint: def-sf-tensor-completion-comparison). -/
structure Tensor (W : Scheme.{u}) where
  ordinary : ProEtaleTensorModel W ((completed l E).ring W)
  good : ∀ P : Cx l E W,
    proEtaleFlatRepresentatives W ((completed l E).ring W) P →
      integralOperationsGoodComplex.{u, u} l E W P
  comparison : ordinary.tensor ⋙ C l E W ≅ integralCompletedTensor.{u, u} l E W
  chain : constructibleTensorTotal l E W ⟶ integralOperationsTensorComplexFunctor.{u, u} l E W
  canonical : IsTensorChain l E W chain ∧ IsTensorCompletion l E W ordinary good comparison chain

/-- The actual comparison chi, obtained from the quotient unit and the normalized tensor
identification. Source: Bhatt--Scholze 6.5.5
(blueprint: def-sf-tensor-completion-comparison). -/
def Tensor.chi {W : Scheme.{u}} (t : Tensor l E W) :
    t.ordinary.tensor ⟶ integralCompletedTensor.{u, u} l E W :=
  Functor.whiskerLeft t.ordinary.tensor (eta l E W) ≫ t.comparison.hom

end WeilConjectures.OpenFactorCoherence
