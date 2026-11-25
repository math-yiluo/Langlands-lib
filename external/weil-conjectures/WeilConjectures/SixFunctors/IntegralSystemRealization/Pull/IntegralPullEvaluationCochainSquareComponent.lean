/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperations
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.IntegralSystemRealization.Pull.IntegralPullEvaluationCochainSquareComponentCore

/-! Degreewise ordinary pullback evaluation transition square. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] pullbackTensorInverseEvaluationComplex pullbackTensorLevelIntrinsic
attribute [local implicit_reducible]
  coefficientSequenceEvaluation pullbackTensorSequenceInverse

/-- The ordinary cochain comparison used by the degreewise square.
Source: Zheng Construction 4.1 and Lemma 4.10.
(blueprint: lem-sf-integral-pull-evaluation-cochain-square-component). -/
def ordinaryPullEvaluationComplex {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (pullbackTensorInverseEvaluationComplex l E f n).symm ≪≫
    Functor.isoWhiskerLeft
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ))
      (NatIso.mapHomologicalComplex (pullbackTensorLevelIntrinsic l E f n) (.up ℤ))

/-- The degreewise component of the ordinary cochain pullback evaluation transition square.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks Tags 03D2 and 0941.
(blueprint: lem-sf-integral-pull-evaluation-cochain-square-component).

Proof: this is the fixed ordinary sectionwise calculation at one cochain degree.
The inverse-image/evaluation comparison is the inverse mate of the identity
comparison for direct image and evaluation. The level intrinsic comparison is
characterized by preservation of the ordinary adjunction unit. Restriction of
scalars and direct image are identity on the relevant underlying sections, and
coefficient transitions are restriction along the horizontal arrow
(n,U) → (n+1,U). Naturality of the adjunction unit and the mate correspondence
therefore identify the two composites on every generating section; sheaf
extensionality gives equality of module maps. The same calculation applies to
the displayed mate of r₀.inv because hr₀ identifies r₀ with the canonical
identity-on-sections comparison. The mapHomologicalComplex component at i is
exactly this module equality, with no differential or localization argument.
Zero modules and n = 0 use the same section formula.
-/
theorem integralPullEvaluation_cochainSquare_component {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (r₀ : normalizedDVRModuleRes l E X (Nat.le_succ n) ⋙
        proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 2)) ≅
      proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        normalizedDVRModuleRes l E Y (Nat.le_succ n))
    (hr₀ : HEq r₀ (proEtaleCoefficientDirectImageComparison f
      (Padic.coefficientExtensionTransition l E (n + 1))).symm)
    (P : CochainComplex (coefficientSequenceModules l E Y) ℤ) (i : ℤ) :
    ((NatTrans.mapHomologicalComplex
        (coefficientSequenceTransition l E X (Nat.le_succ n)) (.up ℤ)).app
        (((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj P)).f i ≫
      (((normalizedDVRModuleRes l E X (Nat.le_succ n)).mapHomologicalComplex (.up ℤ)).map
        ((ordinaryPullEvaluationComplex l E f n).hom.app P)).f i =
    (((ordinaryPullEvaluationComplex l E f (n + 1)).hom.app P)).f i ≫
      (((sfIntrinsicPullback (finiteCoefficientRing l E (n + 2)) f).mapHomologicalComplex
        (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex
          (coefficientSequenceTransition l E Y (Nat.le_succ n)) (.up ℤ)).app P)).f i ≫
      ((NatTrans.mapHomologicalComplex
        ((mateEquiv
            (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1)))
            (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 2)))).symm
          (TwoSquare.mk _ _ _ _ r₀.inv)) (.up ℤ)).app
        (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj P)).f i  := by
  simpa only [ordinaryPullEvaluationComplex] using
    (integralPullEvaluation_cochainSquare_component_core_expanded l E f n r₀ hr₀ P i)

end WeilConjectures.IntegralSystemRealization
