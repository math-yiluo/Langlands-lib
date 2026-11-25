/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperations
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.IntegralSystemRealization.Pull.IntegralPullEvaluationCochainSquareComponent

/-! # The cochain pullback evaluation transition square

Source: Zheng Construction 4.1 and Lemma 4.10; Stacks Tags 03D2 and 0941.
-/

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

/-- The actual comparison of exact cochain functors, before localization.
Source: Stacks 03D2 and 0941
(blueprint: lem-sf-integral-pull-evaluation-cochain-square). -/
def integralPullEvaluationComplex {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (pullbackTensorInverseEvaluationComplex l E f n).symm ≪≫
    Functor.isoWhiskerLeft
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ))
      (NatIso.mapHomologicalComplex (pullbackTensorLevelIntrinsic l E f n) (.up ℤ))

/-- The pullback transition square already commutes as a square of cochain maps.
Source: Zheng Construction 4.1, p. 21; the sectionwise calculation preceding
Lemma 4.10, p. 23; Stacks 03D2 and 0941
(blueprint: lem-sf-integral-pull-evaluation-cochain-square).

Proof: first work in the abelian categories of modules on the sequence sites.
The inverse-image/evaluation comparison is the inverse mate of the identity
comparison for direct image and evaluation. The level intrinsic comparison
preserves the ordinary adjunction unit. Restriction of scalars and direct image
commute by the identity on sections. The horizontal transition of a system is
its restriction map along (n,U) to (n+1,U). Naturality of the system adjunction
unit in this horizontal arrow and mate pasting identify the two composites:
both pull back a section and then apply the same coefficient quotient. Check
this on the generating unit sections; the inverse-image adjunction and
sheafification determine the resulting module maps. Apply the cochain functor:
the same equality holds in every degree and respects the differentials.
The cochain reordering maps in integralPullEvaluationComplex are precisely
those induced from the ordinary comparison. No derived direct image,
K-injective representative, flatness or normalization of the input is used. -/
theorem integralPullEvaluation_cochainSquare {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (r₀ : normalizedDVRModuleRes l E X (Nat.le_succ n) ⋙
        proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 2)) ≅
      proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        normalizedDVRModuleRes l E Y (Nat.le_succ n))
    (hr₀ : HEq r₀ (proEtaleCoefficientDirectImageComparison f
      (Padic.coefficientExtensionTransition l E (n + 1))).symm)
    (P : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
    (NatTrans.mapHomologicalComplex
        (coefficientSequenceTransition l E X (Nat.le_succ n)) (.up ℤ)).app
        (((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj P) ≫
      ((normalizedDVRModuleRes l E X (Nat.le_succ n)).mapHomologicalComplex (.up ℤ)).map
        ((integralPullEvaluationComplex l E f n).hom.app P) =
    (integralPullEvaluationComplex l E f (n + 1)).hom.app P ≫
      ((sfIntrinsicPullback (finiteCoefficientRing l E (n + 2)) f).mapHomologicalComplex
        (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex
          (coefficientSequenceTransition l E Y (Nat.le_succ n)) (.up ℤ)).app P) ≫
      (NatTrans.mapHomologicalComplex
        ((mateEquiv
            (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1)))
            (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 2)))).symm
          (TwoSquare.mk _ _ _ _ r₀.inv)) (.up ℤ)).app
        (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj P) := by
  apply HomologicalComplex.hom_ext
  intro i
  have h := integralPullEvaluation_cochainSquare_component l E f n r₀ hr₀ P i
  -- Normalize hidden successor indices before comparing the evaluation functor applications.
  dsimp only [Nat.succ_eq_add_one, integralPullEvaluationComplex, ordinaryPullEvaluationComplex,
    HomologicalComplex.comp_f] at h ⊢
  exact h

end WeilConjectures.IntegralSystemRealization
