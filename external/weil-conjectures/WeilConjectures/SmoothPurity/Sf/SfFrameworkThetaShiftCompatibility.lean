/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.PoincareDuality.Integral.IntegralPullbackComparisonRealization
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.FourierTransform.IntegralCompletedComparison.IntegralPullbackShiftCoordinates
public import WeilConjectures.SmoothPurity.Completed.CompletedScalarShiftCoordinates

import WeilConjectures.SmoothPurity.Integral.Comparison.IntegralComparisonPullbackRealizationShifts
import WeilConjectures.SmoothPurity.Integral.Comparison.IntegralComparisonScalarRealizationShifts
import WeilConjectures.SmoothPurity.Integral.Comparison.IntegralComparisonSequenceScalarPullbackShifts

set_option linter.privateModule false

/-!
# The normalized completed pullback scalar comparison commutes with shifts

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sf-localization/
prop-sf-open-closed-triangle-all-stages.proof.md, Weil-structures and rational-stage
paragraphs; Stacks Tags 011G, 014E, 0941 and 099N(5)
(blueprint: lem-sf-framework-theta-shift-compatibility).

The shift data below are fixed by the existing signed cochain coordinate and
representative-descent predicates. Theta is lambda followed by mu inverse for
the whole-system counit realization, rather than an arbitrary isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe d u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{u}} (f : X ⟶ Y)

variable [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

attribute [local irreducible] integralComparisonSequenceScalarModel
  integralComparisonPullbackCounit integralComparisonScalarCounit
  integralDerivedPullback integralComparisonDerivedSequencePullback
  integralComparisonDerivedSequenceScalar coefficientSequenceLimit

private theorem reduced_realization_commShift
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
    (F : A ⥤ B) (H : A ⥤ C) (T : C ⥤ D) (L : D ⥤ B) (R : B ⥤ D)
    [F.CommShift ℤ] [H.CommShift ℤ] [T.CommShift ℤ]
    [L.CommShift ℤ] [R.CommShift ℤ]
    (e : F ⟶ H ⋙ T ⋙ L) (c : L ⋙ R ⟶ 𝟭 D)
    [NatTrans.CommShift e ℤ] [NatTrans.CommShift c ℤ] :
    NatTrans.CommShift (show F ⋙ R ⟶ H ⋙ T from
      Functor.whiskerRight e R ≫ Functor.whiskerLeft (H ⋙ T) c) ℤ := by
  let t := Functor.whiskerRight e R ≫ (Functor.associator H (T ⋙ L) R).hom ≫
    Functor.whiskerLeft H ((Functor.associator T L R).hom ≫
      Functor.whiskerLeft T c ≫ T.rightUnitor.hom)
  have ht : NatTrans.CommShift t ℤ := by dsimp [t]; infer_instance
  have he : t = (show F ⋙ R ⟶ H ⋙ T from
      Functor.whiskerRight e R ≫ Functor.whiskerLeft (H ⋙ T) c) := by
    ext X
    simp [t]
  exact he ▸ ht

end WeilConjectures
