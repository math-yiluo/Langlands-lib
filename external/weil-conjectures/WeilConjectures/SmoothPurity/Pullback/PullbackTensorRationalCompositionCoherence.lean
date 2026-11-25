/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import WeilConjectures.SmoothPurity.Pullback.PullbackTensorIntegralCompositionCoherence
import WeilConjectures.SmoothPurity.Canonical.CanonicalRationalPullbackTensorCompositionRightLocalization
import WeilConjectures.SmoothPurity.Canonical.CanonicalRationalPullbackTensorCompositionLeftLocalization

/-! Rational coefficient component of pullback/tensor composition coherence.

Source: Stacks 07A4 and 0941; this is the rational part of
`lem-pur-pullback-tensor-composition-coherence`.
(blueprint: lem-pur-pullback-tensor-composition-coherence)

Localize the normalized integral quotient-tower composition equation. The
object and morphism normalization specifications identify every localized
comparison and compositor with its prescribed rational construction. Bilinearity
of localization identifies the tensor of the two compositor components.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Rational component of higher pullback/tensor composition coherence.
Source: Stacks 07A4 and 0941; localization of the integral composition square.
(blueprint: lem-pur-pullback-tensor-composition-coherence). -/
theorem pullbackTensorRationalCompositionCoherence {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)] :
    ∀ M N : sfRationalConstructibleCategory l E Y,
      canonicalRationalPullbackTensor_composition l E f h M N := by
  intro M N
  have hL := canonicalRationalPullbackTensorComposition_left_localization l E f h M N
  have hR := canonicalRationalPullbackTensorComposition_right_localization l E f h M N
  have hI := pullbackTensorIntegralCompositionCoherence l E f h M.obj N.obj
  have hmapI :
      (sfRationalConstructibleLocalization l E Z).map
          ((canonicalIntegralPullbackTensor l E (h ≫ f) M.obj N.obj).hom ≫
            (constructibleIntegralTensor l E Z).map (Prod.mkHom
              ((pullbackTensorIntegralComposition l E f h).hom.app M.obj)
              ((pullbackTensorIntegralComposition l E f h).hom.app N.obj))) =
      (sfRationalConstructibleLocalization l E Z).map
        ((pullbackTensorIntegralComposition l E f h).hom.app
            ((constructibleIntegralTensor l E Y).obj (M.obj,N.obj)) ≫
          (constructibleIntegralPullback l E h).map
            (canonicalIntegralPullbackTensor l E f M.obj N.obj).hom ≫
          (canonicalIntegralPullbackTensor l E h
            ((constructibleIntegralPullback l E f).obj M.obj)
            ((constructibleIntegralPullback l E f).obj N.obj)).hom) := by
    exact congrArg (sfRationalConstructibleLocalization l E Z).map hI
  exact eq_of_heq (hL.trans ((heq_of_eq hmapI).trans hR.symm))

end WeilConjectures
