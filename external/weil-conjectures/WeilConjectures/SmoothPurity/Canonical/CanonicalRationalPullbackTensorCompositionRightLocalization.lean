/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints

/-! Localization of the right hand side of rational pullback/tensor composition.
Source: Stacks 07A4 and 0941; normalized localization of the composition square.
(blueprint: lem-pur-pullback-tensor-rational-composition-coherence-right-localization)
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

/-- The right side of rational composition is the localized integral right side.
Source: Stacks 07A4 and 0941; localization of the normalized composition square.
(blueprint: lem-pur-pullback-tensor-rational-composition-coherence-right-localization).
Apply the localization formula for the composition compositor, the pullback map, and
the canonical tensor comparison, then use functoriality of localization. Endpoint
normalization identifies the resulting morphisms with the displayed types.
-/
theorem canonicalRationalPullbackTensorComposition_right_localization {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M N : sfRationalConstructibleCategory l E Y) :
    HEq
      ((pullbackTensorRationalComposition l E f h
          ((rationalDerivedTensor l E Y).obj (M,N))).hom ≫
        (rationalDerivedPullback l E h).map
          (canonicalRationalPullbackTensor l E f M N).hom ≫
        (canonicalRationalPullbackTensor l E h
          ((rationalDerivedPullback l E f).obj M)
          ((rationalDerivedPullback l E f).obj N)).hom)
      ((sfRationalConstructibleLocalization l E Z).map
        ((pullbackTensorIntegralComposition l E f h).hom.app
            ((constructibleIntegralTensor l E Y).obj (M.obj,N.obj)) ≫
          (constructibleIntegralPullback l E h).map
            (canonicalIntegralPullbackTensor l E f M.obj N.obj).hom ≫
          (canonicalIntegralPullbackTensor l E h
            ((constructibleIntegralPullback l E f).obj M.obj)
            ((constructibleIntegralPullback l E f).obj N.obj)).hom)) := by
  let Q := sfRationalConstructibleLocalization l E Z
  have hF {V W : Scheme.{u}} (g : V ⟶ W)
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)]
      (K : sfRationalConstructibleCategory l E W) :
      (rationalDerivedPullback l E g).obj K =
        (sfRationalConstructibleLocalization l E V).obj
          ((constructibleIntegralPullback l E g).obj K.obj) :=
    (rationalDerivedPullback_existsUnique l E g).exists.choose_spec.2.1 K
  have hT (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
      (A B : sfRationalConstructibleCategory l E W) :
      (rationalDerivedTensor l E W).obj (A,B) =
        (sfRationalConstructibleLocalization l E W).obj
          ((constructibleIntegralTensor l E W).obj (A.obj,B.obj)) :=
    (rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1 (A,B)
  have ht : ((rationalDerivedTensor l E Y).obj (M,N)).obj =
      (constructibleIntegralTensor l E Y).obj (M.obj,N.obj) := by
    rw [hT]
    rfl
  have hf (K : sfRationalConstructibleCategory l E Y) :
      ((rationalDerivedPullback l E f).obj K).obj =
        (constructibleIntegralPullback l E f).obj K.obj := by
    rw [hF]
    rfl
  have hcomp (A B : sfIntegralConstructibleCategory l E Y) (hab : A = B) :
      HEq (Q.map ((pullbackTensorIntegralComposition l E f h).hom.app A))
        (Q.map ((pullbackTensorIntegralComposition l E f h).hom.app B)) := by
    subst B
    rfl
  have hc := (pullbackTensorRationalComposition_existsUnique l E f h
    ((rationalDerivedTensor l E Y).obj (M,N))).exists.choose_spec
  have hc' := hc.trans (hcomp _ _ ht)
  have hmap {A B : sfRationalConstructibleCategory l E X}
      {A' B' : sfIntegralConstructibleCategory l E X}
      (hA : A = (sfRationalConstructibleLocalization l E X).obj A')
      (hB : B = (sfRationalConstructibleLocalization l E X).obj B')
      (a : A ⟶ B) (b : A' ⟶ B')
      (hab : HEq a ((sfRationalConstructibleLocalization l E X).map b)) :
      HEq ((rationalDerivedPullback l E h).map a)
        (Q.map ((constructibleIntegralPullback l E h).map b)) := by
    subst A B
    cases hab
    exact (rationalDerivedPullback_existsUnique l E h).exists.choose_spec.2.2 A' B' b 1
  have hd := (canonicalRationalPullbackTensor_existsUnique l E f M N).exists.choose_spec
  have hd' := hmap (by rw [hF, hT]; rfl) (by rw [hT, hF, hF]; rfl) _ _ hd
  have hcomparison (A B A' B' : sfIntegralConstructibleCategory l E X)
      (ha : A = A') (hb : B = B') :
      HEq (Q.map (canonicalIntegralPullbackTensor l E h A B).hom)
        (Q.map (canonicalIntegralPullbackTensor l E h A' B').hom) := by
    subst A' B'
    rfl
  have he := (canonicalRationalPullbackTensor_existsUnique l E h
    ((rationalDerivedPullback l E f).obj M)
    ((rationalDerivedPullback l E f).obj N)).exists.choose_spec
  have he' := he.trans (hcomparison _ _ _ _ (hf M) (hf N))
  have htail := heq_comp (by rw [hF, hF, hT]; rfl)
    (by rw [hF, hT, hF, hF]; rfl)
    (by rw [hT, hF, hF, hF, hF]; rfl) hd' he'
  have hright := heq_comp (by rw [hF, hT]; rfl)
    (by rw [hF, hF, hT]; rfl)
    (by rw [hT, hF, hF, hF, hF]; rfl) hc' htail
  simpa only [← Functor.map_comp, Q, pullbackTensorRationalComposition,
    canonicalRationalPullbackTensor] using hright

end WeilConjectures
