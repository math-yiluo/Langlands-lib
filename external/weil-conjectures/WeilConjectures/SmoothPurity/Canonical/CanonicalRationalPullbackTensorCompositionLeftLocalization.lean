/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints

/-! Localization of the left hand side of rational pullback/tensor composition.
Source: Stacks 07A4 and 0941; normalized localization of the composition square.
(blueprint: lem-pur-pullback-tensor-rational-composition-coherence-left-localization)
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

/-- The left side of rational composition is the localized integral left side.
Source: Stacks 07A4 and 0941; localization of the normalized composition square.
(blueprint: lem-pur-pullback-tensor-rational-composition-coherence-left-localization).
Use the normalization of the rational canonical tensor and compositor, together with
bilinearity of localized tensor, to identify the left composite with the localization
of the integral left composite. Endpoint normalization supplies the displayed HEq.
-/
theorem canonicalRationalPullbackTensorComposition_left_localization {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M N : sfRationalConstructibleCategory l E Y) :
    HEq
      ((canonicalRationalPullbackTensor l E (h ≫ f) M N).hom ≫
        (rationalDerivedTensor l E Z).map (Prod.mkHom
          (pullbackTensorRationalComposition l E f h M).hom
          (pullbackTensorRationalComposition l E f h N).hom))
      ((sfRationalConstructibleLocalization l E Z).map
        ((canonicalIntegralPullbackTensor l E (h ≫ f) M.obj N.obj).hom ≫
          (constructibleIntegralTensor l E Z).map (Prod.mkHom
            ((pullbackTensorIntegralComposition l E f h).hom.app M.obj)
            ((pullbackTensorIntegralComposition l E f h).hom.app N.obj)))) := by
  let Q := sfRationalConstructibleLocalization l E Z
  let T := rationalDerivedTensor l E Z
  let I := constructibleIntegralTensor l E Z
  have hF (K : sfRationalConstructibleCategory l E Y) :
      (rationalDerivedPullback l E (h ≫ f)).obj
          ((rationalDerivedTensor l E Y).obj (M, N)) =
        Q.obj ((constructibleIntegralPullback l E (h ≫ f)).obj
          ((constructibleIntegralTensor l E Y).obj (M.obj, N.obj))) := by
    dsimp only [rationalDerivedPullback, rationalDerivedTensor, Q]
    rw [(rationalDerivedPullback_existsUnique l E (h ≫ f)).exists.choose_spec.2.1,
      (rationalDerivedTensor_existsUnique l E Y).exists.choose_spec.1]
    rfl
  have hFM : (rationalDerivedPullback l E (h ≫ f)).obj M =
      Q.obj ((constructibleIntegralPullback l E (h ≫ f)).obj M.obj) := by
    dsimp only [rationalDerivedPullback, Q]
    rw [(rationalDerivedPullback_existsUnique l E (h ≫ f)).exists.choose_spec.2.1 M]
    rfl
  have hFN : (rationalDerivedPullback l E (h ≫ f)).obj N =
      Q.obj ((constructibleIntegralPullback l E (h ≫ f)).obj N.obj) := by
    dsimp only [rationalDerivedPullback, Q]
    rw [(rationalDerivedPullback_existsUnique l E (h ≫ f)).exists.choose_spec.2.1 N]
    rfl
  have hCM : (rationalDerivedPullback l E h).obj
        ((rationalDerivedPullback l E f).obj M) =
      Q.obj ((constructibleIntegralPullback l E h).obj
        ((constructibleIntegralPullback l E f).obj M.obj)) := by
    dsimp only [rationalDerivedPullback, Q]
    rw [(rationalDerivedPullback_existsUnique l E h).exists.choose_spec.2.1,
      (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1]
    rfl
  have hCN : (rationalDerivedPullback l E h).obj
        ((rationalDerivedPullback l E f).obj N) =
      Q.obj ((constructibleIntegralPullback l E h).obj
        ((constructibleIntegralPullback l E f).obj N.obj)) := by
    dsimp only [rationalDerivedPullback, Q]
    rw [(rationalDerivedPullback_existsUnique l E h).exists.choose_spec.2.1,
      (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1]
    rfl
  have hT (A B : sfRationalConstructibleCategory l E Z) :
      T.obj (A, B) = Q.obj (I.obj (A.obj, B.obj)) := by
    dsimp only [rationalDerivedTensor, T, I, Q]
    rw [(rationalDerivedTensor_existsUnique l E Z).exists.choose_spec.1]
    rfl
  have hbilmap {A B C D : sfRationalConstructibleCategory l E Z}
      {A' B' C' D' : sfIntegralConstructibleCategory l E Z}
      (hA : A = Q.obj A') (hB : B = Q.obj B')
      (hC : C = Q.obj C') (hD : D = Q.obj D')
      (a : A ⟶ B) (b : C ⟶ D) (a' : A' ⟶ B') (b' : C' ⟶ D')
      (ha : HEq a (Q.map a')) (hb : HEq b (Q.map b')) :
      HEq (T.map (Prod.mkHom a b))
        (Q.map (I.map (Prod.mkHom a' b'))) := by
    subst A B C D
    have ha' := eq_of_heq ha
    have hb' := eq_of_heq hb
    subst a b
    obtain ⟨bil, hbil, hbil'⟩ :=
      (rationalDerivedTensor_existsUnique l E Z).exists.choose_spec.2
        (Q.obj A') (Q.obj B') (Q.obj C') (Q.obj D')
    change HEq ((rationalDerivedTensor_existsUnique l E Z).exists.choose.map
      (Prod.mkHom (Q.map a') (Q.map b'))) _
    rw [hbil]
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      simpa only [one_mul, Q, sfRationalConstructibleLocalization,
        ScalarLocalization.localization] using hbil' a' b' 1 1
  have hc :=
    (canonicalRationalPullbackTensor_existsUnique l E (h ≫ f) M N).exists.choose_spec
  have hm :=
    (pullbackTensorRationalComposition_existsUnique l E f h M).exists.choose_spec
  have hn :=
    (pullbackTensorRationalComposition_existsUnique l E f h N).exists.choose_spec
  have hb := hbilmap hFM (hCM) hFN hCN
      (pullbackTensorRationalComposition l E f h M).hom
      (pullbackTensorRationalComposition l E f h N).hom
      ((pullbackTensorIntegralComposition l E f h).hom.app M.obj)
      ((pullbackTensorIntegralComposition l E f h).hom.app N.obj) hm hn
  have hcomp := heq_comp (hF M) (by rw [hT, hFM, hFN]; rfl)
      (by rw [hCM, hCN, hT]; rfl) hc hb
  exact hcomp.trans (heq_of_eq (Q.map_comp _ _).symm)

end WeilConjectures
