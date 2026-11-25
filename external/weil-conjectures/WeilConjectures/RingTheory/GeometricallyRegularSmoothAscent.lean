/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import WeilConjectures.RingTheory.GRing
import Mathlib.Algebra.Field.Shrink
import WeilConjectures.RingTheory.RegularRingSmoothAscent

/-!
# Geometric regularity ascends along smooth algebra maps

Source: Stacks Project, Algebra, Lemma 07QF
(blueprint: lem-weil-pbc-geometrically-regular-smooth-ascent).
-/

@[expose] public section

universe u v w

namespace Algebra

/-- Smooth maps of algebras over a field preserve Noetherianity and geometric regularity.
Source: Stacks Project, Algebra, Lemma 07QF
(blueprint: lem-weil-pbc-geometrically-regular-smooth-ascent).

Proof:
1. Smoothness gives finite presentation, hence finite type. Since A is Noetherian, B is
   Noetherian by lem-weil-pbc-finite-type-algebra-noetherian (Stacks 00FN).
2. For any finite purely inseparable extension k'/k, geometric regularity of A says that
   k' ⊗[k] A is regular, by theorem-finite-etale-covers-proper-henselian--2 (Stacks 0381, condition
   (2)).
3. Base change of the smooth map gives a smooth map from k' ⊗[k] A to k' ⊗[k] B, using
   lem-weil-pbc-smooth-ring-map-base-change-composition (Stacks 00T4) and
   lem-weil-pbc-tensor-cancel-base-change. Transport smoothness across the tensor-product
   identification using Algebra.Smooth.of_equiv.
4. Regularity ascends along this smooth map, by lem-weil-pbc-regular-ring-smooth-ascent
   (Stacks 07NF), so k' ⊗[k] B is regular.
5. Together with step 1, this is geometric regularity of B by
theorem-finite-etale-covers-proper-henselian--2.
-/
theorem isGeometricallyRegular_of_smooth
    {k : Type u} {A : Type v} {B : Type w}
    [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (φ : A →ₐ[k] B)
    (hsmooth : letI : Algebra A B := φ.toRingHom.toAlgebra; Algebra.Smooth A B)
    (hnoetherian : IsNoetherianRing A) (hregular : IsGeometricallyRegular k A) :
    IsNoetherianRing B ∧ IsGeometricallyRegular k B := by
  let : Algebra A B := φ.toRingHom.toAlgebra
  let : Smooth A B := hsmooth
  let : IsNoetherianRing A := hnoetherian
  let : IsScalarTower k A B := IsScalarTower.of_algHom φ
  have hB : IsNoetherianRing B := FiniteType.isNoetherianRing A B
  refine ⟨hB, hB, ?_⟩
  intro K _ _ _ _
  -- The definition for A tests extensions in Type (max u v).
  have : Small.{max u v} K := Module.Finite.small k K
  let K₀ := Shrink.{max u v} K
  have : IsPurelyInseparable k K₀ := (Shrink.algEquiv k K).symm.isPurelyInseparable
  have : IsRegularRing (TensorProduct k K₀ A) := hregular.2 K₀
  have : IsRegularRing (TensorProduct k A K₀) :=
    IsRegularRing.of_ringEquiv (TensorProduct.comm k K₀ A).toRingEquiv
  -- Use the right-algebra structure on the base change, then cancel it as a ring.
  let : Algebra (TensorProduct k A K₀) (TensorProduct A B (TensorProduct k A K₀)) :=
    TensorProduct.rightAlgebra
  have : Smooth (TensorProduct k A K₀) (TensorProduct A B (TensorProduct k A K₀)) :=
    Smooth.of_equiv (TensorProduct.commRight A (TensorProduct k A K₀) B)
  have : IsRegularRing (TensorProduct A B (TensorProduct k A K₀)) :=
    isRegularRing_of_smooth (TensorProduct k A K₀) _
  have : IsRegularRing (TensorProduct k B K₀) :=
    IsRegularRing.of_ringEquiv (TensorProduct.cancelBaseChange k A B B K₀).toRingEquiv
  have : IsRegularRing (TensorProduct k K₀ B) :=
    IsRegularRing.of_ringEquiv (TensorProduct.comm k B K₀).toRingEquiv
  exact IsRegularRing.of_ringEquiv
    (TensorProduct.congr (Shrink.algEquiv k K) (AlgEquiv.refl : B ≃ₐ[k] B)).toRingEquiv

end Algebra
