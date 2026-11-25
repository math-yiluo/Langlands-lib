/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import WeilConjectures.RingTheory.RegularRingFaithfullyFlatDescent
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Field.Shrink

/-!
# Geometric regularity descends along faithfully flat algebra maps

Source: Stacks Project, Algebra, Lemma Tag 07NH
(blueprint: lem-weil-pbc-geometrically-regular-descent).
-/

@[expose] public section

universe u v w

namespace Algebra

/-- Geometric regularity descends along a faithfully flat map of algebras over a field: the
`k`-algebra map `A → B` is `algebraMap A B`, compatible with `k` by `IsScalarTower k A B`.
Source: Stacks Project, Algebra, Lemma Tag 07NH
(blueprint: lem-weil-pbc-geometrically-regular-descent).

Proof: assume `B` is geometrically regular and fix a finite purely inseparable extension
`k'/k`, as in `def-weil-pbc-finite-purely-inseparable-extension`. The map from
`A ⊗[k] k'` to `B ⊗[k] k'` is faithfully flat by the faithfully-flat base-change lemma.
Geometric regularity of `B` makes `B ⊗[k] k'` regular by
`theorem-finite-etale-covers-proper-henselian--2` and `def-weil-regular-scheme`. Regularity descends
along this faithfully flat map by `lem-weil-pbc-regular-ring-faithfully-flat-descent`, so
`A ⊗[k] k'` is regular. Since `k'/k` was arbitrary,
`theorem-finite-etale-covers-proper-henselian--2` gives geometric regularity of `A`. -/
theorem isGeometricallyRegular_of_faithfullyFlat
    (k : Type u) (A : Type v) (B : Type w) [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    [Module.FaithfullyFlat A B] (hB : IsGeometricallyRegular k B) :
    IsGeometricallyRegular k A := by
  classical
  have : IsNoetherianRing B := hB.1
  refine ⟨?_, ?_⟩
  · exact Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
      (isNoetherian_of_linearEquiv (Algebra.TensorProduct.rid A B B).symm.toLinearEquiv)
  · intro K _ _ _ _
    have : Small.{max u w} K := Module.Finite.small k K
    have : IsPurelyInseparable k (Shrink.{max u w} K) :=
      (Shrink.algEquiv k K).symm.isPurelyInseparable
    have : IsRegularRing (TensorProduct k (Shrink.{max u w} K) B) :=
      hB.2 (Shrink.{max u w} K)
    have : IsRegularRing (TensorProduct k K B) :=
      IsRegularRing.of_ringEquiv
        (Algebra.TensorProduct.congr (Shrink.algEquiv k K)
          (AlgEquiv.refl : B ≃ₐ[k] B)).toRingEquiv
    have : IsRegularRing (TensorProduct k B K) :=
      IsRegularRing.of_ringEquiv (Algebra.TensorProduct.comm k K B).toRingEquiv
    have : IsRegularRing (TensorProduct A B (TensorProduct k A K)) :=
      IsRegularRing.of_ringEquiv
        (Algebra.TensorProduct.cancelBaseChange k A A B K).symm.toRingEquiv
    have : IsRegularRing (TensorProduct A (TensorProduct k A K) B) :=
      IsRegularRing.of_ringEquiv
        (Algebra.TensorProduct.comm A B (TensorProduct k A K)).toRingEquiv
    have : IsRegularRing (TensorProduct k A K) :=
      IsRegularRing.of_faithfullyFlat (TensorProduct k A K)
        (TensorProduct A (TensorProduct k A K) B)
    exact IsRegularRing.of_ringEquiv (Algebra.TensorProduct.comm k A K).toRingEquiv

end Algebra
