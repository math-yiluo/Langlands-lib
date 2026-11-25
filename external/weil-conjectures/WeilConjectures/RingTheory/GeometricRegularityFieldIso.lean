/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Field.Shrink
import Mathlib.RingTheory.Finiteness.Small

/-!
# Geometric regularity under compatible field and ring isomorphisms

Source: Stacks Project, Algebra, Definition 0382.
(blueprint: lem-weil-pbc-geometric-regularity-field-iso).
-/

@[expose] public section

universe u v w z

namespace Algebra

/-- Geometric regularity is invariant under compatible field and ring isomorphisms.
Source: Stacks Project, Algebra, Definition 0382, transport of structure in step 5
of lem-weil-pbc-regular-through-localization.
(blueprint: lem-weil-pbc-geometric-regularity-field-iso).

Proof: Transport Noetherianity along the ring isomorphism. For each finite purely
inseparable extension L of k', give L the k-algebra structure obtained by composing
its structure map with σ. Its dimension over k equals its dimension over k', since
σ is bijective, and pure inseparability is unchanged since the images of the two
base fields in L coincide. The rule l ⊗ a ↦ l ⊗ e(a) is balanced by the compatibility
hypothesis. The inverse rule uses e.symm and σ.symm, and gives an isomorphism
L ⊗[k] A ≃+* L ⊗[k'] B. Regularity is invariant under this ring isomorphism.
If L is in a larger universe than the one tested by IsGeometricallyRegular k A,
first replace it by Shrink L: finiteness over k makes it small in that universe.
Transport back along the canonical field isomorphism Shrink L ≃+* L. This yields
regularity after every finite purely inseparable extension of k', as required. -/
theorem isGeometricallyRegular_of_fieldIso
    {k : Type u} {k' : Type v} {A : Type w} {B : Type z}
    [Field k] [Field k'] [CommRing A] [CommRing B] [Algebra k A] [Algebra k' B]
    (σ : k ≃+* k') (e : A ≃+* B)
    (hcompat : ∀ x : k, ∀ a : A, e (x • a) = σ x • e a)
    (hA : IsGeometricallyRegular k A) : IsGeometricallyRegular k' B := by
  let : Algebra k k' := σ.toRingHom.toAlgebra
  let : Algebra k B := ((algebraMap k' B).comp σ.toRingHom).toAlgebra
  have : IsScalarTower k k' B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let eA : A ≃ₐ[k] B :=
    { e with
      commutes' := fun x ↦ by
        change e (algebraMap k A x) = algebraMap k' B (σ x)
        simpa only [Algebra.smul_def, mul_one, map_one] using hcompat x 1 }
  have : IsNoetherianRing A := hA.1
  refine ⟨isNoetherianRing_of_ringEquiv A e, ?_⟩
  intro L _ _ _ _
  let : Algebra k L := ((algebraMap k' L).comp σ.toRingHom).toAlgebra
  have : IsScalarTower k k' L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Module.Finite k k' :=
    Module.Finite.of_surjective (Algebra.linearMap k k') σ.surjective
  have : Module.Finite k L := Module.Finite.trans k' L
  have : IsPurelyInseparable k k' :=
    ⟨inferInstance, fun x _ ↦ σ.surjective x⟩
  have : IsPurelyInseparable k L := IsPurelyInseparable.trans k k' L
  have : Small.{max u w} L := Module.Finite.small k L
  have : IsPurelyInseparable k (Shrink.{max u w} L) :=
    (Shrink.algEquiv k L).symm.isPurelyInseparable
  have : IsRegularRing (TensorProduct k (Shrink.{max u w} L) A) :=
    hA.2 (Shrink.{max u w} L)
  have : IsRegularRing (TensorProduct k L A) :=
    IsRegularRing.of_ringEquiv
      (Algebra.TensorProduct.congr (Shrink.algEquiv k L)
        (AlgEquiv.refl : A ≃ₐ[k] A)).toRingEquiv
  have : TensorProduct.CompatibleSMul k k' L B := ⟨by
    intro x l b
    obtain ⟨x, rfl⟩ := σ.surjective x
    change (algebraMap k k' x • l) ⊗ₜ[k] b = l ⊗ₜ[k] (algebraMap k k' x • b)
    simp only [algebraMap_smul, TensorProduct.smul_tmul]⟩
  let e₁ := Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[k] L) eA
  let e₂ := Algebra.TensorProduct.equivOfCompatibleSMul k k' k L B
  exact IsRegularRing.of_ringEquiv (e₁.trans e₂.symm).toRingEquiv

end Algebra
