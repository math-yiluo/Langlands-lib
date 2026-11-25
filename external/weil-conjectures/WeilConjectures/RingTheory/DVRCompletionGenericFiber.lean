/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import WeilConjectures.RingTheory.CompletionOfDVR
import WeilConjectures.Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Geometric regularity of the generic fibre of a DVR completion

Source: Stacks Project, More on Algebra, Proposition Tag 07PX
(blueprint: lem-weil-pbc-dvr-completion-generic-fiber).
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace AdicCompletion

/-- The generic fibre of a characteristic-zero DVR completion is geometrically regular.

Proof: Choose a uniformizer π of A. Its image generates the maximal ideal of the
completion by the local-completion theorem. The completion is a DVR by Tag 0AP1, so
this image is nonzero and irreducible. Every nonzero element of the completion is a
unit times a power of this image. Base-changing to the fraction field inverts π and
therefore all nonzero elements of the completion; the generic fibre is its fraction
field. The residue field at the zero prime is the fraction field of A, hence has
characteristic zero. Every purely inseparable extension of a characteristic-zero
field is trivial. Tensoring the generic fibre with such an extension therefore gives
a field again. Fields are Noetherian and regular, proving both conjuncts.

Source: Stacks Project, More on Algebra, Proposition Tag 07PX
(blueprint: lem-weil-pbc-dvr-completion-generic-fiber). -/
theorem isGeometricallyRegular_genericFiber_of_isDiscreteValuationRing_of_charZero
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] :
    Algebra.IsGeometricallyRegular (⊥ : Ideal A).ResidueField
      ((⊥ : Ideal A).Fiber (AdicCompletion (IsLocalRing.maximalIdeal A) A)) := by
  classical
  let B := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let k := (⊥ : Ideal A).ResidueField
  obtain ⟨hB, hDVR⟩ := AdicCompletion.isDiscreteValuationRing A
  have := hB
  have := hDVR
  have hm : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B := AdicCompletion.maximalIdeal_eq_map.symm
  have : IsFractionRing B (B ⊗[A] k) :=
    IsDiscreteValuationRing.isFractionRing_tensorProduct hm k
  let := IsFractionRing.toField B (K := B ⊗[A] k)
  let e := Algebra.TensorProduct.comm A k B
  have hf : IsField (k ⊗[A] B) := e.toRingEquiv.toMulEquiv.isField (Field.toIsField _)
  let := hf.toField
  have : CharZero A := ⟨fun m n h ↦ Nat.cast_injective (R := K) (by
    simpa only [map_natCast] using congrArg (algebraMap A K) h)⟩
  have : CharZero k := IsFractionRing.charZero_of_isFractionRing A
  refine ⟨inferInstance, ?_⟩
  intro k' _ _ _ _
  have hb := IsPurelyInseparable.bijective_algebraMap_of_isSeparable k k'
  let e' := AlgEquiv.ofBijective
    (Algebra.TensorProduct.includeRight : (k ⊗[A] B) →ₐ[k] k' ⊗[k] (k ⊗[A] B))
    (Algebra.TensorProduct.includeRight_bijective hb)
  exact IsRegularRing.of_ringEquiv e'.toRingEquiv

end AdicCompletion
