/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Finite algebras over a henselian local ring with algebraically closed residue field

A finite algebra `B` over a henselian local ring `R` is a finite product of henselian local rings
(Stacks, Tag 04GG, `HenselianLocalRing.finite_over_henselian_exists_algEquiv_pi`). If the
residue field of `R` is algebraically closed, the factors have the same residue field, so they
are strictly henselian (blueprint `lemma-vanishing-restrictions-after-blowing-up--1`: the strict
transform of a curve through the closed point of a strictly local surface is a finite disjoint union
of strictly local curves).

## Main results

- `exists_algEquiv_pi_isStrictlyHenselianLocalRing`: `B ≅ ∏ A_j` with `A_j` strictly henselian
  local rings with residue fields equal to that of `R`.
-/

@[expose] public section

universe u

open IsLocalRing

/-- A finite algebra `B` over a henselian local ring `R` with algebraically closed residue field is
a finite product of strictly henselian local rings `A_j`, local over `R`, with residue fields
equal to that of `R`. -/
theorem exists_algEquiv_pi_isStrictlyHenselianLocalRing (R B : Type u) [CommRing R] [CommRing B]
    [HenselianLocalRing R] [IsAlgClosed (ResidueField R)] [Algebra R B] [Module.Finite R B] :
    ∃ (J : Type u) (_ : Finite J) (A : J → Type u) (_ : ∀ j, CommRing (A j))
      (_ : ∀ j, IsStrictlyHenselianLocalRing (A j)) (_ : ∀ j, Algebra R (A j)),
      (∀ j, Function.Surjective (residue (A j) ∘ algebraMap R (A j))) ∧
        Nonempty (B ≃ₐ[R] ∀ j, A j) := by
  obtain ⟨r, A, rings, algebras, henselian, localMaps, ⟨e⟩, -, hres⟩ :=
    HenselianLocalRing.finite_over_henselian_exists_algEquiv_pi R B
  have hsurj : ∀ i, Function.Surjective (residue (A i) ∘ algebraMap R (A i)) := by
    intro i
    have : Algebra.IsIntegral (ResidueField R) (ResidueField (A i)) := inferInstance
    have h := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ResidueField R)
      (K := ResidueField (A i))).2
    intro a
    obtain ⟨b, rfl⟩ := h a
    obtain ⟨r, rfl⟩ := residue_surjective b
    exact ⟨r, (ResidueField.map_residue _ r).symm⟩
  have hstrict : ∀ i, IsStrictlyHenselianLocalRing (A i) := by
    intro i
    have hbij : Function.Bijective (algebraMap (ResidueField R) (ResidueField (A i))) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    have : IsAlgClosed (ResidueField (A i)) :=
      IsAlgClosed.of_ringEquiv _ _ (RingEquiv.ofBijective _ hbij)
    exact (isStrictlyHenselianLocalRing_iff_henselianLocalRing_and_isSepClosed _).2
      ⟨inferInstance, inferInstance⟩
  exact ⟨ULift (Fin r), inferInstance, fun j ↦ A j.down, fun j ↦ rings j.down,
    fun j ↦ hstrict j.down, fun j ↦ algebras j.down, fun j ↦ hsurj j.down,
    ⟨e.trans (AlgEquiv.piCongrLeft R A Equiv.ulift).symm⟩⟩
