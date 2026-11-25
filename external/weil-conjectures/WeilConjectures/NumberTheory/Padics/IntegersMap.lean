/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Filtration
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import WeilConjectures.NumberTheory.Padics.Extension
public import WeilConjectures.NumberTheory.Padics.IntegersFinite
public import WeilConjectures.RingTheory.FrobeniusForm

/-!
# The inclusion of rings of integers `𝒪_E ⟶ 𝒪_L`

Let `E ⊆ L` be extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`, and let `PadicAlgCl.integersMap` and
`PadicAlgCl.integersShrinkMap` be the inclusions `𝒪_E ⟶ 𝒪_L` of their rings of integers and of
the universe `u + 1` copies `Shrink 𝒪_E ⟶ Shrink 𝒪_L`.

## Main results

- `PadicAlgCl.integersMap_injective`, `PadicAlgCl.integersShrinkMap_injective`: these inclusions
  are injective.
- `PadicAlgCl.exists_basis_frobeniusForm_integersShrinkMap`: if `E` and `L` are finite over
  `ℚ_ℓ`, then `𝒪_L` is free over `𝒪_E` and has a Frobenius form, so that extension and
  coextension of scalars along `𝒪_E ⟶ 𝒪_L` agree.
- `PadicAlgCl.exists_dvd_pow_of_mem_maximalIdealShrink`: every nonzero element of `𝒪_L` divides
  a power of every element of the maximal ideal of `𝒪_L`.
-/

@[expose] public section

universe w u

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (E L : Type w) [Field E] [Field L]
  [Algebra E (PadicAlgCl l)] [Algebra L (PadicAlgCl l)] [Algebra E L]
  [IsScalarTower E L (PadicAlgCl l)]

lemma integersMap_injective : Function.Injective (integersMap l E L) := fun _ _ h ↦
  Subtype.ext ((algebraMap E L).injective (congrArg Subtype.val h))

section Shrink

variable [Small.{u + 1} E] [Small.{u + 1} L]

lemma integersShrinkMap_injective : Function.Injective (integersShrinkMap.{w, u} l E L) :=
  (shrinkRingEquiv l L).injective.comp
    ((integersMap_injective l E L).comp (shrinkRingEquiv l E).symm.injective)

/-- The inclusion `𝒪_E ⟶ 𝒪_L` carries nonzerodivisors to nonzerodivisors. -/
lemma integersShrinkMap_mem_nonZeroDivisors {x : Shrink.{u + 1} (integers l E)}
    (hx : x ∈ nonZeroDivisors _) : integersShrinkMap l E L x ∈ nonZeroDivisors _ :=
  mem_nonZeroDivisors_of_ne_zero fun h ↦ nonZeroDivisors.ne_zero hx
    (integersShrinkMap_injective l E L (h.trans (map_zero _).symm))

end Shrink

section Finite

variable [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]
  [Algebra ℚ_[l] L] [IsScalarTower ℚ_[l] L (PadicAlgCl l)] [FiniteDimensional ℚ_[l] L]
  [Small.{u + 1} E] [Small.{u + 1} L]

/-- If `E ⊆ L` are finite extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`, then `𝒪_L` is a finite free
`𝒪_E`-module (for the universe `u + 1` copies of the rings of integers) with a Frobenius form:
an `𝒪_E`-linear form `φ` on `𝒪_L` such that every `𝒪_E`-linear form on `𝒪_L` is `φ(s * -)` for a
unique `s ∈ 𝒪_L`. -/
theorem exists_basis_frobeniusForm_integersShrinkMap :
    letI := (integersShrinkMap.{w, u} l E L).toAlgebra
    ∃ (n : ℕ) (_ : Module.Basis (Fin n) (Shrink.{u + 1} (integers l E))
        (Shrink.{u + 1} (integers l L)))
      (φ : Shrink.{u + 1} (integers l L) →ₗ[Shrink.{u + 1} (integers l E)]
        Shrink.{u + 1} (integers l E)),
      Function.Bijective fun s ↦ φ ∘ₗ LinearMap.mulLeft _ s := by
  let := (integersShrinkMap.{w, u} l E L).toAlgebra
  have : IsPrincipalIdealRing (Shrink.{u + 1} (integers l E)) :=
    IsPrincipalIdealRing.of_surjective (shrinkRingEquiv l E).toRingHom
      (shrinkRingEquiv l E).surjective
  have : IsPrincipalIdealRing (Shrink.{u + 1} (integers l L)) :=
    IsPrincipalIdealRing.of_surjective (shrinkRingEquiv l L).toRingHom
      (shrinkRingEquiv l L).surjective
  have : Module.Finite (Shrink.{u + 1} (integers l E)) (Shrink.{u + 1} (integers l L)) :=
    finite_integersShrinkMap l E L
  have : FaithfulSMul (Shrink.{u + 1} (integers l E)) (Shrink.{u + 1} (integers l L)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (integersShrinkMap_injective l E L)
  obtain ⟨φ, hφ⟩ := Module.exists_bijective_comp_mulLeft (Shrink.{u + 1} (integers l E))
    (Shrink.{u + 1} (integers l L))
  exact ⟨_, Module.finBasis _ _, φ, hφ⟩

end Finite

section Divisibility

variable {l} {L}

/-- In the ring of integers of a finite extension of `ℚ_ℓ`, a nonzero element divides a power of
every element of the maximal ideal. -/
lemma exists_dvd_pow_of_mem_maximalIdeal [Algebra ℚ_[l] L] [IsScalarTower ℚ_[l] L (PadicAlgCl l)]
    [FiniteDimensional ℚ_[l] L] {x y : integers l L} (hx : x ≠ 0)
    (hy : y ∈ IsLocalRing.maximalIdeal (integers l L)) : ∃ k : ℕ, x ∣ y ^ k := by
  by_contra! h
  refine hx ((Submodule.mem_bot (integers l L)).1 ?_)
  rw [← Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top]
  refine Submodule.mem_iInf _ |>.2 fun k ↦ ?_
  obtain ⟨c, hc⟩ := (ValuationRing.dvd_total x (y ^ k)).resolve_left (h k)
  rw [hc]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hy k)

variable [Small.{u + 1} L]

/-- In the universe `u + 1` copy of the ring of integers of a finite extension of `ℚ_ℓ`, a nonzero
element divides a power of every element of the maximal ideal. -/
lemma exists_dvd_pow_of_mem_maximalIdealShrink [Algebra ℚ_[l] L]
    [IsScalarTower ℚ_[l] L (PadicAlgCl l)] [FiniteDimensional ℚ_[l] L]
    {x y : Shrink.{u + 1} (integers l L)} (hx : x ≠ 0) (hy : y ∈ maximalIdealShrink l L) :
    ∃ k : ℕ, x ∣ y ^ k := by
  let e := shrinkRingEquiv.{w, u} l L
  have hy' : e.symm y ∈ IsLocalRing.maximalIdeal (integers l L) := by
    rw [maximalIdealShrink, Ideal.mem_map_of_equiv] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rwa [RingEquiv.symm_apply_apply]
  obtain ⟨k, hk⟩ := exists_dvd_pow_of_mem_maximalIdeal (x := e.symm x)
    (by simpa using hx) hy'
  refine ⟨k, ?_⟩
  simpa [map_pow] using map_dvd e hk

end Divisibility

end PadicAlgCl
