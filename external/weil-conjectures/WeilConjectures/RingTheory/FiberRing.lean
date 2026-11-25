/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-!
# Fibre rings of ring maps

Let `R → S` be a ring map and `p` a prime of `R`. We study the fibre ring
`p.Fiber S = κ(p) ⊗[R] S`.

## Main results

* `Ideal.Fiber.toResidueField`: for a prime `q` of `S` over `p`, the map
  `κ(p) ⊗[R] S → κ(q)`, `λ ⊗ b ↦ λ̄ b̄`.
* `Ideal.Fiber.primes_residueField`: the primes of the fibre ring correspond to the primes of `S`
  over `p` (via contraction along `S → κ(p) ⊗[R] S`, with inverse `q ↦ ker (κ(p) ⊗ S → κ(q))`),
  compatibly with inclusions, and the residue fields of corresponding primes agree.
-/

@[expose] public section

open Algebra TensorProduct

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]

/-- The map `κ(p) ⊗[R] S → κ(q)`, `λ ⊗ b ↦ λ̄ b̄`, for a prime `q` of `S` over `p`. -/
noncomputable def Fiber.toResidueField (q : Ideal S) [q.IsPrime] (hq : q.under R = p) :
    p.Fiber S →ₐ[R] q.ResidueField :=
  Algebra.TensorProduct.lift (Ideal.ResidueField.mapₐ p q (Algebra.ofId _ _) hq.symm)
    (IsScalarTower.toAlgHom _ _ _) fun _ _ ↦ .all _ _

instance Fiber.isPrime_ker_toResidueField (q : Ideal S) [q.IsPrime] (hq : q.under R = p) :
    (RingHom.ker (Fiber.toResidueField p q hq)).IsPrime :=
  RingHom.ker_isPrime _

@[simp]
lemma Fiber.toResidueField_one_tmul (q : Ideal S) [q.IsPrime] (hq : q.under R = p) (b : S) :
    Fiber.toResidueField p q hq (1 ⊗ₜ b) = algebraMap S q.ResidueField b := by
  simp [Fiber.toResidueField]

lemma Fiber.isPrime_comap_includeRight (Q : Ideal (p.Fiber S)) (hQ : Q.IsPrime) :
    (Q.comap includeRight.toRingHom).IsPrime ∧ (Q.comap includeRight.toRingHom).under R = p := by
  let x := (PrimeSpectrum.preimageEquivFiber R S ⟨p, ‹_›⟩).symm ⟨Q, hQ⟩
  exact ⟨x.1.2, congr($(x.2).asIdeal)⟩

lemma Fiber.comap_ker_toResidueField (q : Ideal S) [q.IsPrime] (hq : q.under R = p) :
    (RingHom.ker (Fiber.toResidueField p q hq)).comap includeRight.toRingHom = q := by
  let x : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {⟨p, ‹_›⟩} :=
    ⟨⟨q, ‹_›⟩, PrimeSpectrum.ext hq⟩
  exact congr($((PrimeSpectrum.preimageEquivFiber R S ⟨p, ‹_›⟩).left_inv x).1.asIdeal)

lemma Fiber.comap_includeRight_le_iff (Q Q' : Ideal (p.Fiber S)) (hQ : Q.IsPrime)
    (hQ' : Q'.IsPrime) :
    Q.comap includeRight.toRingHom ≤ Q'.comap includeRight.toRingHom ↔ Q ≤ Q' :=
  (PrimeSpectrum.preimageOrderIsoFiber R S ⟨p, ‹_›⟩).symm.le_iff_le (x := ⟨Q, hQ⟩)
    (y := ⟨Q', hQ'⟩)

lemma Fiber.exists_residueField_ringEquiv (q : Ideal S) [q.IsPrime] (hq : q.under R = p) :
    ∃ σ : (RingHom.ker (Fiber.toResidueField p q hq)).ResidueField ≃+* q.ResidueField,
      ∀ c, σ (algebraMap _ _ c) = Fiber.toResidueField p q hq c := by
  set ψ := Fiber.toResidueField p q hq
  let σ := Ideal.ResidueField.lift (RingHom.ker ψ) (ψ : p.Fiber S →+* q.ResidueField) le_rfl
    (fun c hc => by simpa [Ideal.primeCompl, IsUnit.mem_submonoid_iff] using hc)
  have hσ : ∀ c, σ (algebraMap _ _ c) = ψ c := Ideal.ResidueField.lift_algebraMap _ _ _ _
  refine ⟨RingEquiv.ofBijective σ ⟨σ.injective, fun z => ?_⟩, hσ⟩
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := S ⧸ q) z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨algebraMap _ _ ((1 : p.ResidueField) ⊗ₜ[R] x) /
    algebraMap _ _ ((1 : p.ResidueField) ⊗ₜ[R] y), ?_⟩
  rw [map_div₀, hσ, hσ, Ideal.algebraMap_quotient_residueField_mk,
    Ideal.algebraMap_quotient_residueField_mk]
  simp [ψ]

/-- **Primes and residue fields of the fibre ring.** Let `C = κ(p) ⊗[R] S` and `j : S → C`,
`b ↦ 1 ⊗ b`. Then:
1. for a prime `Q` of `C`, `j⁻¹(Q)` is a prime of `S` lying over `p`;
2. for a prime `q` of `S` over `p`, `ker ψ_q` (with `ψ_q : C → κ(q)`, `λ ⊗ b ↦ λ̄ b̄`) is a prime
   of `C` with `j⁻¹(ker ψ_q) = q`;
3. for a prime `Q` of `C`, `ker ψ_{j⁻¹(Q)} = Q`; so `Q ↦ j⁻¹(Q)` is a bijection onto the primes
   of `S` over `p` with inverse `q ↦ ker ψ_q`;
4. `Q ↦ j⁻¹(Q)` preserves and reflects inclusions;
5. `ψ_q` induces an isomorphism `κ(ker ψ_q) ≃ κ(q)` through which it factors.

(blueprint: `theorem-finite-etale-covers-proper-henselian--2`) -/
theorem Fiber.primes_residueField :
    (∀ Q : Ideal (p.Fiber S), Q.IsPrime →
      (Q.comap includeRight.toRingHom).IsPrime ∧ (Q.comap includeRight.toRingHom).under R = p) ∧
    (∀ (q : Ideal S) [q.IsPrime] (hq : q.under R = p),
      (RingHom.ker (Fiber.toResidueField p q hq)).IsPrime ∧
      (RingHom.ker (Fiber.toResidueField p q hq)).comap includeRight.toRingHom = q) ∧
    (∀ (Q : Ideal (p.Fiber S)) [Q.IsPrime] (hQ : (Q.comap includeRight.toRingHom).under R = p),
      RingHom.ker (Fiber.toResidueField p _ hQ) = Q) ∧
    (∀ Q Q' : Ideal (p.Fiber S), Q.IsPrime → Q'.IsPrime →
      (Q.comap includeRight.toRingHom ≤ Q'.comap includeRight.toRingHom ↔ Q ≤ Q')) ∧
    (∀ (q : Ideal S) [q.IsPrime] (hq : q.under R = p),
      ∃ σ : (RingHom.ker (Fiber.toResidueField p q hq)).ResidueField ≃+* q.ResidueField,
        ∀ c, σ (algebraMap _ _ c) = Fiber.toResidueField p q hq c) := by
  refine ⟨Fiber.isPrime_comap_includeRight p, fun q _ hq =>
    ⟨inferInstance, Fiber.comap_ker_toResidueField p q hq⟩, fun Q _ hQ => ?_,
    Fiber.comap_includeRight_le_iff p, Fiber.exists_residueField_ringEquiv p⟩
  have h := Fiber.comap_ker_toResidueField p _ hQ
  exact le_antisymm
    ((Fiber.comap_includeRight_le_iff p _ _ inferInstance ‹_›).1 h.le)
    ((Fiber.comap_includeRight_le_iff p _ _ ‹_› inferInstance).1 h.ge)

end Ideal
