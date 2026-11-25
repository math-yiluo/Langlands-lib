/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Module.AdicDualityTransport
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantCohomologyBaseChange

/-!
# Duality for the cohomology of `ℚ̄_ℓ` from duality with coefficients `ℤ/ℓᵐ`

Let `S` be a quasi-compact quasi-separated scheme whose pro-étale cohomology groups
`Hᵏ(S, ℤ/ℓᵐ)` are finite. This file transports dualities between the finite-level cohomology
groups `Hⁱ(S, ℤ/ℓᵐ)` and `Hʲ(S, ℤ/ℓᵐ)` — nondegenerate pairings with values in `ℤ/ℓᵐ` which are
similitudes for given endomorphisms (Frobenius) of the integral cohomology — to a perfect
pairing between the cohomology groups `Hⁱ(S, ℚ̄_ℓ)` and `Hʲ(S, ℚ̄_ℓ)` of the constant `ℓ`-adic
sheaf, which is a similitude for the induced endomorphisms
(`AlgebraicGeometry.ProEtale.exists_isPerfPair_adicConstantH`). The finite-level dualities need
not be compatible with each other.

The ingredients are: finite generation of `Hⁿ(S, ℤ_ℓ)` and the Bockstein sequences
(`WeilConjectures.AlgebraicGeometry.ProEtale.IntegralAdicCohomology`),
`Hⁿ(S, ℚ̄_ℓ) = ℚ̄_ℓ ⊗ Hⁿ(S, ℤ_ℓ)`
(`AlgebraicGeometry.ProEtale.isBaseChange_integralToAdicConstantH`)
and the linear algebra of `LinearMap.exists_isPerfPair_of_finiteLevel`. This is the transport
step of blueprint `theorem-poincare-duality--6` (`theorem-poincare-duality--9`), for the constant
coefficient sheaf.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (S : Scheme.{u})

/-- The ℓ-power torsion of a finitely generated `ℤ_ℓ`-module is killed by a fixed power of `ℓ`,
in the form used by the Bockstein sequences. -/
lemma exists_pow_smul_eq_zero_of_pow_smul_eq_zero {A : Type*} [AddCommGroup A]
    [Module ℤ_[l] A] [Module.Finite ℤ_[l] A] :
    ∃ e : ℕ, ∀ x : A, (∃ k, (l : ℤ_[l]) ^ k • x = 0) → (l : ℤ_[l]) ^ e • x = 0 := by
  obtain ⟨e, he⟩ := LinearMap.exists_pow_smul_eq_zero_of_finite (p := l) (A := A)
  refine ⟨e, fun x ⟨k, hk⟩ ↦ he x ⟨⟨(l : ℤ_[l]) ^ k, pow_mem (mem_nonZeroDivisors_of_ne_zero
    (by exact_mod_cast (Fact.out : l.Prime).ne_zero)) k⟩, hk⟩⟩

lemma pow_smul_eq_zero_mono {A : Type*} [AddCommGroup A] [Module ℤ_[l] A] {e e' : ℕ}
    (hee' : e ≤ e')
    (he : ∀ x : A, (∃ k, (l : ℤ_[l]) ^ k • x = 0) → (l : ℤ_[l]) ^ e • x = 0) (x : A)
    (hx : ∃ k, (l : ℤ_[l]) ^ k • x = 0) : (l : ℤ_[l]) ^ e' • x = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hee'
  rw [pow_add, mul_comm, mul_smul, he x hx, smul_zero]

/-- **Duality for `ℚ̄_ℓ`-cohomology from finite-level dualities.** Let `S` be quasi-compact and
quasi-separated with finite cohomology groups `Hᵏ(S, ℤ/ℓᵐ)`. Let `F_A`, `F_B` be endomorphisms of
`Hⁱ(S, ℤ_ℓ)`, `Hʲ(S, ℤ_ℓ)`, and `F_V`, `F_W` endomorphisms of `Hⁱ(S, ℚ̄_ℓ)`, `Hʲ(S, ℚ̄_ℓ)`
extending them. If for every `m` there is a pairing `Hⁱ(S, ℤ/ℓᵐ) × Hʲ(S, ℤ/ℓᵐ) ⟶ ℤ/ℓᵐ`,
nondegenerate on both sides, whose restriction to the integral classes is a `c`-similitude, then
there is a perfect pairing `Hⁱ(S, ℚ̄_ℓ) × Hʲ(S, ℚ̄_ℓ) ⟶ ℚ̄_ℓ` which is a `c`-similitude for
`F_V`, `F_W`. -/
theorem exists_isPerfPair_adicConstantH [CompactSpace S] [QuasiSeparatedSpace S]
    (hfin : ∀ m k, Finite (FiniteAdicH S l m k)) (i j : ℕ)
    (FA : IntegralAdicH S l i →ₗ[ℤ_[l]] IntegralAdicH S l i)
    (FB : IntegralAdicH S l j →ₗ[ℤ_[l]] IntegralAdicH S l j) (c : ℤ_[l])
    (Q : ∀ m, FiniteAdicH S l m i →ₗ[ℤ_[l]] FiniteAdicH S l m j →ₗ[ℤ_[l]]
      ℤ_[l] ⧸ Ideal.span {(l : ℤ_[l]) ^ m})
    (hQl : ∀ m, Function.Injective (Q m)) (hQr : ∀ m, Function.Injective (Q m).flip)
    (hQF : ∀ m a b, Q m (reduction S l m i (FA a)) (reduction S l m j (FB b)) =
      c • Q m (reduction S l m i a) (reduction S l m j b))
    (FV : AdicConstantH l S i →ₗ[PadicAlgCl l] AdicConstantH l S i)
    (FW : AdicConstantH l S j →ₗ[PadicAlgCl l] AdicConstantH l S j)
    (hFV : ∀ a, FV (integralToAdicConstantH l S i a) = integralToAdicConstantH l S i (FA a))
    (hFW : ∀ b, FW (integralToAdicConstantH l S j b) = integralToAdicConstantH l S j (FB b)) :
    ∃ P : AdicConstantH l S i →ₗ[PadicAlgCl l] AdicConstantH l S j →ₗ[PadicAlgCl l]
        PadicAlgCl l,
      P.IsPerfPair ∧ ∀ x y, P (FV x) (FW y) = algebraMap ℤ_[l] (PadicAlgCl l) c * P x y := by
  have hfin' (n : ℕ) : Module.Finite ℤ_[l] (IntegralAdicH S l n) :=
    have := hfin 1 n
    module_finite_integralAdicH S l n fun m k _ ↦ hfin m k
  have := hfin' i
  have := hfin' j
  have := hfin' (i + 1)
  have := hfin' (j + 1)
  obtain ⟨eA, heA⟩ := exists_pow_smul_eq_zero_of_pow_smul_eq_zero l
    (A := IntegralAdicH S l (i + 1))
  obtain ⟨eB, heB⟩ := exists_pow_smul_eq_zero_of_pow_smul_eq_zero l
    (A := IntegralAdicH S l (j + 1))
  exact LinearMap.exists_isPerfPair_of_finiteLevel FA FB c (max eA eB)
    (fun m ↦ reduction S l m i) (fun m ↦ reduction S l m j) Q
    (fun m _ ha ↦ exists_eq_pow_smul_of_reduction_eq_zero S l m i ha)
    (fun m _ hb ↦ exists_eq_pow_smul_of_reduction_eq_zero S l m j hb)
    (fun m y ↦ pow_smul_mem_range_reduction S l m i _
      (pow_smul_eq_zero_mono l (le_max_left _ _) heA) y)
    (fun m y ↦ pow_smul_mem_range_reduction S l m j _
      (pow_smul_eq_zero_mono l (le_max_right _ _) heB) y)
    hQl hQr hQF (isBaseChange_integralToAdicConstantH l S i)
    (isBaseChange_integralToAdicConstantH l S j) FV FW hFV hFW

end AlgebraicGeometry.ProEtale
