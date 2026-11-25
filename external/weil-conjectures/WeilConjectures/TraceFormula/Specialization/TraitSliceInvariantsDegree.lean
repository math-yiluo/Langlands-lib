/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Normal.Closure
public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisDegree
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChange

/-!

# The finite subextensions of `L^sep / L` have degree prime to `ℓ`

Let `L = Ω(K⟦t⟧) ⊆ Ω_K` be the compositum of the slice trait
(`AlgebraicGeometry.traitTensorCompositum`, `K` algebraically closed) and `L^sep` its separable
closure. The finite Galois subextensions of `L^sep / L` have `p`-power degree
(`AlgebraicGeometry.exists_finrank_traitTensorCompositum_eq_pow`), `p` the characteristic
exponent of `k'`. Hence, for a prime `ℓ` different from the characteristic of `k'`, no finite
Galois subextension of `L^sep / L` has degree divisible by `ℓ`
(`AlgebraicGeometry.not_dvd_finrank_traitTensorCompositum`), and neither has any finite
subextension, whose degree divides that of its normal closure
(`IntermediateField.not_dvd_finrank_of_forall_finiteGalois`). This is the degree hypothesis of the
stabilization of nearby cycles along Galois layers with `ℚ̄_ℓ`-coefficients
(`NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_of_integralModel`).

-/

@[expose] public section

/-- **Degrees of finite subextensions from those of the finite Galois ones**: in a Galois extension
`Ω / L`, if no finite Galois subextension has degree divisible by `ℓ`, then no finite subextension
has: its degree divides that of its normal closure. -/
theorem IntermediateField.not_dvd_finrank_of_forall_finiteGalois {L Ω : Type*} [Field L]
    [Field Ω] [Algebra L Ω] [IsGalois L Ω] {ℓ : ℕ}
    (h : ∀ L₁ : FiniteGaloisIntermediateField L Ω, ¬ ℓ ∣ Module.finrank L L₁)
    (M : IntermediateField L Ω) [FiniteDimensional L M] : ¬ ℓ ∣ Module.finrank L M := by
  intro hM
  refine h (.mk (IntermediateField.normalClosure L M Ω)) (hM.trans ?_)
  exact IntermediateField.finrank_dvd_of_le_right (IntermediateField.le_normalClosure M)

universe u

namespace AlgebraicGeometry

attribute [local instance] traitGenericFieldAlgebra

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K] [IsAlgClosed K]

-- the instances `Module L L₁` for the concrete composita are found slowly
/-- **The finite Galois subextensions of `L^sep / L` have degree prime to `ℓ`**, for a prime `ℓ`
different from the characteristic of `k'`: their degree is a power of the characteristic
exponent of `k'`. -/
lemma not_dvd_finrank_traitTensorCompositum {ℓ : ℕ} (hℓ : ringChar k' ≠ ℓ) (hℓ' : ℓ.Prime)
    (L₁ : FiniteGaloisIntermediateField (traitTensorCompositum (PowerSeries K)
      (traitGenericField k') (traitGenericField K)) (traitTensorCompositumSep (PowerSeries K)
        (traitGenericField k') (traitGenericField K))) :
    ¬ ℓ ∣ Module.finrank (traitTensorCompositum (PowerSeries K) (traitGenericField k')
      (traitGenericField K)) L₁ := by
  obtain ⟨p, hp, hpℓ, hpk⟩ :=
    ProEtale.CondensedRing.exists_prime_ne_dvd_of_natCast_eq_zero k' hℓ
  intro hdvd
  obtain ⟨n, hn⟩ := exists_finrank_traitTensorCompositum_eq_pow (K := K) hp hpk L₁
  rw [hn] at hdvd
  exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ' hp).1 (hℓ'.dvd_of_dvd_pow hdvd)).symm

end AlgebraicGeometry
