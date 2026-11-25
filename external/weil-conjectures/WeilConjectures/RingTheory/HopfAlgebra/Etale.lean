/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Etale.Descent
public import WeilConjectures.Mathlib.RingTheory.Etale.Field
public import WeilConjectures.Mathlib.RingTheory.TensorProduct.Maps
public import WeilConjectures.RingTheory.Bialgebra.Frobenius

/-!
# Finite Hopf algebras of dimension prime to the characteristic are étale

Let `A` be a finite-dimensional commutative Hopf algebra over a field `K` of characteristic
`p ≥ 0`, the coordinate ring of a finite group scheme `G` over `K`. If `p ∤ dim_K A` (for
`p = 0`: always), then `A` is étale over `K`.

For `p = 0` this is Cartier's theorem `HopfAlgebra.isReduced_of_charZero`: `A` is reduced, hence
étale over the perfect field `K`. For `p > 0` we may assume that `K` is algebraically closed,
since étaleness descends along `K → K̄`. Let `𝔪` be the augmentation ideal. The local ring `A_𝔪`
is the coordinate ring of the identity component `G⁰`; it is the quotient of `A` by the ideal
`Bialgebra.identityComponentIdeal`, which is a coideal, so `A_𝔪` is a finite local bialgebra and
`dim_K A_𝔪 = pʳ` by `Bialgebra.exists_finrank_eq_pow`. Translations by the `K`-points of `G`
identify all local rings of `A` with `A_𝔪`, so `dim_K A = #G(K) · pʳ`. Hence `r = 0`, every local
ring of `A` is `K`, and `A` is étale.

## Main definitions

- `Bialgebra.identityComponentIdeal`: the kernel of `A → A_𝔪`, the ideal of the identity
  component.

## Main statements

- `Bialgebra.isCoideal_identityComponentIdeal`: the identity component is a subgroup: its ideal is
  a coideal.
- `HopfAlgebra.finrank_localization_eq`: over an algebraically closed field all local rings of a
  finite Hopf algebra have the same dimension.
- `HopfAlgebra.etale_of_not_dvd_finrank`: a finite Hopf algebra whose dimension is prime to the
  characteristic is étale.

## Blueprint

`HopfAlgebra.etale_of_not_dvd_finrank` is the algebraic content of
`proposition-multiplication-n--2`.
-/

@[expose] public section

open Module TensorProduct

namespace Bialgebra

open Coalgebra

variable {K A : Type*} [Field K] [CommRing A] [Bialgebra K A]

local notation "𝔪" => RingHom.ker (Bialgebra.counitAlgHom K A)

/-- The augmentation ideal is prime. -/
instance isPrime_ker_counitAlgHom : (𝔪).IsPrime := RingHom.ker_isPrime _

variable (K A) in
/-- The ideal of the identity component: the kernel of the localization `A → A_𝔪` at the
augmentation ideal `𝔪`. For a finite-dimensional `A` the localization is surjective, so
`A ⧸ identityComponentIdeal K A` is the local ring `A_𝔪`. -/
abbrev identityComponentIdeal : Ideal A :=
  RingHom.ker (algebraMap A (Localization.AtPrime 𝔪))

/-- An element of `identityComponentIdeal K A` is killed by an element not in `𝔪`. -/
theorem exists_mul_eq_zero_of_mem_identityComponentIdeal {x : A}
    (hx : x ∈ identityComponentIdeal K A) :
    ∃ s, counitAlgHom K A s ≠ 0 ∧ s * x = 0 := by
  obtain ⟨⟨s, hs⟩, hsx⟩ := (IsLocalization.map_eq_zero_iff (𝔪).primeCompl _ x).1 hx
  exact ⟨s, hs, hsx⟩

/-- The ideal of the identity component is contained in the augmentation ideal. -/
theorem identityComponentIdeal_le : identityComponentIdeal K A ≤ 𝔪 := fun x hx ↦ by
  obtain ⟨s, hs, hsx⟩ := exists_mul_eq_zero_of_mem_identityComponentIdeal hx
  have h := congrArg (counitAlgHom K A) hsx
  rw [map_mul, map_zero] at h
  exact (mul_eq_zero.1 h).resolve_left hs

/-- `(ε ⊗ ε) ∘ Δ = ε`. -/
theorem productMap_counitAlgHom_comul (a : A) :
    Algebra.TensorProduct.productMap (counitAlgHom K A) (counitAlgHom K A) (comul a) =
      counitAlgHom K A a := by
  let r := Coalgebra.Repr.arbitrary K a
  rw [← r.eq, map_sum]
  simp_rw [Algebra.TensorProduct.productMap_apply_tmul, counitAlgHom_apply]
  conv_rhs => rw [← Coalgebra.sum_counit_smul r]
  simp [map_sum, map_smul, smul_eq_mul]

variable [FiniteDimensional K A]

/-- The coordinate ring of the identity component is local. -/
theorem isLocalRing_quotient_identityComponentIdeal :
    IsLocalRing (A ⧸ identityComponentIdeal K A) := by
  have : IsArtinianRing A := .of_finite K A
  let e := RingHom.quotientKerEquivOfSurjective
    (IsArtinianRing.localization_surjective (𝔪).primeCompl (Localization.AtPrime 𝔪))
  have : Nontrivial (A ⧸ identityComponentIdeal K A) :=
    Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (RingHom.ker_ne_top _)
      identityComponentIdeal_le)
  exact .of_surjective' e.symm.toRingHom e.symm.surjective

variable (K A) in
/-- The counit of `A`, as a `K`-point of the quotient by `identityComponentIdeal`. -/
noncomputable abbrev identityComponentCounit : (A ⧸ identityComponentIdeal K A) →ₐ[K] K :=
  Ideal.Quotient.liftₐ _ (counitAlgHom K A) fun _ hx ↦ identityComponentIdeal_le hx

/-- The augmentation ideal of the coordinate ring of the identity component is nilpotent. -/
theorem isNilpotent_ker_identityComponentCounit :
    IsNilpotent (RingHom.ker (identityComponentCounit K A)) := by
  have := isLocalRing_quotient_identityComponentIdeal (K := K) (A := A)
  have : IsArtinianRing (A ⧸ identityComponentIdeal K A) := .of_finite K _
  have h := IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective
    (identityComponentCounit K A) fun c ↦ ⟨algebraMap K _ c, by simp⟩)
  rw [h, ← IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  exact IsArtinianRing.isNilpotent_jacobson_bot

/-- The identity component is a closed subgroup scheme: its ideal is a coideal, so the local ring
at the identity inherits a bialgebra structure. The comultiplication `ψ : A → A_𝔪 ⊗ A_𝔪` sends
an element `s ∉ 𝔪` to a unit, as `ψ s - ε s` is nilpotent; hence it kills every `x` with
`s x = 0`. -/
instance isCoideal_identityComponentIdeal :
    ((identityComponentIdeal K A).restrictScalars K).IsCoideal := by
  constructor
  · intro x hx
    exact identityComponentIdeal_le hx
  · intro x hx
    obtain ⟨s, hs, hsx⟩ := exists_mul_eq_zero_of_mem_identityComponentIdeal hx
    let mk := Ideal.Quotient.mkₐ K (identityComponentIdeal K A)
    let ψ := (Algebra.TensorProduct.map mk mk).comp (comulAlgHom K A)
    change ψ x = 0
    let χ := Algebra.TensorProduct.productMap (identityComponentCounit K A)
      (identityComponentCounit K A)
    have hχψ (a : A) : χ (ψ a) = counitAlgHom K A a := by
      rw [← productMap_counitAlgHom_comul]
      simp only [χ, ψ, AlgHom.comp_apply, comulAlgHom_apply]
      rw [← AlgHom.comp_apply]
      congr 1
      ext <;> rfl
    have hnil : IsNilpotent (ψ s - algebraMap K _ (counitAlgHom K A s)) :=
      Algebra.TensorProduct.isNilpotent_of_productMap_eq_zero
        isNilpotent_ker_identityComponentCounit isNilpotent_ker_identityComponentCounit
        (by rw [map_sub, hχψ, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
          sub_self])
    have hunit : IsUnit (ψ s) := by
      have hu : IsUnit (algebraMap K ((A ⧸ identityComponentIdeal K A) ⊗[K]
          (A ⧸ identityComponentIdeal K A)) (counitAlgHom K A s)) := (Ne.isUnit hs).map _
      simpa using hnil.isUnit_add_left_of_commute hu (Commute.all _ _)
    have h := congrArg ψ hsx
    rw [map_mul, map_zero] at h
    exact (hunit.mul_right_eq_zero).1 h

end Bialgebra

namespace HopfAlgebra

open Bialgebra

variable {K A : Type*} [Field K] [CommRing A] [HopfAlgebra K A]

local notation "𝔪" => RingHom.ker (Bialgebra.counitAlgHom K A)

/-- Over an algebraically closed field, translations identify the local ring of a finite
group scheme at any point with the local ring at the identity. -/
theorem finrank_localization_eq [IsAlgClosed K] [FiniteDimensional K A] (m : Ideal A)
    [m.IsMaximal] :
    finrank K (Localization.AtPrime m) = finrank K (Localization.AtPrime 𝔪) := by
  obtain ⟨g, rfl⟩ := exists_algHom_ker_eq_of_isMaximal K A m
  obtain ⟨τ, hτ⟩ := exists_algEquiv_comp_eq_counitAlgHom g
  have hτ' (a : A) : counitAlgHom K A a = g (τ a) := by rw [← hτ]; rfl
  have H : (𝔪).primeCompl.map τ.toRingEquiv.toMonoidHom = (RingHom.ker g).primeCompl := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [Ideal.primeCompl, RingHom.mem_ker, hτ'] using hx
    · intro hy
      refine ⟨τ.symm y, ?_, by simp⟩
      simpa [Ideal.primeCompl, RingHom.mem_ker, hτ'] using hy
  let e := IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime 𝔪)
    (Localization.AtPrime (RingHom.ker g)) τ.toRingEquiv H
  let e' : Localization.AtPrime 𝔪 ≃ₐ[K] Localization.AtPrime (RingHom.ker g) :=
    AlgEquiv.ofRingEquiv (f := e) fun c ↦ by
      rw [IsScalarTower.algebraMap_apply K A, IsLocalization.ringEquivOfRingEquiv_eq,
        IsScalarTower.algebraMap_apply K A (Localization.AtPrime (RingHom.ker g))]
      simp
  exact e'.toLinearEquiv.finrank_eq.symm

variable (K A) in
/-- A finite-dimensional commutative Hopf algebra over an algebraically closed field of
characteristic `p > 0` whose dimension is prime to `p` is étale. -/
theorem etale_of_not_dvd_finrank_of_isAlgClosed [IsAlgClosed K] [FiniteDimensional K A]
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp : ¬ p ∣ finrank K A) : Algebra.Etale K A := by
  have : IsArtinianRing A := .of_finite K A
  have : Finite (MaximalSpectrum A) :=
    Finite.of_injective _ MaximalSpectrum.toPrimeSpectrum_injective
  have := Fintype.ofFinite (MaximalSpectrum A)
  have (m : MaximalSpectrum A) : Module.Finite K (Localization.AtPrime m.asIdeal) :=
    .of_surjective (IsScalarTower.toAlgHom K A _).toLinearMap
      (IsArtinianRing.localization_surjective m.asIdeal.primeCompl _)
  have := isLocalRing_quotient_identityComponentIdeal (K := K) (A := A)
  obtain ⟨r, hr⟩ := Bialgebra.exists_finrank_eq_pow K (A ⧸ identityComponentIdeal K A) p
  let e : (A ⧸ identityComponentIdeal K A) ≃ₐ[K] Localization.AtPrime 𝔪 :=
    Ideal.quotientKerAlgEquivOfSurjective (f := IsScalarTower.toAlgHom K A _)
      (IsArtinianRing.localization_surjective (𝔪).primeCompl _)
  have hall (m : MaximalSpectrum A) : finrank K (Localization.AtPrime m.asIdeal) = p ^ r := by
    have := m.isMaximal
    rw [finrank_localization_eq, ← e.toLinearEquiv.finrank_eq, hr]
  have hr0 : r = 0 := by
    by_contra hr0
    apply hp
    rw [((MaximalSpectrum.toPiLocalizationEquiv A).restrictScalars K).toLinearEquiv.finrank_eq,
      Module.finrank_pi_fintype]
    exact Finset.dvd_sum fun m _ ↦ hall m ▸ dvd_pow_self p hr0
  exact .of_forall_finrank_localization_eq_one fun m ↦ by rw [hall, hr0, pow_zero]

variable (K A) in
/-- **Blueprint `proposition-multiplication-n--2`**, algebraic form: a finite-dimensional
commutative Hopf algebra over a field of characteristic `p` whose dimension is prime to `p` (for
`p = 0`: any finite-dimensional one) is étale. -/
theorem etale_of_not_dvd_finrank [FiniteDimensional K A] (p : ℕ) [CharP K p]
    (hp : ¬ p ∣ finrank K A) : Algebra.Etale K A := by
  rcases CharP.char_is_prime_or_zero K p with hprime | rfl
  · have : Fact p.Prime := ⟨hprime⟩
    let L := AlgebraicClosure K
    have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
    have := etale_of_not_dvd_finrank_of_isAlgClosed L (L ⊗[K] A) p
      (by rwa [Module.finrank_baseChange])
    exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat L
  · have : CharZero K := CharP.charP_to_charZero K
    have := isReduced_of_charZero (k := K) (A := A)
    exact Algebra.Etale.of_isReduced_of_perfectField K A

end HopfAlgebra
