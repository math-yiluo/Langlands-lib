/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.PolynomialAlgebra
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Tensor products with a localization of the polynomial ring

Let `k` be a field and `h ∈ k[X]` nonzero, so that `R = k[X]_h` is the coordinate ring of the
open subscheme `D(h)` of the affine line. For a `k`-algebra `D` we have `D ⊗_k R = D[X]_h`.

## Main results

- `TensorProduct.isDomain_localizationAway`: `D ⊗_k k[X]_h` is a domain if `D` is.
- `TensorProduct.uniqueFactorizationMonoid_localizationAway`: `D ⊗_k k[X]_h` is a unique
  factorization domain if `D` is.
- `TensorProduct.uniqueFactorizationMonoid_localization_atPrime`: if `A` is a `k`-algebra whose
  localization `A_𝔭` at a prime is a UFD, then so is the localization of `A ⊗_k k[X]_h` at the
  image of `A \ 𝔭`.
- `TensorProduct.exists_units_eq_tmul`: for `k` algebraically closed and `A` a domain, every unit
  of `A ⊗_k k[X]_h` is a pure tensor `a ⊗ r` of units (as `h` splits into linear factors, which are
  prime in `A[X]`).
-/

@[expose] public section

universe u

open Polynomial TensorProduct

namespace TensorProduct

variable {k : Type u} [Field k]

/-- The image `1 ⊗ h` of a nonzero `h ∈ k[X]` in `D ⊗_k k[X]` is nonzero for `D` nontrivial. -/
lemma one_tmul_ne_zero (D : Type u) [CommRing D] [Nontrivial D] [Algebra k D]
    {h : k[X]} (hh : h ≠ 0) : (1 : D) ⊗ₜ[k] h ≠ 0 := by
  intro H
  have := congrArg (polyEquivTensor k D).symm H
  rw [polyEquivTensor_symm_apply_tmul_eq_smul, one_smul, map_zero,
    Polynomial.map_eq_zero_iff (algebraMap k D).injective] at this
  exact hh this

/-- `D ⊗_k k[X] ≅ D[X]` is a domain if `D` is. -/
instance (D : Type u) [CommRing D] [IsDomain D] [Algebra k D] : IsDomain (D ⊗[k] k[X]) :=
  (polyEquivTensor k D).toMulEquiv.symm.isDomain _

/-- Over a domain `A`, a divisor of a product of linear polynomials `X - C (v i)` is a unit
constant times a sub-product. -/
lemma exists_eq_C_mul_prod_of_dvd_prod {A ι : Type*} [CommRing A] [IsDomain A] (v : ι → A)
    (s : Multiset ι) (p : A[X]) (hp : p ∣ (s.map fun i ↦ X - C (v i)).prod) :
    ∃ a : Aˣ, ∃ t ≤ s, p = C (a : A) * (t.map fun i ↦ X - C (v i)).prod := by
  induction s using Multiset.induction_on generalizing p with
  | empty =>
    rw [Multiset.map_zero, Multiset.prod_zero] at hp
    obtain ⟨a, ha, rfl⟩ := Polynomial.isUnit_iff.mp (isUnit_of_dvd_one hp)
    exact ⟨ha.unit, 0, le_rfl, by simp⟩
  | cons i s ih =>
    obtain ⟨q, hq⟩ := hp
    rw [Multiset.map_cons, Multiset.prod_cons] at hq
    have hdvd : X - C (v i) ∣ p * q := Dvd.intro _ hq
    rcases (prime_X_sub_C (v i)).dvd_or_dvd hdvd with ⟨p', rfl⟩ | ⟨q', rfl⟩
    · obtain ⟨a, t, ht, rfl⟩ := ih p' ⟨q, mul_left_cancel₀ (X_sub_C_ne_zero (v i))
        (by linear_combination hq)⟩
      refine ⟨a, i ::ₘ t, Multiset.cons_le_cons i ht, ?_⟩
      rw [Multiset.map_cons, Multiset.prod_cons]
      ring
    · obtain ⟨a, t, ht, rfl⟩ := ih p ⟨q', mul_left_cancel₀ (X_sub_C_ne_zero (v i))
        (by linear_combination hq)⟩
      exact ⟨a, t, ht.trans (Multiset.le_cons_self s i), rfl⟩

/-- Let `k` be algebraically closed and `A` a `k`-algebra which is a domain. A divisor in `A[X]`
of the image of a nonzero `f ∈ k[X]` is `C a * g` for a unit `a` of `A` and a divisor `g` of `f`
in `k[X]`. -/
lemma exists_eq_C_mul_map_of_dvd_map [IsAlgClosed k] {A : Type*} [CommRing A] [IsDomain A]
    [Algebra k A] {f : k[X]} (hf : f ≠ 0) {p : A[X]} (hp : p ∣ f.map (algebraMap k A)) :
    ∃ a : Aˣ, ∃ g : k[X], g ∣ f ∧ p = C (a : A) * g.map (algebraMap k A) := by
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C (IsAlgClosed.card_roots_eq_natDegree
    (p := f))
  rw [← hfac, Polynomial.map_mul, map_C, Polynomial.map_multiset_prod, Multiset.map_map] at hp
  have hu : IsUnit (C (algebraMap k A f.leadingCoeff)) :=
    (((leadingCoeff_ne_zero.mpr hf).isUnit).map (algebraMap k A)).map C
  rw [hu.dvd_mul_left] at hp
  obtain ⟨a, t, ht, rfl⟩ := exists_eq_C_mul_prod_of_dvd_prod (algebraMap k A) f.roots p
    (by simpa [Function.comp_def] using hp)
  refine ⟨a, (t.map fun r ↦ X - C r).prod, ?_, ?_⟩
  · rw [← hfac]
    exact (Multiset.prod_dvd_prod_of_le (Multiset.map_le_map ht)).mul_left _
  · simp [Polynomial.map_multiset_prod, Multiset.map_map]

/-- The isomorphism `D ⊗_k k[X]_h ≃ (D ⊗_k k[X])_h` of `D`-algebras. -/
noncomputable abbrev tensorAwayEquiv (D : Type u) [CommRing D] [Algebra k D] (h : k[X]) :
    D ⊗[k] Localization.Away h ≃ₐ[D] Localization.Away ((1 : D) ⊗ₜ[k] h) :=
  IsLocalization.Away.tensorProductEquivTMulRight k D h _

/-- `D ⊗_k k[X]_h` is a domain if `D` is a domain and `h ≠ 0`. -/
theorem isDomain_localizationAway (D : Type u) [CommRing D] [IsDomain D] [Algebra k D]
    {h : k[X]} (hh : h ≠ 0) : IsDomain (D ⊗[k] Localization.Away h) :=
  haveI : IsDomain (Localization.Away ((1 : D) ⊗ₜ[k] h)) :=
    IsLocalization.isDomain_localization
      (powers_le_nonZeroDivisors_of_noZeroDivisors (one_tmul_ne_zero D hh))
  (tensorAwayEquiv D h).toMulEquiv.isDomain _

/-- `D ⊗_k k[X]_h` is a unique factorization monoid if `D` is a unique factorization domain:
it is a localization of `D ⊗_k k[X] = D[X]`. -/
theorem uniqueFactorizationMonoid_localizationAway (D : Type u) [CommRing D] [IsDomain D]
    [Algebra k D] [UniqueFactorizationMonoid D] (h : k[X]) :
    UniqueFactorizationMonoid (D ⊗[k] Localization.Away h) :=
  haveI : UniqueFactorizationMonoid (D ⊗[k] k[X]) :=
    (polyEquivTensor k D).toMulEquiv.uniqueFactorizationMonoid inferInstance
  (tensorAwayEquiv D h).toMulEquiv.symm.uniqueFactorizationMonoid inferInstance

/-- Let `A` be a `k`-algebra, `𝔭` a prime of `A` whose localization `A_𝔭` is a unique
factorization domain, and `B ≅ A ⊗_k k[X]_h` as `A`-algebras with `h ≠ 0`. Then the localization
of `B` at the image of `A \ 𝔭` is a unique factorization domain, being `A_𝔭 ⊗_k k[X]_h`. -/
theorem uniqueFactorizationMonoid_localization_atPrime {A D B : Type u} [CommRing A]
    [Algebra k A] [CommRing D] [Algebra A D] [Algebra k D] [IsScalarTower k A D] (𝔭 : Ideal A)
    [𝔭.IsPrime] [IsLocalization.AtPrime D 𝔭] [IsDomain D] [UniqueFactorizationMonoid D]
    [CommRing B] [Algebra A B] {h : k[X]} (hh : h ≠ 0)
    (e : A ⊗[k] Localization.Away h ≃ₐ[A] B) :
    IsDomain (Localization (Algebra.algebraMapSubmonoid B 𝔭.primeCompl)) ∧
      UniqueFactorizationMonoid (Localization (Algebra.algebraMapSubmonoid B 𝔭.primeCompl)) := by
  let f : Localization (Algebra.algebraMapSubmonoid B 𝔭.primeCompl) ≃+*
      D ⊗[k] Localization.Away h :=
    (IsLocalization.algEquiv (Algebra.algebraMapSubmonoid B 𝔭.primeCompl) _
      (B ⊗[A] D)).toRingEquiv.trans <|
    (Algebra.TensorProduct.comm A B D).toRingEquiv.trans <|
    (Algebra.TensorProduct.congr (AlgEquiv.refl (R := A) (A₁ := D)) e.symm).toRingEquiv.trans
    (Algebra.TensorProduct.cancelBaseChange k A D D _).toRingEquiv
  have := isDomain_localizationAway D hh
  exact ⟨f.toMulEquiv.isDomain _,
    f.toMulEquiv.symm.uniqueFactorizationMonoid (uniqueFactorizationMonoid_localizationAway D h)⟩

/-- **Units of `A ⊗_k k[X]_h`.** Let `k` be algebraically closed, `A` a `k`-algebra which is a
domain and `h ≠ 0`. Every unit of `A ⊗_k k[X]_h = A[X]_h` is of the form `a ⊗ r` with `a` a unit
of `A` and `r` a unit of `k[X]_h`: writing `h = c ∏ (X - αᵢ)`, a divisor of a power of `h` in
`A[X]` is a unit of `A` times a product of the primes `X - αᵢ`. -/
theorem exists_units_eq_tmul [IsAlgClosed k] (A : Type u) [CommRing A] [IsDomain A] [Algebra k A]
    {h : k[X]} (hh : h ≠ 0) (u : (A ⊗[k] Localization.Away h)ˣ) :
    ∃ (a : Aˣ) (r : (Localization.Away h)ˣ),
      (u : A ⊗[k] Localization.Away h) = (a : A) ⊗ₜ (r : Localization.Away h) := by
  let : Algebra (A ⊗[k] k[X]) (A ⊗[k] Localization.Away h) :=
    (Algebra.TensorProduct.map (AlgHom.id k A)
      (IsScalarTower.toAlgHom k k[X] (Localization.Away h))).toAlgebra
  have : IsScalarTower A (A ⊗[k] k[X]) (A ⊗[k] Localization.Away h) :=
    .of_algebraMap_eq fun _ ↦ by simp [RingHom.algebraMap_toAlgebra]
  have hloc := IsLocalization.tensorProduct_tensorProduct_right k A (Submonoid.powers h)
    (Localization.Away h) (by ext <;> simp [RingHom.algebraMap_toAlgebra])
  rw [Submonoid.map_powers, Algebra.TensorProduct.includeRight_apply] at hloc
  have halg (x : A) (y : k[X]) : algebraMap (A ⊗[k] k[X]) (A ⊗[k] Localization.Away h)
      (x ⊗ₜ y) = x ⊗ₜ algebraMap k[X] _ y := rfl
  have hM : Submonoid.powers ((1 : A) ⊗ₜ[k] h) ≤ nonZeroDivisors (A ⊗[k] k[X]) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors (one_tmul_ne_zero A hh)
  obtain ⟨⟨P, s, m, rfl⟩, hP⟩ := IsLocalization.surj (Submonoid.powers ((1 : A) ⊗ₜ[k] h))
    (u : A ⊗[k] Localization.Away h)
  obtain ⟨⟨Q, s', n, rfl⟩, hQ⟩ := IsLocalization.surj (Submonoid.powers ((1 : A) ⊗ₜ[k] h))
    (↑u⁻¹ : A ⊗[k] Localization.Away h)
  have hPQ : P * Q = (1 ⊗ₜ h) ^ (m + n) := by
    apply IsLocalization.injective (A ⊗[k] Localization.Away h) hM
    rw [map_mul, ← hP, ← hQ, mul_mul_mul_comm, Units.mul_inv, one_mul, ← map_mul, pow_add]
  have hdvd : (polyEquivTensor k A).symm P ∣ (h ^ (m + n)).map (algebraMap k A) := by
    refine ⟨(polyEquivTensor k A).symm Q, ?_⟩
    rw [← map_mul, hPQ, Algebra.TensorProduct.tmul_pow, one_pow,
      polyEquivTensor_symm_apply_tmul_eq_smul, one_smul]
  obtain ⟨a, g, hg, hPg⟩ := exists_eq_C_mul_map_of_dvd_map (pow_ne_zero _ hh) hdvd
  have hgu : IsUnit (algebraMap k[X] (Localization.Away h) g) := by
    obtain ⟨c, hc⟩ := hg
    refine isUnit_of_mul_isUnit_left (y := algebraMap k[X] (Localization.Away h) c) ?_
    rw [← map_mul, ← hc, map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit h).pow _
  have hhu : IsUnit (algebraMap k[X] (Localization.Away h) h ^ m) :=
    (IsLocalization.Away.algebraMap_isUnit h).pow _
  refine ⟨a, hgu.unit * hhu.unit⁻¹, ?_⟩
  have hP' : P = (a : A) ⊗ₜ g := by
    rw [← (polyEquivTensor k A).apply_symm_apply P, hPg, ← smul_eq_C_mul,
      ← polyEquivTensor_symm_apply_tmul_eq_smul, AlgEquiv.apply_symm_apply]
  have hunit : IsUnit (algebraMap (A ⊗[k] k[X]) (A ⊗[k] Localization.Away h)
      ((1 ⊗ₜ h) ^ m)) := IsLocalization.map_units _ (⟨_, m, rfl⟩ : Submonoid.powers _)
  rw [← hunit.mul_left_inj, hP, hP', halg, Algebra.TensorProduct.tmul_pow, one_pow, halg,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, Units.val_mul, mul_assoc, map_pow,
    IsUnit.val_inv_mul, mul_one, IsUnit.unit_spec]

end TensorProduct
