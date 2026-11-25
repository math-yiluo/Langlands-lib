/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Derivation.Basic

import WeilConjectures.RingTheory.FiniteSubalgebraFractionField
import WeilConjectures.RingTheory.FormalFiberDerivationExtension
import WeilConjectures.RingTheory.Derivation.DetectNonPthPower
import WeilConjectures.RingTheory.RegularRingNormal
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.RegularLocalLocalization
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.Algebra.CharP.Reduced
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.RegularLocalRing.Polynomial

/-!
# Degree-p formal-fibre derivation component

Source: Stacks Project, More on Algebra, Tag 07PR.
-/

@[expose] public section

universe u

namespace MvPowerSeries

private theorem unit_derivative (F : Type u) [Field F] (p : ℕ) [CharP F p]
    (R : Type u) [CommRing R] (i : F →+* R) (D : Derivation ℤ R R)
    (a c s d : F) (hc : c = s ^ p * a) (hd : D (i c) = i d) (hne : d ≠ 0) :
    IsUnit (D (i a)) := by
  have hi : IsUnit (i d) := (isUnit_iff_ne_zero.mpr hne).map i
  have hpzero : (p : R) = 0 := by
    rw [← map_natCast i, CharP.cast_eq_zero F p, map_zero]
  have hsp : D (i s ^ p) = 0 := by
    rw [D.leibniz_pow]
    simp only [nsmul_eq_mul, hpzero, zero_mul]
  have hprod : i d = i s ^ p * D (i a) := by
    rw [← hd, hc, map_mul, map_pow, D.leibniz, hsp]
    simp only [smul_eq_mul, mul_zero, add_zero]
  apply isUnit_of_mul_isUnit_right (x := i s ^ p)
  rwa [← hprod]

private theorem field_not_cohen (k : Type u) [Field k] (p : ℕ) :
    ¬ IsCohenRing p k := by
  rintro ⟨_, hdomain, hdvr, _, _⟩
  let := hdomain
  let := hdvr
  exact IsDiscreteValuationRing.not_isField k (Field.toIsField k)

private theorem powerSeries_field_regular_complete (k : Type u) [Field k] (n : ℕ) :
    ∃ _ : IsLocalRing (MvPowerSeries (Fin n) k),
      IsAdicComplete (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) k))
        (MvPowerSeries (Fin n) k) ∧ IsRegularLocalRing (MvPowerSeries (Fin n) k) := by
  obtain hbase := power_series_field_cohen_regular_complete (Λ := k) n
    (Or.inl (Field.toIsField k))
  rcases hbase with ⟨_, _, _, hlocal, _, _, _, hcomplete, hregular, _⟩ | ⟨p, hp, _⟩
  · exact ⟨hlocal, hcomplete, hregular⟩
  · exact False.elim (field_not_cohen k p hp)

private theorem exists_derivation_isUnit_of_finite_model
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (q : Ideal A) [q.IsPrime] (M : Type u) [Field M]
    [Algebra (⊥ : Ideal A).ResidueField M] [Algebra A M]
    [IsScalarTower A (⊥ : Ideal A).ResidueField M]
    [Module.Finite (⊥ : Ideal A).ResidueField M]
    [IsPurelyInseparable (⊥ : Ideal A).ResidueField M]
    (B : Subalgebra A M) [Module.Finite A B] [IsFractionRing B M]
    (p : ℕ) [Fact p.Prime] [CharP M p] [CharP B p]
    (R₀ : Type u) [CommRing R₀] [IsNoetherianRing R₀] [IsLocalRing R₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal R₀) R₀]
    [Algebra R₀ B] [Algebra.FiniteType R₀ B]
    (a : M) (hnot : ¬ ∃ x : M, x ^ p = a)
    (hfrac : ∀ x : M, ∃ b s : B, (s : M) ≠ 0 ∧ x = (b : M) / (s : M)) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)
    let R := TensorProduct (⊥ : Ideal A).ResidueField M ((⊥ : Ideal A).Fiber C)
    ∃ E : Derivation ℤ R R, IsUnit (E (Algebra.TensorProduct.includeLeftRingHom a)) := by
  intro C R
  obtain ⟨b, s, hs, hab⟩ := hfrac a
  let c : B := s ^ (p - 1) * b
  have hc : (c : M) = (s : M) ^ p * a := by
    rw [hab]
    dsimp [c]
    field_simp
    have hp : p = (p - 1) + 1 := (Nat.sub_add_cancel
      (Nat.Prime.one_lt (Fact.out : p.Prime)).le).symm
    conv_rhs => rw [hp, pow_succ]
    ring
  have hcn : ¬ ∃ x : M, x ^ p = algebraMap B M c := by
    rintro ⟨x, hx⟩
    apply hnot
    refine ⟨x / (s : M), ?_⟩
    rw [div_pow, hx]
    change (c : M) / (s : M) ^ p = a
    rw [hc, mul_div_cancel_left₀ _ (pow_ne_zero _ hs)]
  obtain ⟨D, hD⟩ := Derivation.exists_apply_ne_zero_of_not_pth_power
    (p := p) (B := B) (M := M) (R₀ := R₀) c hcn
  obtain ⟨E, hE⟩ := Derivation.exists_formalFiber_extension
    (A := A) (q := q) (M := M) (B := B) D
  exact ⟨E, unit_derivative M p R Algebra.TensorProduct.includeLeftRingHom E
    a c s (D c) hc (hE c) (fun h ↦ hD (Subtype.ext h))⟩

private theorem exists_derivation_isUnit_of_not_pth_power
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (n m : ℕ)
    (q : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))) [q.IsPrime]
    (M : Type u) [Field M]
    [Algebra ((⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).ResidueField) M]
    [Module.Finite
      ((⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).ResidueField) M]
    [IsPurelyInseparable
      ((⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).ResidueField) M]
    (a : M) (hnot : ¬ ∃ x : M, x ^ p = a) :
    let A := MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)
    let R := TensorProduct (⊥ : Ideal A).ResidueField M ((⊥ : Ideal A).Fiber C)
    ∃ D : Derivation ℤ R R, IsUnit (D (Algebra.TensorProduct.includeLeftRingHom a)) := by
  classical
  let A := MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)
  let K := (⊥ : Ideal A).ResidueField
  let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
    (Localization.AtPrime q)
  let R := TensorProduct K M ((⊥ : Ideal A).Fiber C)
  change ∃ D : Derivation ℤ R R,
    IsUnit (D (Algebra.TensorProduct.includeLeftRingHom a))
  let : Algebra A M := ((algebraMap K M).comp (algebraMap A K)).toAlgebra
  let : IsScalarTower A K M := IsScalarTower.of_algebraMap_eq fun x ↦ rfl
  let : IsDomain (MvPowerSeries (Fin n) k) := NoZeroDivisors.to_isDomain _
  let : IsLocalization.AtPrime K (⊥ : Ideal A) := by
    simpa only [IsLocalization.AtPrime, Ideal.primeCompl_bot] using
      (inferInstance : IsFractionRing A K)
  let : CharP (MvPowerSeries (Fin n) k) p :=
    charP_of_injective_ringHom (MvPowerSeries.C_injective (σ := Fin n)) p
  let : CharP A p := inferInstance
  let : CharP K p := IsFractionRing.charP_of_isFractionRing A p
  let : CharP M p := charP_of_injective_ringHom (algebraMap K M).injective p
  obtain ⟨_, B, hB, hfrac⟩ :=
    MvPolynomial.exists_finite_subalgebra_fraction_field k p
      (Nat.Prime.pos (Fact.out : p.Prime)) n m K M
  let : Module.Finite A B := hB
  let : IsFractionRing B M := IsFractionRing.of_field B M fun x ↦ by
    obtain ⟨b, s, _, hs⟩ := hfrac x
    exact ⟨b, s, hs⟩
  let : CharP B p := (algebraMap B M).charP Subtype.val_injective p
  obtain ⟨hlocal, hcomplete, hregular⟩ := powerSeries_field_regular_complete k n
  let := hlocal
  let := hcomplete
  let := hregular
  let : IsRegularRing (MvPowerSeries (Fin n) k) :=
    (IsRegularLocalRing.localization_at_prime_and_isRegularRing
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) k))).2
  let : IsRegularRing A := inferInstance
  let : IsIntegrallyClosed A := IsIntegrallyClosed.of_localization_maximal
    fun r _ _ ↦ (IsRegularRing.isNormalRing A r).2
  let : Algebra (MvPowerSeries (Fin n) k) B :=
    ((algebraMap A B).comp (algebraMap (MvPowerSeries (Fin n) k) A)).toAlgebra
  let : IsScalarTower (MvPowerSeries (Fin n) k) A B :=
    IsScalarTower.of_algebraMap_eq fun x ↦ rfl
  let : Algebra.FiniteType (MvPowerSeries (Fin n) k) B :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType
      (MvPowerSeries (Fin n) k) A) (inferInstance : Algebra.FiniteType A B)
  exact exists_derivation_isUnit_of_finite_model A q M B p
    (MvPowerSeries (Fin n) k) a hnot hfrac


set_option backward.isDefEq.respectTransparency false in
/-- A derivation detects the specified degree-p coefficient in the extended formal fibre.
Source: Stacks Project, More on Algebra, Tags 07PR, 07PH and 07PE.
(blueprint: new-lem-weil-pbc-degree-p-derivation-component)

Proof: The element a is not a pth power in M. Otherwise injectivity of Frobenius
in L implies z belongs to M, contradicting [L:M] = p > 1. Choose a finite
A-subalgebra B with fraction field M. Write a = b/s, with s nonzero in B,
and set c = s^(p-1)b, so c = s^p a in M and c is not a pth power in M.
The power-series base is Noetherian complete local and B is finite type over it.
Tag 07PH supplies an absolute derivation of B nonzero on c. Normality of A and
pure inseparability give a unique prime r over q. Finite-extension completion
and tensor associativity identify R with completion(B_r) tensor_B M.
Extend the derivation through B_r, its completion, and this localization by
Tag 07PE. Its value on c is the image of a nonzero element of M, hence is a unit.
Characteristic p implies D(s^p) = 0. Thus D(i(a)) = i(s)^(-p) D(i(c)),
which is a unit. Transport the derivation along the ring equivalence with R.
If R is zero, zero is a unit, and the same identities still apply. -/
theorem exists_derivation_isUnit_tmul_formalFiber
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (n m : ℕ)
    (q : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))) [q.IsPrime]
    (L : Type u) [Field L]
    [Algebra ((⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).ResidueField) L]
    [Module.Finite
      ((⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).ResidueField) L]
    [IsPurelyInseparable
      ((⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).ResidueField) L]
    (M : IntermediateField
      ((⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).ResidueField) L)
    [Module.Finite
      ((⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).ResidueField) M]
    [IsPurelyInseparable
      ((⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).ResidueField) M]
    (z : L) (hz : IntermediateField.adjoin M ({z} : Set L) = ⊤)
    (a : M) (ha : z ^ p = (a : L)) (hdeg : Module.finrank M L = p) :
    let A := MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)
    let K := (⊥ : Ideal A).ResidueField
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)
    let R := TensorProduct K M ((⊥ : Ideal A).Fiber C)
    letI : CommSemiring R := (inferInstance : CommRing R).toCommSemiring
    letI : AddCommMonoid R := (inferInstance : CommRing R).toAddCommGroup.toAddCommMonoid
    ∃ D : Derivation ℤ R R, IsUnit (D (Algebra.TensorProduct.includeLeftRingHom a)) := by
  classical
  let A := MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)
  let K := (⊥ : Ideal A).ResidueField
  let : IsDomain (MvPowerSeries (Fin n) k) := NoZeroDivisors.to_isDomain _
  let : CharP (MvPowerSeries (Fin n) k) p :=
    charP_of_injective_ringHom (MvPowerSeries.C_injective (σ := Fin n)) p
  let : CharP A p := inferInstance
  let : CharP K p := IsFractionRing.charP_of_isFractionRing A p
  let : CharP L p := charP_of_injective_ringHom (algebraMap K L).injective p
  have hnot : ¬ ∃ x : M, x ^ p = a := by
    rintro ⟨x, hx⟩
    have hxz : (x : L) = z := by
      apply frobenius_inj L p
      change (x : L) ^ p = z ^ p
      rw [ha, ← hx]
      rfl
    have hbot : (⊥ : IntermediateField M L) = ⊤ := by
      rw [← hz]
      symm
      apply IntermediateField.adjoin_simple_eq_bot_iff.mpr
      exact IntermediateField.mem_bot.mpr ⟨x, hxz⟩
    have hone : Module.finrank M L = 1 :=
      IntermediateField.bot_eq_top_iff_finrank_eq_one.mp hbot
    exact (Nat.Prime.ne_one (Fact.out : p.Prime)) (hdeg.symm.trans hone)
  exact exists_derivation_isUnit_of_not_pth_power k p n m q M a hnot

end MvPowerSeries
