/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import WeilConjectures.RingTheory.KaehlerDifferentialZeroIffPow
import Mathlib.LinearAlgebra.Dual.Lemmas
import WeilConjectures.RingTheory.Derivation.FiniteCoefficientPreparation
import Mathlib.RingTheory.Localization.Integer

/-!
# Detecting non-pth-powers by absolute derivations

Source: Stacks Project, More on Algebra, Lemma 07PH (`lemma-find-D`)
(blueprint: lem-weil-pbc-derivation-nonzero-on-non-pth-power).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Derivation

/-- A fraction-field derivation detecting `f` can be produced from the
  normalization and differential argument in the blueprint.  This is the
  field-valued part of that argument; the remaining denominator-clearing
  step is isolated in `exists_domain_derivation_of_fraction_derivation`.
(blueprint: lem-weil-pbc-fraction-field-derivation-nonzero)
Proof: carry out Steps 1--5 of the parent Lemma 07PH proof (complete-local
quotient, power-series normalization, Noether normalization, and the
Kähler-differential/p-basis argument) to obtain a derivation of the fraction
field nonzero on the chosen element. -/
theorem exists_fraction_field_derivation_of_not_pth_power
    (p : ℕ) [Fact p.Prime]
    (B : Type u) [CommRing B] [IsDomain B] [CharP B p]
    (M : Type v) [Field M] [Algebra B M] [IsFractionRing B M]
    (R₀ : Type w) [CommRing R₀] [IsNoetherianRing R₀] [IsLocalRing R₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal R₀) R₀]
    [Algebra R₀ B] [Algebra.FiniteType R₀ B]
    (f : B) (hf : ¬ ∃ x : M, x ^ p = algebraMap B M f) :
    ∃ D : Derivation ℤ M M, D (algebraMap B M f) ≠ 0 := by
  let : CharP M p := charP_of_injective_ringHom (IsFractionRing.injective B M) p
  let : Algebra (ZMod p) M := ZMod.algebra M p
  have hdiff : KaehlerDifferential.D (ZMod p) M (algebraMap B M f) ≠ 0 := by
    intro hz
    have hp := (KaehlerDifferential.D_eq_zero_iff_exists_pow_of_perfectField p
      (ZMod p) M (algebraMap B M f)).mp hz
    rcases hp with ⟨x, hx⟩
    apply hf
    exact ⟨x, hx.symm⟩
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero M hdiff
  exact ⟨(φ.compDer (KaehlerDifferential.D (ZMod p) M)).restrictScalars ℤ, hφ⟩

private theorem clear_denominators
    {B : Type u} [CommRing B] [IsDomain B]
    {M : Type v} [Field M] [Algebra B M] [IsFractionRing B M]
    (A : Subring B) (hfinite : Algebra.FiniteType A B)
    (δ : Derivation ℤ M M) (hbase : ∀ a : A, δ (algebraMap B M a) = 0) :
    ∃ c : B, c ≠ 0 ∧ ∀ x : B,
      ∃ y : B, algebraMap B M y = algebraMap B M c * δ (algebraMap B M x) := by
  classical
  obtain ⟨s, hs⟩ := hfinite.out
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors B) s
    (fun x : B ↦ δ (algebraMap B M x))
  let Δ : Derivation ℤ M M := algebraMap B M (c : B) • δ
  refine ⟨c, nonZeroDivisors.ne_zero c.property, ?_⟩
  intro x
  have hx : x ∈ Algebra.adjoin A (s : Set B) := by rw [hs]; trivial
  change ∃ y : B, algebraMap B M y = Δ (algebraMap B M x)
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨y, hy⟩ := hc x hx
    exact ⟨y, by simpa only [Δ, Derivation.smul_apply, smul_eq_mul, Algebra.smul_def] using hy⟩
  | algebraMap a =>
    refine ⟨0, ?_⟩
    rw [map_zero]
    change 0 = algebraMap B M (c : B) * δ (algebraMap B M (a : B))
    rw [hbase a, mul_zero]
  | add x y _ _ hx hy =>
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hy
    exact ⟨x' + y', by simp only [map_add, hx', hy']⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hy
    refine ⟨x * y' + y * x', ?_⟩
    simp only [map_add, map_mul, hx', hy', Δ.leibniz, smul_eq_mul]

/-- Denominator clearing for a finite type domain.
(blueprint: lem-weil-pbc-domain-derivation-from-fraction)
Proof: multiply the fraction-field derivation by the product of denominators
of its values on finite module generators, as in Step 6 of Lemma 07PH. -/
theorem exists_domain_derivation_of_fraction_derivation
    (p : ℕ) [Fact p.Prime]
    (B : Type u) [CommRing B] [IsDomain B] [CharP B p]
    (M : Type v) [Field M] [Algebra B M] [IsFractionRing B M]
    (R₀ : Type w) [CommRing R₀] [IsNoetherianRing R₀] [IsLocalRing R₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal R₀) R₀]
    [Algebra R₀ B] [Algebra.FiniteType R₀ B]
    (f : B) (D : Derivation ℤ M M) (hD : D (algebraMap B M f) ≠ 0) :
    ∃ D' : Derivation ℤ B B, D' f ≠ 0 := by
  classical
  obtain ⟨A, hfinite, δ, hbase, hδ⟩ :=
    exists_finite_coefficient_derivation p B M R₀ f D hD
  obtain ⟨c, hc, H⟩ := clear_denominators A hfinite δ hbase
  let Δ : Derivation ℤ M M := algebraMap B M c • δ
  choose d hd using H
  have hdd (x : B) : algebraMap B M (d x) = Δ (algebraMap B M x) := hd x
  let D' : Derivation ℤ B B :=
    { toFun := d
      map_add' := by
        intro x y
        apply IsFractionRing.injective B M
        calc
          algebraMap B M (d (x + y)) = Δ (algebraMap B M (x + y)) := hdd _
          _ = Δ (algebraMap B M x + algebraMap B M y) := by rw [map_add]
          _ = Δ (algebraMap B M x) + Δ (algebraMap B M y) := Δ.map_add _ _
          _ = algebraMap B M (d x + d y) := by rw [← hdd, ← hdd, map_add]
      map_smul' := by
        intro z x
        apply IsFractionRing.injective B M
        calc
          algebraMap B M (d (z • x)) = Δ (algebraMap B M (z • x)) := hdd _
          _ = Δ ((algebraMap ℤ M) z * algebraMap B M x) := by
            simp [Algebra.smul_def]
          _ = (algebraMap ℤ M) z * Δ (algebraMap B M x) := by
            convert Δ.map_smul z (algebraMap B M x) using 1 <;> simp [Algebra.smul_def]
          _ = algebraMap B M (z • d x) := by simp [Algebra.smul_def, hdd]
      map_one_eq_zero' := by
        apply IsFractionRing.injective B M
        change algebraMap B M (d 1) = algebraMap B M 0
        rw [hdd, map_one, Δ.map_one_eq_zero, map_zero]
      leibniz' := by
        intro x y
        apply IsFractionRing.injective B M
        change algebraMap B M (d (x * y)) = algebraMap B M (x * d y + y * d x)
        calc
          algebraMap B M (d (x * y)) = Δ (algebraMap B M (x * y)) := hdd _
          _ = Δ (algebraMap B M x * algebraMap B M y) := by rw [map_mul]
          _ = algebraMap B M x * Δ (algebraMap B M y) +
              algebraMap B M y * Δ (algebraMap B M x) := Δ.leibniz _ _
          _ = algebraMap B M (x * d y + y * d x) := by simp [hdd, map_add, map_mul] }
  refine ⟨D', ?_⟩
  intro hz
  have hd0 : d f = 0 := hz
  have hΔ0 : Δ (algebraMap B M f) = 0 := by rw [← hdd, hd0, map_zero]
  have hcM : algebraMap B M c ≠ 0 := fun h ↦ hc
    ((IsFractionRing.injective B M) (h.trans (map_zero _).symm))
  exact (mul_ne_zero hcM hδ) hΔ0

/-- Stacks Project, More on Algebra, Lemma 07PH (`lemma-find-D`).
(blueprint: lem-weil-pbc-derivation-nonzero-on-non-pth-power)
A non-pth-power in the fraction field of a characteristic-p domain of finite type over a
Noetherian complete local ring is detected by an absolute derivation of the domain.

Proof:
1. Replace the complete local base by its image in `B`, a complete Noetherian local domain
   by lem-weil-pbc-complete-local-quotient. By
   lem-weil-pbc-complete-local-domain-finite-over-regular it is finite over a power series
   ring over a field. The Cohen-ring alternative is excluded by characteristic `p`.
   Thus `B` is finite type over this power series ring.
2. By lem-weil-pbc-noether-normalization-over-domain, find a polynomial ring `A` over that
   base and `A ⊆ B' ⊆ B`, with `B'` finite over `A` and `B'_g = B_g` for nonzero `g`.
   The fraction field of `B'` is `M`. Choose `N` so that `f' = g^(p*N)*f` belongs to `B'`;
   it is still not a pth power, since a pth root would give one for `f` after division by
   `g^N`.
3. It suffices to find a derivation `D'` of `B'` nonzero on `f'`: by
   lem-weil-pbc-derivation-extends-finite-type-extension a multiple `g^r*D'` extends to `B`.
   Its value on `f'` is nonzero. The Leibniz rule and characteristic `p` imply
   `D(g^(p*N)) = 0`, so `D(f') = g^(p*N)*D(f)` and `D(f)` is nonzero.
4. The extension of fraction fields `M/K`, for `K = Frac(A)`, is finite, by integrality
   (lem-weil-pbc-finite-algebra-is-integral) and the finite module generators of `B'`.
   By lem-weil-pbc-differential-zero-iff-pth-power, `df'` is nonzero over the prime field.
   Choose a p-basis of the coefficient field (lem-weil-pbc-p-basis-exists). The subfields
   of lem-weil-pbc-power-series-ring-subfields and both parts of
   lem-weil-pbc-intersection-subfields-differentials give a finite-index coefficient
   subfield and `A' ⊆ A`, with `A` finite over `A'`, such that `df'` remains nonzero over
   a subfield containing `K' = Frac(A')`.
5. By lem-weil-pbc-vector-space-dual-separates, a linear functional on these differentials
   is nonzero on `df'`. The universal property of def-weil-pbc-kahler-differentials gives
   a derivation of `M` nonzero on `f'` and vanishing on `A'`.
6. By lem-weil-pbc-finite-module-over-finite-algebra, `B'` is finite over `A'`. Multiply
   the derivation by the product of denominators of its values on finitely many module
   generators. It then maps `B'` into `B'` and is still nonzero on `f'` because the
   product of denominators is nonzero in the domain. Step 3 completes the argument. -/
theorem exists_apply_ne_zero_of_not_pth_power
    (p : ℕ) [Fact p.Prime]
    (B : Type u) [CommRing B] [IsDomain B] [CharP B p]
    (M : Type v) [Field M] [Algebra B M] [IsFractionRing B M]
    (R₀ : Type w) [CommRing R₀] [IsNoetherianRing R₀] [IsLocalRing R₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal R₀) R₀]
    [Algebra R₀ B] [Algebra.FiniteType R₀ B]
    (f : B) (hf : ¬ ∃ x : M, x ^ p = algebraMap B M f) :
    ∃ D : Derivation ℤ B B, D f ≠ 0 := by
  obtain ⟨D, hD⟩ := exists_fraction_field_derivation_of_not_pth_power
    p B M R₀ f hf
  exact exists_domain_derivation_of_fraction_derivation p B M R₀ f D hD

end Derivation
