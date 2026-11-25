/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Krull dimension of finitely generated algebras and of quotients

## Main results

- `ringKrullDim_ne_top_of_finiteType`: a finitely generated algebra over a field has finite Krull
  dimension.
- `Ideal.eq_of_le_of_ringKrullDim_quotient_eq`: if `I ≤ J` with `I` prime and `R ⧸ I` of finite
  dimension, then `R ⧸ J` has the dimension of `R ⧸ I` only if `J = I`: a proper closed subset
  of an irreducible variety has smaller dimension.
- `ringKrullDim_quotient_lt_of_ne_bot`: in a finite-dimensional domain the quotient by a nonzero
  ideal has strictly smaller dimension.
- `ringKrullDim_quotient_lt_of_irreducibleSpace`: a proper closed subset of an irreducible affine
  variety has strictly smaller dimension.
- `MvPolynomial.height_eq_of_isMaximal`: every maximal ideal of `k[X₁, …, Xₙ]` has height `n`.

## Blueprint

- `lem-wf-affine-dimension-drop`: proper closed subsets have strictly smaller dimension.
-/

@[expose] public section

/-- A finitely generated algebra over a field has finite Krull dimension. -/
theorem ringKrullDim_ne_top_of_finiteType (k A : Type*) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] : ringKrullDim A ≠ ⊤ := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 ‹Algebra.FiniteType k A›
  refine ne_top_of_le_ne_top ?_ (ringKrullDim_le_of_surjective f.toRingHom hf)
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field, zero_add]
  intro h
  cases h

/-- A proper closed subset of an irreducible closed subset of `Spec R` of finite dimension has
strictly smaller dimension: if `I ≤ J` with `I` prime, `R ⧸ I` finite-dimensional and
`dim (R ⧸ J) = dim (R ⧸ I)`, then `J = I`. -/
theorem Ideal.eq_of_le_of_ringKrullDim_quotient_eq {R : Type*} [CommRing R] {I J : Ideal R}
    [hI : I.IsPrime] (hIJ : I ≤ J) (hfin : ringKrullDim (R ⧸ I) ≠ ⊤)
    (h : ringKrullDim (R ⧸ J) = ringKrullDim (R ⧸ I)) : J = I := by
  by_contra hne
  have hlt : I < J := lt_of_le_of_ne hIJ (Ne.symm hne)
  rw [ringKrullDim_quotient, ringKrullDim_quotient] at h
  rw [ringKrullDim_quotient] at hfin
  have hbot : Order.krullDim (PrimeSpectrum.zeroLocus (R := R) I) ≠ ⊥ :=
    Order.krullDim_ne_bot_iff.2 ⟨⟨⟨I, hI⟩, fun _ h ↦ h⟩⟩
  obtain ⟨d, hd⟩ : ∃ d : ℕ, Order.krullDim (PrimeSpectrum.zeroLocus (R := R) I) = d := by
    rcases hk : Order.krullDim (PrimeSpectrum.zeroLocus (R := R) I) with _ | _ | d
    · exact absurd hk hbot
    · exact absurd hk hfin
    · exact ⟨d, rfl⟩
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.1 (h.trans hd).ge
  let f : PrimeSpectrum.zeroLocus (R := R) J → PrimeSpectrum.zeroLocus (R := R) I :=
    fun x ↦ ⟨x.1, (PrimeSpectrum.zeroLocus_anti_mono hIJ) x.2⟩
  have hf : StrictMono f := fun _ _ h ↦ h
  let l' := (l.map f hf).cons ⟨⟨I, hI⟩, fun _ h ↦ h⟩ (by
    change I < (l.head : PrimeSpectrum R).asIdeal
    exact lt_of_lt_of_le hlt l.head.2)
  have := Order.LTSeries.length_le_krullDim l'
  rw [hd, RelSeries.cons_length, LTSeries.map_length, hl] at this
  exact absurd (WithBot.coe_le_coe.1 this) (by norm_cast; omega)

/-- In a domain `R` of finite Krull dimension, the quotient by a nonzero ideal `I` has strictly
smaller dimension: a prime chain of `R ⧸ I` consists of nonzero primes of `R`, and prepending the
prime `(0)` lengthens it. -/
theorem ringKrullDim_quotient_lt_of_ne_bot {R : Type*} [CommRing R] [IsDomain R]
    (hR : ringKrullDim R ≠ ⊤) {I : Ideal R} (hI : I ≠ ⊥) :
    ringKrullDim (R ⧸ I) < ringKrullDim R := by
  have e := ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot R)
  rw [← e] at hR ⊢
  refine lt_of_le_of_ne (ringKrullDim_le_of_surjective _
    (Ideal.Quotient.factor_surjective (bot_le (a := I)))) fun h ↦ hI ?_
  exact Ideal.eq_of_le_of_ringKrullDim_quotient_eq (hIJ := bot_le) (hI := Ideal.isPrime_bot) hR h

/-- Blueprint `lem-wf-affine-dimension-drop`: let `A` be the coordinate algebra of an irreducible
affine variety over a field `k`, i.e. a reduced finitely generated `k`-algebra with irreducible
spectrum. Then `A` is a domain (`PrimeSpectrum.isDomain_of_irreducibleSpace`), and a proper closed
subset `V(I)`, i.e. one with `I ≠ 0`, has strictly smaller dimension: `dim (A ⧸ I) < dim A`.

The dimension of `A` is finite (`ringKrullDim_ne_top_of_finiteType`), and the strict drop is
`ringKrullDim_quotient_lt_of_ne_bot`. -/
theorem ringKrullDim_quotient_lt_of_irreducibleSpace (k A : Type*) [Field k] [CommRing A]
    [IsReduced A] [IrreducibleSpace (PrimeSpectrum A)] [Algebra k A] [Algebra.FiniteType k A]
    {I : Ideal A} (hI : I ≠ ⊥) : ringKrullDim (A ⧸ I) < ringKrullDim A := by
  have := PrimeSpectrum.isDomain_of_irreducibleSpace A
  exact ringKrullDim_quotient_lt_of_ne_bot (ringKrullDim_ne_top_of_finiteType k A) hI

open Ideal in
/-- Every maximal ideal of the polynomial ring `k[X₁, …, Xₙ]` over a field `k` has height `n`:
writing `k[X₁, …, Xₙ₊₁] = k[X₁, …, Xₙ][X]`, a maximal ideal lies over a maximal ideal of
`k[X₁, …, Xₙ]` since this ring is Jacobson, and its height is one more than that one. -/
theorem MvPolynomial.height_eq_of_isMaximal {k : Type*} [Field k] :
    ∀ (n : ℕ) (M : Ideal (MvPolynomial (Fin n) k)) [M.IsMaximal], M.height = n
  | 0, M, _ => by
    have h := height_le_ringKrullDim_of_ne_top (IsMaximal.ne_top ‹M.IsMaximal›)
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field] at h
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.cast_zero, add_zero] at h
    exact_mod_cast le_antisymm (by exact_mod_cast h) zero_le
  | n + 1, M, _ => by
    let e := MvPolynomial.finSuccEquiv k n
    let M' : Ideal (Polynomial (MvPolynomial (Fin n) k)) := M.map e.toRingEquiv
    have : M'.IsMaximal := map_isMaximal_of_equiv e.toRingEquiv
    have hM : M.height = M'.height := (e.toRingEquiv.height_map M).symm
    let p := M'.comap Polynomial.C
    have : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing M'
    have : M'.LiesOver p := ⟨rfl⟩
    rw [hM, Polynomial.height_eq_height_add_one p M', MvPolynomial.height_eq_of_isMaximal n p]
    norm_cast

/-- For a field `k` and a maximal ideal `M` of `P = k[X₁, …, Xₙ]`, the localization `P_M` has
Krull dimension `n` (Stacks `00OP`): its dimension is the height of `M`, which is `n`.
(blueprint: `lem-weil-pbc-polynomial-ring-maximal-localization-dimension`) -/
theorem MvPolynomial.ringKrullDim_localization_atPrime_of_isMaximal {k : Type*} [Field k]
    (n : ℕ) (M : Ideal (MvPolynomial (Fin n) k)) [M.IsMaximal] :
    ringKrullDim (Localization.AtPrime M) = n := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height M, MvPolynomial.height_eq_of_isMaximal n M]
  rfl

