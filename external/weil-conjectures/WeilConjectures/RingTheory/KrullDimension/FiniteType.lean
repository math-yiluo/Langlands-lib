/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import WeilConjectures.Mathlib.RingTheory.NoetherNormalization
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Dimensions of quotients of finitely generated algebras over a field

- `PrimeSpectrum.topologicalKrullDim_closure_singleton`: the closure of a point `𝔭` of
  `Spec R` has the dimension of `R ⧸ 𝔭`.
- `ringKrullDim_quotient_comap_le`: for a map `φ : A → B` of finitely generated algebras over a
  field and a prime `𝔓` of `B`, `dim A ⧸ φ⁻¹(𝔓) ≤ dim B ⧸ 𝔓`, both dimensions being transcendence
  degrees.
-/

@[expose] public section

/-- The closure of a point `𝔭` of `Spec R` is the image of `Spec (R ⧸ 𝔭)`, so it has the
dimension of `R ⧸ 𝔭`. -/
theorem PrimeSpectrum.topologicalKrullDim_closure_singleton {R : Type*} [CommRing R]
    (p : PrimeSpectrum R) :
    topologicalKrullDim (closure {p}) = ringKrullDim (R ⧸ p.asIdeal) := by
  rw [closure_singleton, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    (isClosedEmbedding_comap_of_surjective _ _
      Ideal.Quotient.mk_surjective).isEmbedding.topologicalKrullDim_eq_range,
    range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]

/-- A nontrivial finitely generated algebra over a field has finite Krull dimension. -/
lemma exists_ringKrullDim_eq_natCast_of_finiteType (k R : Type*) [Field k] [CommRing R]
    [Nontrivial R] [Algebra k R] [Algebra.FiniteType k R] : ∃ n : ℕ, ringKrullDim R = n := by
  have h1 := ringKrullDim_ne_top_of_finiteType k R
  have h2 : ringKrullDim R ≠ ⊥ :=
    ne_bot_of_le_ne_bot WithBot.coe_ne_bot ringKrullDim_nonneg_of_nontrivial
  induction h : ringKrullDim R using WithBot.recBotCoe with
  | bot => exact absurd h h2
  | coe m =>
    induction m using ENat.recTopCoe with
    | top => exact absurd h h1
    | coe m => exact ⟨m, rfl⟩

/-- For a map `φ : A → B` of finitely generated algebras over a field `k` and a prime `𝔓` of `B`,
`dim A ⧸ φ⁻¹(𝔓) ≤ dim B ⧸ 𝔓`: both are finitely generated domains, whose dimensions are their
transcendence degrees over `k`, and `φ` induces an injection `A ⧸ φ⁻¹(𝔓) → B ⧸ 𝔓`. -/
theorem ringKrullDim_quotient_comap_le (k : Type*) {A B : Type*} [Field k] [CommRing A]
    [CommRing B] [Algebra k A] [Algebra k B] [Algebra.FiniteType k A] [Algebra.FiniteType k B]
    (φ : A →ₐ[k] B) (P : Ideal B) [P.IsPrime] :
    ringKrullDim (A ⧸ P.comap φ) ≤ ringKrullDim (B ⧸ P) := by
  have : Algebra.FiniteType k (A ⧸ P.comap φ) :=
    .of_surjective (Ideal.Quotient.mkₐ k _) Ideal.Quotient.mk_surjective
  have : Algebra.FiniteType k (B ⧸ P) :=
    .of_surjective (Ideal.Quotient.mkₐ k _) Ideal.Quotient.mk_surjective
  obtain ⟨n, hn⟩ := exists_ringKrullDim_eq_natCast_of_finiteType k (A ⧸ P.comap φ)
  obtain ⟨m, hm⟩ := exists_ringKrullDim_eq_natCast_of_finiteType k (B ⧸ P)
  have h := lift_trdeg_le_of_injective (Ideal.quotientMapₐ P φ le_rfl)
    Ideal.quotientMap_injective
  rw [Algebra.trdeg_eq_of_ringKrullDim_eq k _ hn, Algebra.trdeg_eq_of_ringKrullDim_eq k _ hm,
    Cardinal.lift_natCast, Cardinal.lift_natCast, Nat.cast_le] at h
  rw [hn, hm]
  exact_mod_cast h
