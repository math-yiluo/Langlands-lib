/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.RingTheory.SingularIdeal
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section
universe u v w z s
namespace Algebra

/-- Singular-ideal comparison for a commuting lifting diagram with smoothness transfer.
Source: Stacks Project, Lemma 07F0, the final verification using 07CP(c).
(blueprint: new-popescu-lifting-witness-control).

Proof: Put J = δ(H_D)Λ. Lift τ(x), for x in H_C, to y in Λ. For any prime p
containing J, the hypothesis on L makes p descend to Λ/L. Pull this prime back
along ψ to D/I. Its inverse image in D contains H_D by the commuting square,
so it is nonsmooth. Smoothness transfer implies that its inverse image in C
is nonsmooth, hence contains H_C. Thus ψ(c(x)) belongs to p/L. The second
commuting square and the reduction equation identify this element with y mod L,
so y belongs to p. Intersecting all such primes gives y in √J, and therefore
τ(x) in the quotient image of √J. The ideal-map adjunction finishes the proof.
-/
theorem popescu_lifting_witness_control
    (R : Type u) (S : Type s) (C : Type z) (D : Type v) (Λ : Type w)
    [CommRing R] [CommRing S] [CommRing C] [CommRing D] [CommRing Λ]
    [Algebra R D] [Algebra S C]
    (I : Ideal D) (K L : Ideal Λ) (δ : D →+* Λ)
    (ψ : (D ⧸ I) →+* (Λ ⧸ L)) (red : (Λ ⧸ K) →+* (Λ ⧸ L))
    (c : C →+* (D ⧸ I)) (τ : C →+* (Λ ⧸ K))
    (hψ : ψ.comp (Ideal.Quotient.mk I) = (Ideal.Quotient.mk L).comp δ)
    (hred : red.comp (Ideal.Quotient.mk K) = Ideal.Quotient.mk L)
    (hsquare : ψ.comp c = red.comp τ)
    (hL : L ≤ (Ideal.map δ (singularIdeal R D)).radical)
    (hover : ∀ q : PrimeSpectrum (D ⧸ I),
      IsSmoothAtPrime S (PrimeSpectrum.comap c q) →
        IsSmoothAtPrime R (PrimeSpectrum.comap (Ideal.Quotient.mk I) q)) :
    Ideal.map τ (singularIdeal S C) ≤
      Ideal.map (Ideal.Quotient.mk K) (Ideal.map δ (singularIdeal R D)).radical := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro x hx
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (I := K) (τ x)
  apply (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mpr
  refine ⟨y, ?_, hy⟩
  rw [Ideal.radical_eq_sInf]
  apply Ideal.mem_sInf.mpr
  rintro p ⟨hp, hprime⟩
  let : p.IsPrime := hprime
  have hLp : L ≤ p := hL.trans (hprime.radical_le_iff.mpr hp)
  have hker : RingHom.ker (Ideal.Quotient.mk L) ≤ p := by
    simpa only [Ideal.mk_ker] using hLp
  let pbar : PrimeSpectrum (Λ ⧸ L) :=
    ⟨Ideal.map (Ideal.Quotient.mk L) p,
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker⟩
  have hcomap : Ideal.comap (Ideal.Quotient.mk L) pbar.asIdeal = p := by
    change Ideal.comap (Ideal.Quotient.mk L) (Ideal.map (Ideal.Quotient.mk L) p) = p
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hker]
  let q := PrimeSpectrum.comap ψ pbar
  have hD : singularIdeal R D ≤
      (PrimeSpectrum.comap (Ideal.Quotient.mk I) q).asIdeal := by
    intro d hd
    change ψ (Ideal.Quotient.mk I d) ∈ pbar.asIdeal
    change (ψ.comp (Ideal.Quotient.mk I)) d ∈ pbar.asIdeal
    rw [hψ]
    change δ d ∈ Ideal.comap (Ideal.Quotient.mk L) pbar.asIdeal
    rw [hcomap]
    exact hp (Ideal.mem_map_of_mem δ hd)
  have hnD : ¬ IsSmoothAtPrime R (PrimeSpectrum.comap (Ideal.Quotient.mk I) q) := by
    have hz : PrimeSpectrum.comap (Ideal.Quotient.mk I) q ∈
        PrimeSpectrum.zeroLocus (singularIdeal R D : Set D) := hD
    rwa [(singularIdeal_zeroLocus R D).1] at hz
  have hnC : ¬ IsSmoothAtPrime S (PrimeSpectrum.comap c q) :=
    fun h ↦ hnD (hover q h)
  have hC : singularIdeal S C ≤ (PrimeSpectrum.comap c q).asIdeal := by
    have hz : PrimeSpectrum.comap c q ∈
        PrimeSpectrum.zeroLocus (singularIdeal S C : Set C) := by
      rwa [(singularIdeal_zeroLocus S C).1]
    exact hz
  have hm : ψ (c x) ∈ pbar.asIdeal := hC hx
  have he : ψ (c x) = Ideal.Quotient.mk L y := by
    calc
      ψ (c x) = red (τ x) := DFunLike.congr_fun hsquare x
      _ = red (Ideal.Quotient.mk K y) := congrArg red hy.symm
      _ = Ideal.Quotient.mk L y := DFunLike.congr_fun hred y
  rw [he] at hm
  change y ∈ Ideal.comap (Ideal.Quotient.mk L) pbar.asIdeal at hm
  rwa [hcomap] at hm

end Algebra
