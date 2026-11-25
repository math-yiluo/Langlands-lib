/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Rank-one propagation for a Zariski pair

Source: literature/stacks-project/more-algebra.tex, Lemma Tag 0ELZ
(blueprint: lem-weil-pbc-zariski-pair-rank-one-propagation)
-/

@[expose] public section

universe u v

namespace RingHom

/-- A finite flat algebra whose reduction modulo an ideal in the Jacobson radical is the
base quotient has rank one at every prime.
Source: Stacks Project, More on Algebra, Lemma Tag 0ELZ
(blueprint: lem-weil-pbc-zariski-pair-rank-one-propagation).
Proof:
1. The quotient isomorphism and the quotient/tensor-product equivalence identify
   `(A/I) ⊗[A] B` with `A/I` as an `A/I`-module.
2. Given a prime `p`, choose a maximal ideal `m` containing it. Since the Jacobson
   radical is contained in `m`, so is `I`; thus `m` comes from a prime `q` of `A/I`.
   The base-change formula for rank and the equivalence in step 1 give rank one at `m`.
3. For a finite flat module the rank is unchanged under specialization `p ≤ m`.
   The localization at `p` is finite free over the local ring `A_p`; its rank is one,
   so it is linearly equivalent to `A_p`.
-/
theorem zariskiPair_rank_one_propagation
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Module.FinitePresentation A B]
    (I : Ideal A) (hI : I ≤ Ideal.jacobson (⊥ : Ideal A))
    (hflat : RingHom.Flat (algebraMap A B))
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B)
        Ideal.le_comap_map)) :
    ∀ (p : Ideal A) [p.IsPrime],
      Nonempty
        (LocalizedModule p.primeCompl B ≃ₗ[Localization.AtPrime p]
          Localization.AtPrime p) := by
  have : Module.Flat A B := (RingHom.flat_algebraMap_iff).mp hflat
  let e := AlgEquiv.ofBijective
    (Algebra.ofId (A ⧸ I) (B ⧸ I.map (algebraMap A B))) hquot
  let e' : TensorProduct A (A ⧸ I) B ≃ₗ[A ⧸ I] A ⧸ I :=
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm.toLinearEquiv ≪≫ₗ
      e.symm.toLinearEquiv
  intro p hp
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p hp.ne_top
  have : m.IsMaximal := hm
  have hIm : I ≤ m := hI.trans (sInf_le ⟨bot_le, hm⟩)
  obtain ⟨q, hq⟩ : (⟨m, inferInstance⟩ : PrimeSpectrum A) ∈
      Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker, PrimeSpectrum.mem_zeroLocus]
    exact hIm
  have : Nontrivial (A ⧸ I) := q.nontrivial
  have hqrank : Module.rankAtStalk (R := A ⧸ I) (TensorProduct A (A ⧸ I) B) q = 1 := by
    rw [Module.rankAtStalk_eq_of_equiv e', Module.rankAtStalk_self]
    rfl
  have hmrank : Module.rankAtStalk (R := A) B ⟨m, inferInstance⟩ = 1 := by
    rw [Module.rankAtStalk_baseChange] at hqrank
    simpa only [Ideal.Quotient.algebraMap_eq, hq] using hqrank
  have hprank : Module.rankAtStalk (R := A) B ⟨p, hp⟩ = 1 :=
    (Module.rankAtStalk_eq_of_le_of_finite_of_flat' B hpm).trans hmrank
  have : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl B) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hprank
  exact ⟨e.symm⟩

end RingHom
