/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Bijectivity of flat compatible completion maps

Source: More on Algebra, Lemma Tag 0AGX. The proof uses completeness and separation
for surjectivity, and faithful flatness for injectivity.
-/

@[expose] public section

universe u v

namespace RingHom

/-- Bijectivity of a completion map under the residue-field and maximal-ideal hypotheses.
Source: More on Algebra, Lemma Tag 0AGX, final rank-one argument.
(blueprint: theorem-finite-etale-covers-proper-henselian--2)

Proof:
Let R and S denote the two completions, with maximal ideals mR and nS.
The local-completion theorem identifies these ideals with those extended from A and B,
and identifies their residue fields with the residue fields of A and B. Compatibility
and hmax therefore give mR S = nS. In particular the map sends mR into nS, hence
sends every power into the corresponding power and is adically continuous.
An element of R is congruent modulo mR^k to an element of A for every k. Thus
compatibility and separation of S identify this map with the componentwise completion
map, including its action on residue fields. The same argument identifies it with the
map supplied by finite_after_completion. Since hmax and hres identify B/mA B with
A/mA, that theorem makes S finite over R for this map.
The assumed flatness now makes S a finite free module over the local ring R.
Reduction modulo mR identifies S/mR S with B/mB, a one-dimensional vector space
over A/mA, by hres. A finite basis therefore has exactly one member e.
Write 1 = u e. If u belongs to mR then 1 belongs to mR S = nS, impossible in a
nonzero local ring. Thus u is a unit, so 1 itself is a basis. Every element of S is
then uniquely x times 1 for x in R, which says exactly that the ring map is bijective.
-/
theorem completion_map_bijective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B]
    (φ : A →+* B) [IsLocalHom φ]
    (hmax : Ideal.map φ (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal B)
    (hres : Function.Bijective (Ideal.quotientMap (IsLocalRing.maximalIdeal B) φ
      (IsLocalRing.maximalIdeal_comap φ).ge))
    (φhat : AdicCompletion (IsLocalRing.maximalIdeal A) A →+*
      AdicCompletion (IsLocalRing.maximalIdeal B) B)
    (hcomp : φhat.comp (algebraMap A
      (AdicCompletion (IsLocalRing.maximalIdeal A) A)) =
      (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)).comp φ)
    (hflat : φhat.Flat) : Function.Bijective φhat := by
  let m := IsLocalRing.maximalIdeal A
  let n := IsLocalRing.maximalIdeal B
  let R := AdicCompletion m A
  let S := AdicCompletion n B
  have hn : n.FG := Ideal.fg_of_isNoetherianRing n
  let := φhat.toAlgebra
  have hmaxhat : Ideal.map φhat (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal S := by
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map, hcomp,
      ← Ideal.map_map, hmax, ← AdicCompletion.maximalIdeal_eq_map]
  have : IsLocalHom φhat :=
    ((IsLocalRing.local_hom_TFAE φhat).out 1 3).mpr hmaxhat.le
  have : Module.Flat R S := hflat
  -- Flat local maps are faithfully flat, hence injective.
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  refine ⟨FaithfulSMul.algebraMap_injective R S, ?_⟩
  -- Lift residues, then use completeness of R and separation of S.
  have hlift (s : S) : ∃ r : R, s - φhat r ∈ IsLocalRing.maximalIdeal S := by
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ n s)
    obtain ⟨q, hq⟩ := hres.surjective (Ideal.Quotient.mk n b)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    have hqa : Ideal.Quotient.mk n (φ a) = Ideal.Quotient.mk n b := by
      simpa only [Ideal.quotientMap_mk] using hq
    refine ⟨algebraMap A R a, ?_⟩
    rw [AdicCompletion.maximalIdeal_eq_map]
    have hzero : AdicCompletion.evalOneₐ n (s - φhat (algebraMap A R a)) = 0 := by
      have ha : φhat (algebraMap A R a) = algebraMap B S (φ a) :=
        DFunLike.congr_fun hcomp a
      rw [map_sub, ha, (AdicCompletion.evalOneₐ n).commutes]
      exact sub_eq_zero.mpr (hb.symm.trans hqa.symm)
    rw [← AdicCompletion.ker_evalOneₐ_eq_map n hn]
    exact hzero
  have : IsHausdorff (Ideal.map φhat (IsLocalRing.maximalIdeal R)) S := by
    rw [hmaxhat]
    infer_instance
  apply surjective_of_mk_map_comp_surjective (I := IsLocalRing.maximalIdeal R) φhat
  intro z
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨r, hr⟩ := hlift s
  refine ⟨r, ?_⟩
  change Ideal.Quotient.mk _ (φhat r) = Ideal.Quotient.mk _ s
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  rw [hmaxhat]
  simpa only [neg_sub] using (IsLocalRing.maximalIdeal S).neg_mem hr

end RingHom
