/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import WeilConjectures.RingTheory.HenselianEtaleRetractionExistence
import WeilConjectures.RingTheory.HenselianEtaleRetractionUniqueness

/-!
# Retractions of étale algebras over henselian local rings

Source: literature/stacks-project/algebra.tex, Lemma Tag 04GG (implication (1) ⇒ (8))
(blueprint: lem-weil-pbc-henselian-etale-retraction).
-/

@[expose] public section

universe u

open AlgebraicGeometry

/-- A residue-rational point of an étale algebra over a henselian local ring
has a unique section back to the base ring.

Source: Stacks Project, Lemma Tag 04GG, implication (1) ⇒ (8), with the
idempotent-lifting henselian terminology of `def-weil-pbc-henselian-terminology`.
(blueprint: lem-weil-pbc-henselian-etale-retraction).

Proof (the six steps of the DAG node):
1. The residue-field isomorphism identifies `B / q'` with the residue field κ of `S`
   (`def-weil-residue-field`). It gives a surjective S-algebra map ρ with kernel `q'`.
   Two surjective S-algebra maps to κ with the same kernel agree, since an S-linear
   automorphism of κ is the identity. Thus a retraction σ has the required prime
   preimage exactly when its reduction is ρ.
2. By `lem-weil-pbc-etale-locally-standard` (Stacks 00UE), choose `g ∉ q'` and a
   standard étale presentation of `B_g` as `C = S[t][Y]/(f, Yh - 1)`, with `f`
   monic and `f' p₁ + f p₂ = h^n`.
3. Since ρ(g) is nonzero, ρ extends uniquely to `B_g` and hence to a map ρ_C on C.
   Localization gives a bijection between lifts of ρ_C and retractions of B with
   prime preimage `q'`: in the reverse direction σ(g) is a unit in the local ring S.
4. The image a₀ of t under ρ_C satisfies f̄(a₀) = 0 and h̄(a₀) ≠ 0 by
   `lem-weil-pbc-standard-etale-pair-maps`. Evaluating the standard étale identity
   gives f̄'(a₀) ≠ 0, including when n = 0.
5. Use `lem-weil-pbc-henselian-local-root-lifting` to lift a₀ to a root a of f.
   The henselian class here is the equivalent root-lifting form of the node's
   idempotent-lifting terminology (Stacks 04GG and More on Algebra 09XI).
   Then h(a) is a unit. The standard étale universal property
   (`lem-weil-pbc-standard-etale-pair-maps`) gives a map C → S reducing to ρ_C,
   which descends to the required retraction by step 3.
6. Any two such maps send t to roots congruent to a₀. Their derivative is a unit,
   so `lem-weil-pbc-simple-root-uniqueness` (Stacks 06RR) makes the roots equal.
   Maps from C are determined by t (`lem-weil-pbc-standard-etale-pair-maps`);
   step 3 then gives equality of the retractions.
-/
theorem existsUnique_algHom_of_henselianLocalRing_etale
    {S B : Type u} [CommRing S] [CommRing B] [HenselianLocalRing S]
    (φ : S →+* B)
    [AlgebraicGeometry.Etale (Scheme.Spec.map (CommRingCat.ofHom φ).op)]
    (q' : Ideal B) [q'.IsPrime]
    (hq : q'.comap φ = IsLocalRing.maximalIdeal S)
    (hres : Function.Bijective
      (Ideal.ResidueField.map (IsLocalRing.maximalIdeal S) q' φ hq.symm)) :
    letI : Algebra S B := φ.toAlgebra
    ∃! σ : B →ₐ[S] S,
      (IsLocalRing.maximalIdeal S).comap σ.toRingHom = q' := by
  set_option linter.style.haveILetI false in
    letI : Algebra S B := φ.toAlgebra
  obtain ⟨σ, hσ⟩ := exists_algHom_of_henselianLocalRing_etale φ q' hq hres
  refine ⟨σ, hσ, ?_⟩
  intro τ hτ
  exact (algHom_eq_of_henselianLocalRing_etale φ q' hq hres σ τ hσ hτ).symm
