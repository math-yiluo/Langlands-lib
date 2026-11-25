/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.RingTheory.NoetherNormalizationOverDomainSurjectiveCore
import Mathlib.Tactic.Ring

@[expose] public section
set_option autoImplicit false
universe u v
namespace Algebra.FiniteType

/-- The constructive part of Noether normalization over a domain, producing a surjective
localization map.  Source: Stacks Project, Algebra, Lemma 07NA.
(blueprint: new-noether-normalization-over-domain-surjective)
Proof: localize `S` at the nonzero elements of `R` and apply field Noether normalization to
the resulting finite-type algebra.  Rescale the normalized coordinates by denominators so that
they lie in `S`; injectivity over the fraction field then gives injectivity of evaluation over
`R`.  Express finite-integral equations for a finite set of algebra generators, clear their
coefficient denominators, and multiply by one common nonzero element of `R` so that the
equations hold in `S`.  If `f` is the product of these clearing factors, let `S'` be generated
over `R` by the normalized coordinates and by `f` times the original generators.  Rescaling
each monic equation shows that these generators are integral over the polynomial subalgebra,
so `S'` is finite over it.  Finally, every element of `S` is a polynomial in the original
generators; multiplying by a sufficiently large power of `f` rewrites it as a polynomial in
the generators of `S'`.  Hence every fraction in `S_f` comes from `S'_f`, which is precisely
surjectivity of the displayed localization map. -/
theorem exists_finite_subalgebra_away_surjective
    (R : Type u) (S : Type v) [CommRing R] [IsDomain R] [CommRing S]
    [Algebra R S] [Algebra.FiniteType R S]
    (hinj : Function.Injective (algebraMap R S)) :
    ∃ (d : ℕ) (y : Fin d → S) (S' : Subalgebra R S),
      Function.Injective (MvPolynomial.aeval (R := R) y) ∧
      ∃ h : (MvPolynomial.aeval (R := R) y).range ≤ S',
        (letI := (Subalgebra.inclusion h).toRingHom.toAlgebra
         Module.Finite (MvPolynomial.aeval (R := R) y).range S') ∧
        ∃ f : R, f ≠ 0 ∧
          Function.Surjective
            (IsLocalization.Away.map
              (Localization.Away (algebraMap R S' f))
              (Localization.Away (S'.val (algebraMap R S' f)))
              S'.val.toRingHom (algebraMap R S' f)) := by
  obtain ⟨g, hgen⟩ := (Algebra.FiniteType.out (R := R) (A := S))
  obtain ⟨d, y, S', hay, h, hfin, f, hf, hg⟩ :=
    exists_finite_subalgebra_away_core R S hinj g hgen
  have hclear : ∀ s : S, ∃ n : ℕ, algebraMap R S f ^ n * s ∈ S' := by
    intro s
    have hs : s ∈ Algebra.adjoin R (g : Set S) := by rw [hgen]; trivial
    induction hs using Algebra.adjoin_induction with
    | mem x hx => exact ⟨1, by simpa using hg x hx⟩
    | algebraMap r => exact ⟨0, by simp⟩
    | add x z hx hz ihx ihz =>
      obtain ⟨n, hn⟩ := ihx
      obtain ⟨m, hm⟩ := ihz
      refine ⟨n + m, ?_⟩
      have h₁ := S'.mul_mem (S'.algebraMap_mem (f ^ m)) hn
      have h₂ := S'.mul_mem (S'.algebraMap_mem (f ^ n)) hm
      convert S'.add_mem h₁ h₂ using 1
      simp only [map_pow, pow_add]
      ring
    | mul x z hx hz ihx ihz =>
      obtain ⟨n, hn⟩ := ihx
      obtain ⟨m, hm⟩ := ihz
      refine ⟨n + m, ?_⟩
      convert S'.mul_mem hn hm using 1
      simp only [pow_add]
      ring
  refine ⟨d, y, S', hay, h, hfin, f, hf, ?_⟩
  apply (IsLocalization.Away.map_surjective_iff
    (Localization.Away (algebraMap R S' f))
    (Localization.Away (S'.val (algebraMap R S' f)))
    S'.val.toRingHom (algebraMap R S' f)).2
  intro s
  obtain ⟨n, hn⟩ := hclear s
  exact ⟨⟨algebraMap R S f ^ n * s, hn⟩, n, rfl⟩

end Algebra.FiniteType
