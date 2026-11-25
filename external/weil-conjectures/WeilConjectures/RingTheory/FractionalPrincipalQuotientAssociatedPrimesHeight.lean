/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.Height
import WeilConjectures.RingTheory.NormalDomainPrincipalQuotientAssociatedHeight

@[expose] public section
universe u v
namespace Ideal

/-- Height-one part of the fractional principal quotient associated-prime argument.
Source: Stacks Project, Algebra, Lemma 10.157.6, Tag 031T, clause (3).
(blueprint: lem-weil-pbc-normal-domain-fractional-principal-quotient-ass-height)
The proof writes a nonzero fraction as `a / b`, embeds the quotient by `A ∩ yA`
into the principal quotient by `a`, and applies the normal-domain principal quotient
height theorem. -/
theorem associatedPrimes_fractionalPrincipalQuotient_height
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsDomain A] [IsIntegrallyClosed A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K] (y : K) (hy : y ≠ 0) :
    ∀ p ∈ associatedPrimes A
        (A ⧸ (Submodule.span A ({y} : Set K)).comap (Algebra.linearMap A K)),
      p.height = 1 := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective A y
  have hbK : algebraMap A K b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have ha : a ≠ 0 := by
    intro h
    simp [h] at hab
    exact hy hab.symm
  let J := (Submodule.span A ({y} : Set K)).comap (Algebra.linearMap A K)
  let I : Ideal A := Ideal.span {a}
  have hmem (c : A) : c ∈ J ↔ b * c ∈ I := by
    change algebraMap A K c ∈ Submodule.span A ({y} : Set K) ↔ b * c ∈ I
    rw [Submodule.mem_span_singleton, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨d, hd⟩
      refine ⟨d, ?_⟩
      apply IsFractionRing.injective A K
      rw [map_mul, map_mul]
      rw [Algebra.smul_def, ← hab] at hd
      have he := congrArg (fun z : K ↦ z * algebraMap A K b) hd
      field_simp at he
      simpa [mul_comm] using he
    · rintro ⟨d, hd⟩
      refine ⟨d, ?_⟩
      rw [Algebra.smul_def, ← hab]
      rw [← mul_div_assoc]
      apply (div_eq_iff hbK).mpr
      have he := congrArg (algebraMap A K) hd
      simpa [map_mul, mul_comm, mul_div_assoc] using he
  let g : A →ₗ[A] A := b • LinearMap.id
  have hJI : J = Submodule.comap g (I : Submodule A A) := by
    ext c
    exact hmem c
  let f : (A ⧸ J) →ₗ[A] (A ⧸ I) := J.mapQ (I : Submodule A A) g hJI.le
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    change LinearMap.ker (J.liftQ ((I : Submodule A A).mkQ.comp g) _) = ⊥
    rw [Submodule.ker_liftQ, LinearMap.ker_comp, Submodule.ker_mkQ, ← hJI]
    exact Submodule.mkQ_map_self J
  intro p hp
  exact height_eq_one_of_mem_associatedPrimes_quotient_span ha
    (associatedPrimes.subset_of_injective hf hp)
end Ideal
