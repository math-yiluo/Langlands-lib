/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Localization.NormTrace
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The norm of a finite free algebra and primes

Let `S` be a finite free `R`-algebra. An element `a : S` lies in no prime of `S` over a prime `p`
of `R` if and only if its norm `N_{S/R}(a)` does not lie in `p`. Geometrically: the locus where
the norm of a function does not vanish is the set of points all of whose preimages lie in the
non-vanishing locus of the function.

## Main statements

- `Algebra.isUnit_norm_iff_isUnit`: in a finite free algebra, an element is a unit if and only
  if its norm is.
- `Algebra.norm_notMem_iff`: `N_{S/R}(a) ∉ p` if and only if `a ∉ q` for every prime `q` of `S`
  lying over `p`.
-/

@[expose] public section

open Module

namespace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- **An element of a finite free algebra is a unit if and only if its norm is a unit.** -/
theorem isUnit_norm_iff_isUnit [Module.Free R S] [Module.Finite R S] (a : S) :
    IsUnit (Algebra.norm R a) ↔ IsUnit a := by
  rw [Algebra.norm_apply, ← LinearMap.isUnit_iff_isUnit_det]
  refine ⟨fun h ↦ ?_, fun h ↦ h.map (Algebra.lmul R S).toMonoidHom⟩
  obtain ⟨b, hb⟩ := (Module.End.isUnit_iff _).mp h |>.2 1
  exact IsUnit.of_mul_eq_one b hb

/-- **The norm and primes lying over a prime.** Let `S` be a finite free `R`-algebra and `p` a
prime of `R`. Then `N_{S/R}(a) ∉ p` if and only if `a` lies in no prime of `S` over `p`. -/
theorem norm_notMem_iff [Module.Free R S] [Module.Finite R S] (p : Ideal R) [p.IsPrime]
    (a : S) : Algebra.norm R a ∉ p ↔
      ∀ q : Ideal S, q.IsPrime → q.comap (algebraMap R S) = p → a ∉ q := by
  classical
  let Rₚ := Localization.AtPrime p
  let M := Algebra.algebraMapSubmonoid S p.primeCompl
  let Sₚ := Localization M
  let : Algebra Rₚ Sₚ := localizationAlgebra p.primeCompl S
  have : IsScalarTower R Rₚ Sₚ := inferInstance
  have hN := Algebra.norm_localization (Rₘ := Rₚ) (Sₘ := Sₚ) R p.primeCompl a
  have : Module.Free Rₚ Sₚ :=
    .of_basis ((Module.Free.chooseBasis R S).localizationLocalization Rₚ p.primeCompl Sₚ)
  have : Module.Finite Rₚ Sₚ := Module.Finite.of_basis
    ((Module.Free.chooseBasis R S).localizationLocalization Rₚ p.primeCompl Sₚ)
  have h₁ : Algebra.norm R a ∉ p ↔ IsUnit (algebraMap S Sₚ a) := by
    rw [← isUnit_norm_iff_isUnit (R := Rₚ), hN,
      IsLocalization.AtPrime.isUnit_to_map_iff Rₚ p]
    rfl
  rw [h₁]
  constructor
  · rintro hu q hq hqp haq
    have hdisj : Disjoint (M : Set S) q := by
      rw [Set.disjoint_left]
      rintro _ ⟨r, hr, rfl⟩ hrq
      exact hr (hqp ▸ Ideal.mem_comap.mpr hrq)
    have := IsLocalization.isPrime_of_isPrime_disjoint M Sₚ q hq hdisj
    exact (q.map (algebraMap S Sₚ)).ne_top_iff_one.mp this.ne_top
      ((Ideal.map (algebraMap S Sₚ) q).eq_top_of_isUnit_mem (Ideal.mem_map_of_mem _ haq) hu ▸
        Submodule.mem_top)
  · intro h
    by_contra hu
    obtain ⟨m, hm, ham⟩ := exists_max_ideal_of_mem_nonunits hu
    let q₀ := m.comap (algebraMap S Sₚ)
    have hq₀ : q₀.IsPrime := Ideal.comap_isPrime _ _
    have hq₀p : q₀.comap (algebraMap R S) ≤ p := by
      intro r hr
      by_contra hrp
      have hunit : IsUnit (algebraMap S Sₚ (algebraMap R S r)) :=
        IsLocalization.map_units Sₚ (⟨algebraMap R S r, r, hrp, rfl⟩ : M)
      exact hm.ne_top (m.eq_top_of_isUnit_mem hr hunit)
    have : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
    obtain ⟨q, hq₀q, hq, hqp⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime p q₀ hq₀p
    exact h q hq hqp (hq₀q ham)

end Algebra
