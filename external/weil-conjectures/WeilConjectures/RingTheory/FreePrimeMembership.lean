/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalProperties.Basic

/-!
# Prime membership in a finite free module after localization

Source: Stacks Project, Algebra, Definition Tag 00CO and the localization at a prime;
the coordinate calculation underlying Lemma Tag 00NX
(blueprint: lem-sc-free-prime-membership).
-/

@[expose] public section

universe u

namespace Module

/-- Prime membership in `R^n` is detected after localization at the same prime, and each
coordinate satisfies the corresponding scalar criterion.

Source: Stacks Project, Algebra, Definition Tag 00CO, module localization Tag 07JZ,
and the finite-free coordinate calculation underlying Lemma Tag 00NX
(blueprint: lem-sc-free-prime-membership).

Here `F = Fin n → R`, `S = p.primeCompl`, `F_p = LocalizedModule S F`
[def-weil-pbc-module-localization], and `R_p = Localization.AtPrime p`
[def-weil-pbc-localization-at-prime]. The extended ideal `p.map (algebraMap R R_p)`
acting on the top submodule is `pF_p`; `p • ⊤` is `pF`.

Proof (the node's single step): membership in `pR^n` is coordinatewise membership in `p`:
use induction on ideal scalar products in one direction and the finite sum of standard
coordinate vectors in the other. Localization commutes with ideal scalar products, so
membership of `s/1` in `pF_p` gives a fraction `v/t` with `v ∈ pR^n` equal to `s/1`.
Equality of fractions supplies another denominator `a`, with `at • s = a • v`.
Every coordinate of `at • s` therefore lies in `p`. Since `at ∉ p`, primality forces
each coordinate of `s` into `p`. Conversely, represent `s/1` with denominator `1`.
For the scalar clause use the localization ideal criterion: `s_i/1 ∈ pR_p` iff
some `u ∉ p` has `u s_i ∈ p`, and apply primality or use denominator `1`.
-/
theorem free_prime_mem_localized_iff
    {R : Type u} [CommRing R] (n : ℕ) (s : Fin n → R) (p : Ideal R) [p.IsPrime] :
    (LocalizedModule.mkLinearMap p.primeCompl (Fin n → R) s ∈
        (Ideal.map (algebraMap R (Localization.AtPrime p)) p) •
          (⊤ : Submodule (Localization.AtPrime p)
            (LocalizedModule p.primeCompl (Fin n → R))) ↔
      s ∈ p • (⊤ : Submodule R (Fin n → R))) ∧
    (∀ i : Fin n,
      algebraMap R (Localization.AtPrime p) (s i) ∈
          Ideal.map (algebraMap R (Localization.AtPrime p)) p ↔ s i ∈ p) := by
  have hcoord (v : Fin n → R) :
      v ∈ p • (⊤ : Submodule R (Fin n → R)) ↔ ∀ i, v i ∈ p := by
    constructor
    · intro hv
      refine Submodule.smul_induction_on hv ?_ ?_
      · intro r hr w _ i
        exact p.mul_mem_right (w i) hr
      · intro v w hv hw i
        exact p.add_mem (hv i) (hw i)
    · intro hv
      rw [pi_eq_sum_univ' v]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem_smul (hv i) Submodule.mem_top
  let f := LocalizedModule.mkLinearMap p.primeCompl (Fin n → R)
  have hloc : (p • (⊤ : Submodule R (Fin n → R))).localized'
      (Localization.AtPrime p) p.primeCompl f =
        Ideal.map (algebraMap R (Localization.AtPrime p)) p • ⊤ := by
    rw [Submodule.localized'_smul, Ideal.localized'_eq_map, Submodule.localized'_top]
  constructor
  · rw [← hloc, Submodule.mem_localized']
    constructor
    · rintro ⟨v, hv, t, ht⟩
      have he : IsLocalizedModule.mk' f v t = IsLocalizedModule.mk' f s (1 : p.primeCompl) := by
        simpa only [IsLocalizedModule.mk'_one] using ht
      obtain ⟨a, ha⟩ := (IsLocalizedModule.mk'_eq_mk'_iff f v s t 1).mp he
      simp only [one_smul] at ha
      have hs : (a * t) • s ∈ p • (⊤ : Submodule R (Fin n → R)) := by
        rw [mul_smul, ha]
        exact Submodule.smul_of_tower_mem _ a hv
      apply (hcoord s).mpr
      intro i
      have hi := (hcoord _).mp hs i
      change ((a * t : p.primeCompl) : R) * s i ∈ p at hi
      exact (Ideal.IsPrime.mem_or_mem (inferInstance : p.IsPrime) hi).resolve_left (a * t).property
    · intro hs
      exact ⟨s, hs, 1, IsLocalizedModule.mk'_one p.primeCompl f s⟩
  · intro i
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl]
    constructor
    · rintro ⟨u, hu, hus⟩
      rcases Ideal.IsPrime.mem_or_mem (inferInstance : p.IsPrime) hus with hu' | hi
      · exact False.elim (hu hu')
      · exact hi
    · intro hi
      exact ⟨1, p.primeCompl.one_mem, by simpa using hi⟩

end Module
