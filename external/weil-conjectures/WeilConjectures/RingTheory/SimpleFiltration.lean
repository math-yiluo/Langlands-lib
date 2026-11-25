/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Length

/-!
# Simple filtrations of finite-length modules

Source: Stacks Project, Algebra, Tags 02LY, 00J1 and 00J3, part (2)
(blueprint: theorem-finite-etale-covers-proper-henselian--2).
-/

@[expose] public section

universe u v

namespace Module

/-- A finite-length module admits a finite strictly increasing filtration with simple quotients.

Source: Stacks Project, Algebra, Tags 02LY, 00J1 and 00J3, part (2)
(blueprint: theorem-finite-etale-covers-proper-henselian--2).

Proof: By `def-weil-pbc-module-length`, lengths of strict submodule chains are bounded by
`length R M`. Chains from zero to the whole module exist: use the one-term chain for the
zero module and the chain from zero to the whole module otherwise. Their lengths form a
nonempty bounded set of natural numbers, so choose a chain of largest length.
For each adjacent pair, its quotient is nonzero because the inclusion is strict. If the
quotient had a nonzero proper submodule, its inverse image under the quotient projection
would lie strictly between the adjacent terms. Inserting it would produce a longer chain,
contradicting maximality. Thus each quotient is simple by `def-weil-pbc-simple-module`.
-/
theorem exists_simple_filtration_of_length_lt_top
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (hM : Module.length R M < ⊤) :
    ∃ (r : ℕ) (F : Fin (r + 1) → Submodule R M),
      F 0 = ⊥ ∧ F (Fin.last r) = ⊤ ∧
        (∀ i : Fin r, F i.castSucc < F i.succ) ∧
        (∀ i : Fin r,
          IsSimpleModule R
            (↥(F i.succ) ⧸ Submodule.comap (F i.succ).subtype (F i.castSucc))) := by
  obtain ⟨s, hs₀, hs₁⟩ := isFiniteLength_iff_exists_compositionSeries.mp
    (Module.length_ne_top_iff.mp hM.ne)
  refine ⟨s.length, s, hs₀, hs₁, ?_, ?_⟩
  · intro i
    exact (s.step i).lt
  · intro i
    exact (covBy_iff_quot_is_simple (s.step i).le).mp (s.step i)

end Module
