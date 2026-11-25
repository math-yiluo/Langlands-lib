/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.KrullDimension.Basic

import WeilConjectures.RingTheory.FilteredColimitPrimeChainContraction
import WeilConjectures.RingTheory.FilteredColimitPrimeChainDimensionBound

/-!
# Prime chains and dimension of filtered ring colimits

Source: Stacks Project, More on Algebra, Tag 06LK, converse inequality in the proof
(blueprint: lem-sc-filtered-colimit-prime-chain-dimension).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat

/-- A finite strict prime chain in a filtered colimit contracts strictly at some stage;
its Krull dimension is therefore bounded by the supremum of the stage dimensions.
Source: Stacks Project, Tag 06LK, converse inequality in the proof
(blueprint: lem-sc-filtered-colimit-prime-chain-dimension).

Proof:
1. For each adjacent pair of primes choose an element in the larger but not the smaller.
   By `lem-pc-filtered-colimit-commrings-elementwise`, each chosen element comes from a
   stage. Filteredness supplies one stage receiving all finitely many stages. Contraction
   preserves primality and inclusion; the chosen representatives witness strictness.
   For a chain of length zero, choose any object of the nonempty filtered category.
2. Each finite chain length is thus bounded by the dimension of some stage, and hence by
   the supremum of all stage dimensions. Taking the supremum over finite chain lengths
   yields the dimension inequality, using `def-weil-pbc-krull-dimension-ring`. -/
theorem filteredColimit_prime_chain_and_dimension
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{u}) :
    (∀ (n : ℕ) (p : Fin (n + 1) → Ideal (colimit R : CommRingCat.{u})),
      (∀ j, (p j).IsPrime) → StrictMono p →
      ∃ i : I,
        (∀ j, (Ideal.comap (colimit.ι R i).hom (p j)).IsPrime) ∧
        StrictMono (fun j ↦ Ideal.comap (colimit.ι R i).hom (p j))) ∧
    ringKrullDim (colimit R : CommRingCat.{u}) ≤ ⨆ i : I, ringKrullDim (R.obj i) := by
  exact ⟨filteredColimit_prime_chain_contraction R,
    filteredColimit_prime_chain_dimension_bound R⟩

end CommRingCat
