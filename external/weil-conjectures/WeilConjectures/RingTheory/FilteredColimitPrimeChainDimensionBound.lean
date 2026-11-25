/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
import WeilConjectures.RingTheory.FilteredColimitPrimeChainContraction

/-! Krull-dimension bound for filtered colimits.

Source: Stacks Project, More on Algebra, Tag 06LK.
(blueprint: lem-sc-filtered-colimit-prime-chain-dimension-bound)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat

/-- The Krull dimension of a filtered colimit is bounded by the supremum of the
dimensions of its stages. This follows by applying finite prime-chain contraction
to each chain and then taking the supremum in the definition of `ringKrullDim`.
(blueprint: lem-sc-filtered-colimit-prime-chain-dimension-bound) -/
theorem filteredColimit_prime_chain_dimension_bound
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{u}) :
    ringKrullDim (colimit R : CommRingCat.{u}) ≤ ⨆ i : I, ringKrullDim (R.obj i) := by
  change Order.krullDim (PrimeSpectrum (colimit R : CommRingCat.{u})) ≤ _
  unfold Order.krullDim
  refine iSup_le fun p ↦ ?_
  obtain ⟨i, hprime, hmono⟩ := filteredColimit_prime_chain_contraction R p.length
    (fun j ↦ (p j).asIdeal) (fun j ↦ (p j).isPrime)
    (fun a b hab ↦ (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr (p.strictMono hab))
  let q : LTSeries (PrimeSpectrum (R.obj i)) := LTSeries.mk p.length
    (fun j ↦ ⟨Ideal.comap (colimit.ι R i).hom (p j).asIdeal, hprime j⟩)
    (fun a b hab ↦ (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp (hmono hab))
  exact (Order.LTSeries.length_le_krullDim q).trans (le_iSup (fun i ↦ ringKrullDim (R.obj i)) i)

end CommRingCat
