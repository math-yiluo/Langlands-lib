/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.FibreDimensionBoundedOpenUpstairs
import WeilConjectures.Topology.DimensionSupremumLocalDimensions
import WeilConjectures.RingTheory.FibreDimensionLocalizedBound

/-!
# A principal neighbourhood bounding all fibre dimensions

Source: Stacks Project, Algebra, Tag 00QH and Tag 00ST, proof (3)
(blueprint: lem-weil-pbc-fibre-dimension-neighborhood).
-/

@[expose] public section

universe u v

namespace Algebra

/-- For a finite type algebra, a prime whose fibre has local dimension `d` admits a
principal neighbourhood all of whose nonempty fibres have dimension at most `d`.
Source: Stacks Project, Algebra, Tag 00QH and Tag 00ST, proof (3)
(blueprint: lem-weil-pbc-fibre-dimension-neighborhood).

The point `Q` is constructed by `PrimeSpectrum.preimageEquivFiber`: its ideal is the
kernel of the canonical map from `κ(p) ⊗[R] S` to `κ(q)`, sending `a ⊗ s` to `ā * s̄`.
Mathlib places the residue field on the left; the tensor-factor swap identifies this
with `S ⊗[R] κ(p)` in the source, including the specified kernel.

Proof:
1. Apply `lem-weil-pbc-fibre-dimension-bounded-open-upstairs` (00QH) to obtain an open
   neighbourhood `V` of `q` where all local fibre dimensions are at most `d`.
   By `lem-weil-pbc-spec-localization-away-basic-open` (i), choose `g` with
   `q ∈ D(g) ⊆ V`, hence `g ∉ q`.
2. Fix any prime `p'` of `R`. By `lem-weil-pbc-algebra-localization-away-base-change`,
   the fibre of `S_g` is the localization of the fibre of `S` at `g ⊗ 1`.
   By `lem-weil-pbc-spec-localization-away-basic-open` (ii) and `def-weil-affine-spectrum`,
   its spectrum is homeomorphic to the open subspace `O = D(g ⊗ 1)` of that fibre.
3. For each point of `O`, `lem-weil-pbc-fibre-ring-primes-bijection` gives a prime `q'`
   of `S` above `p'`. Since `g ∉ q'`, this prime is in `V`, so its local fibre dimension
   is at most `d`. By `lem-weil-pbc-dimension-at-point-open-subspace`, its dimension in
   `O` is the same and is at most `d`.
4. By `lem-weil-pbc-dimension-supremum-local-dimensions` (0B7I), the dimension of `O`
   is the supremum of these local dimensions, hence at most `d`. The homeomorphism
   preserves chains of irreducible closed subsets and thus Krull dimension
   (`def-kun-topological-krull-dimension`). This gives the bound on the nonempty fibre.
   If `O` is empty, its dimension and the empty supremum are both minus infinity. -/
theorem exists_away_fibre_dimension_le
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [FiniteType R S] (q : PrimeSpectrum S) (d : ℕ) :
    let p := PrimeSpectrum.comap (algebraMap R S) q
    let Q := PrimeSpectrum.preimageEquivFiber R S p ⟨q, rfl⟩
    topologicalKrullDimAt Q = (d : WithBot ℕ∞) →
      ∃ g : S, g ∉ q.asIdeal ∧
        ∀ p' : PrimeSpectrum R,
          Nontrivial (p'.asIdeal.Fiber (Localization.Away g)) →
            topologicalKrullDim (PrimeSpectrum (p'.asIdeal.Fiber (Localization.Away g))) ≤
              (d : WithBot ℕ∞) := by
  dsimp
  intro hd
  obtain ⟨V, hVopen, hqV, hdim⟩ := fibre_dimension_bounded_open_upstairs q d hd
  obtain ⟨b, ⟨g, rfl⟩, hqg, hgV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hqV hVopen
  refine ⟨g, ?_, ?_⟩
  · simpa [PrimeSpectrum.mem_basicOpen] using hqg
  · exact localized_fibre_dimension_le_of_basicOpen g d (fun q' hq' ↦
      hdim q' (hgV hq'))

end Algebra
