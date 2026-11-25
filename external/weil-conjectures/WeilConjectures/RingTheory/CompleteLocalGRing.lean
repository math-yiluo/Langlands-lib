/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.CompleteLocalDomainFiniteOverRegular
import WeilConjectures.RingTheory.CompleteLocalQuotient
import WeilConjectures.RingTheory.FiniteSubringGenericFormalFiber
import WeilConjectures.RingTheory.GRingPairsOfPrimes
import WeilConjectures.RingTheory.RegularPowerSeriesGenericFormalFiber

/-!
# Complete local Noetherian rings are G-rings

Source: Stacks Project, More on Algebra, Proposition 07PS (blueprint:
lem-weil-pbc-complete-local-g-ring).
-/

@[expose] public section

universe u

/-- A Noetherian complete local ring is a G-ring. Source: Stacks Project,
More on Algebra, Proposition 07PS (blueprint: lem-weil-pbc-complete-local-g-ring).
Proof (Stacks 07PS, following the seven steps of the node):
1. By lem-weil-pbc-g-ring-check-pairs-of-primes, reduce to the formal fibres over the zero
prime of B = S/q. Quotients and localizations are Noetherian; their completions and
fibres are Noetherian by lem-weil-pbc-adic-completion-noetherian and
lem-weil-pbc-fibre-ring-noetherian. It remains to check geometric regularity.
2. By lem-weil-pbc-complete-local-quotient, B is a complete Noetherian local domain.
Thus reduce to a complete local domain A, its fraction field K, and the fibres of
completed prime localizations over K.
3. By lem-weil-pbc-complete-local-domain-finite-over-regular, choose a regular complete
local subring A₀ over which A is finite. It is a power series ring over a field or a
Cohen ring. Since it is a subring of a domain, it has a fraction field K₀.
4. Finiteness implies quasi-finiteness: each fibre is finite-dimensional over its
residue field; its prime quotients are fields, and the Chinese remainder theorem
bounds the number of maximal ideals by that dimension. Apply
lem-weil-pbc-formal-fibre-quasi-finite-ascent to reduce geometric regularity of the
formal fibre of A to that of A₀.
5. By lem-weil-pbc-regular-local-localization and lem-weil-pbc-completion-regular-local,
the completed prime localization of A₀ is regular. Its tensor product with K₀ is a
localization, hence regular; it is Noetherian by the completion and fibre lemmas.
6. In characteristic zero every finite purely inseparable field extension is trivial,
so this regular fibre is geometrically regular by the definition in
theorem-finite-etale-covers-proper-henselian--2.
7. In positive characteristic A₀ cannot be a power series ring over a Cohen ring:
a Cohen ring has characteristic zero, as its nonzero prime-number uniformizer is
not a unit. Thus A₀ is a power series ring over a field. Apply
lem-weil-pbc-helper-g-ring-char-p with m = 0, and transport along the power-series
isomorphism. Combining both characteristics with the preceding reductions proves
geometric regularity of every required formal fibre, hence the G-ring condition. -/
theorem isGRing_of_isNoetherianRing_of_isAdicComplete
    (S : Type u) [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    [IsAdicComplete (IsLocalRing.maximalIdeal S) S] : IsGRing S := by
  apply (isGRing_iff_pairsOfPrimes S).mpr
  intro q p hq hp hqp
  let B := S ⧸ q
  let : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr hq.ne_top
  let : IsLocalRing B :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  have hcomplete := quotient_complete_local S q hq.ne_top
  let : IsAdicComplete (IsLocalRing.maximalIdeal B) B := hcomplete.2.2.2
  let P := p.map (Ideal.Quotient.mk q)
  let : P.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hqp
  obtain ⟨B₀, hreg, _, hfinite, _, _, _, hmodel⟩ :=
    IsLocalRing.complete_local_domain_finite_over_regular B
  let : IsRegularLocalRing B₀ := hreg
  let : Module.Finite B₀ B := hfinite
  have hbase := isGeometricallyRegular_genericFormalFiber_of_regular_powerSeries
    B₀ hmodel (P.comap (algebraMap B₀ B))
  have hgeom := isGeometricallyRegular_genericFormalFiber_of_finite_subring
    B B₀ q.ResidueField P hbase
  exact ⟨hgeom.1, hgeom⟩
