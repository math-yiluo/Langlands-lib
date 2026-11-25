/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.JapaneseDomain
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import WeilConjectures.RingTheory.PowerSeriesN2Aux
import Mathlib.RingTheory.PowerSeries.Ideal

/-!
# Power series over a Japanese domain

Source: Stacks Project, Algebra, Lemma Tag 032Q (lemma-power-series-over-N-2)
(blueprint: lem-weil-pbc-power-series-n2).
-/

@[expose] public section

universe u

namespace PowerSeries

/-- Over a Noetherian N-2 domain, the one-variable formal power series ring is a
Noetherian N-2 domain. Source: Stacks Project, Algebra, Lemma Tag 032Q
(blueprint: lem-weil-pbc-power-series-n2).

Proof:
1. By `lem-weil-pbc-power-series-noetherian` and `lem-weil-pbc-power-series-domain`
   with one variable, the power series ring is Noetherian and a domain.
2. Let R' be the integral closure of R in its fraction field. The N-2 hypothesis
   makes R' finite over R. It is normal by
   `lem-weil-pbc-integral-closure-finite-extension-normal`, Noetherian by
   `lem-weil-pbc-finite-algebra-noetherian`, and N-2 by
   `lem-weil-pbc-n2-ascends-finite-domain-extension`.
3. Choose finitely many R-module generators r_j of R'. For each coefficient a_k
   of a series over R', write a_k as a linear combination of the r_j over R.
   Collecting the coefficient sequences gives series g_j over R and expresses
   the original series as the finite sum of r_j g_j. Thus R'[[x]] is finite over R[[x]].
4. By `lem-weil-pbc-power-series-normal-domain`, R'[[x]] is a Noetherian normal domain.
5. Apply `lem-weil-pbc-tate-n2-complete-principal` to x in R'[[x]]. Its quotient
   by x is R', by `lem-weil-pbc-power-series-quotient-variables`, and is therefore
   an N-2 domain. The ring is x-adically complete by
   `lem-weil-pbc-power-series-variables-complete`. Hence R'[[x]] is N-2.
6. By `lem-weil-pbc-n2-descends-finite-domain-extension`, the finite extension
   R[[x]] into R'[[x]] descends N-2 to R[[x]], completing all three conclusions. -/
theorem noetherian_domain_isN2 (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (hR : IsN2 R (FractionRing R)) :
    IsNoetherianRing (PowerSeries R) ∧
      IsDomain (PowerSeries R) ∧
      IsN2 (PowerSeries R) (FractionRing (PowerSeries R)) := by
  exact ⟨inferInstance, inferInstance, isN2_power_series R hR⟩

end PowerSeries
