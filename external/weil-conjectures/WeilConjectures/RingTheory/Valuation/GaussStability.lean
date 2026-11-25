/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Valuation.GaussStability.ArtinSchreier
public import WeilConjectures.RingTheory.Valuation.GaussStability.Kummer

/-!
# Stability of residually transcendental extensions (Ohm, Kuhlmann)

Let `𝒪` be a valuation subring of a field `Ω` with residue characteristic `p`, and `K ⊆ Ω` an
algebraically closed subfield which is algebraic over a discretely valued subfield `K₀` with the
full residue field `k` of `K` (the value group of `Ω` having rational rank one over that of
`K₀`). Let `x ∈ 𝒪` have residue `x̄` transcendental over `k`, and let `L = K·B` where `B ⊇ K₀(x)`
is discretely valued, algebraic over `K₀(x)` and residually separable over `k(x̄)`: for instance
`L = K(x)` with the Gauss valuation, or its inertia field in the rank-one situation.

**Stability.** Let `L ⊆ L₂` be an extension in whose residue field `x̄` is not a `p`-th power.
Then an Artin–Schreier equation (`char Ω = p`) or a Kummer equation of degree `p`
(`char Ω = 0`) over `L` which has a root in `L₂` has a root in `L`
(`ValuationSubring.exists_artinSchreier_root_of_transcendental`,
`ValuationSubring.exists_pow_root_of_transcendental`). In particular a cyclic extension of
degree `p` of `L` which is immediate (and `L` is henselian for these equations, see the
hypotheses) does not exist: `L` is defectless for such extensions. This is the
residue-transcendental case of the stability theorem of Ohm (J. Ohm, *Simple transcendental
extensions of valued fields*, J. Math. Kyoto Univ. 22 (1982)) and Kuhlmann (F.-V. Kuhlmann,
*Elimination of ramification I*, Trans. AMS 362 (2010), §4).

The proof combines the approximation package
(`ValuationSubring.exists_frobeniusLift_package_of_transcendental`) with the abstract
Artin–Schreier and Kummer normal forms (`exists_artinSchreier_root_of_approx`,
`exists_pow_eq_of_kummer_of_approx`).
-/

@[expose] public section




