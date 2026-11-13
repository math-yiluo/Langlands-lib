# Moy–Prasad statements on supplied filtrations: a ramified SU(3) counterexample

**Status: an unformalized paper argument.** No Lean term is constructed: the
Library has no building data for SU(3). The argument shows that two published
Prop-valued targets cannot be proved. Both quantify over *every* supplied filtration
of `Z(F)` that satisfies `SatisfiesFiltrationAxioms`:

- `Langlands.Geometry.Building.MoyPrasadCommutatorStatement`, which is KP
  Proposition 13.2.5(4) on supplied data;
- `Langlands.Geometry.Building.MoyPrasadCovarianceStatement`, which is KP 13.2.5(1)
  and (2) on supplied data;
- consequently the aggregate `MoyPrasadFiltrationStatement`, whose definition is the
  conjunction of these two with `MoyPrasadSeparatedStatement` and
  `MoyPrasadBoundedOpenStatement` (separation and bounded openness are not addressed
  here).

All three live in module `Langlands.Geometry.Building.KPMoyPrasadFiltrationStatement`.
Lean names below that begin with `ParahoricBuildingData.`, `KPApartmentData.` or
`ApartmentQuotient.` are relative to `Langlands.Geometry.Building`. Names that begin with
`CentralizerFiltration.` are relative to
`Langlands.Geometry.Building.ParahoricBuildingData`.

The argument applies only if the actual quasi-split SU(3) over `Q_2`, with its
standard valuation of root datum, is an instance of `ParahoricBuildingData`
satisfying `SatisfiesApartmentAxioms`. That is how the targets are meant to be read.

The argument does **not** refute the following:
- KP's own Proposition 13.2.5, which uses KP's filtration of `T(k)`. That filtration
  is larger than the one built below.
- The double-root variants `MoyPrasadDoubleRootCommutatorStatement` and
  `MoyPrasadDoubleRootCovarianceStatement` (module `KPMoyPrasadDoubleRootStatement`).
  Their premise `IsDoubleRootCommutatorFriendly` fails for the filtration below (see
  "Scope").

Found while working on Task 5512 (`05aa82d6-2f2e-4113-908c-edc4ea226133`). Worker 3557,
the publisher of the targets, checked the witness arithmetic and accepted the
report.

## Summary

The four published axioms bound the `Z`-component of a commutator of opposite root
elements in only one direction. They require such components to lie in
`Z(F)_r`, but nothing forces `Z(F)_r` to contain more than these components.

Take the smallest filtration `Z'` that the axioms force. In residue characteristic 2,
the commutator of `u ∈ U_{2a,x,r}` with `u' ∈ U_{-a,x,s}` can have a `Z`-component
that lies in `Z'_{r/2+s}`, where commutator friendliness puts it, but not in
`Z'_{r+s}`. This happens when `r > 0` and `s < ω(2)`.

This is the known gap in KP's proof of 13.2.5(4): commutator friendliness gives depth
`r/2 + s`, while `r + s` is needed. In this model the gap actually breaks the
statements.

## Model and normalizations

**Fields.** Let `F = Q_2`, with valuation `ω` normalized by `ω(2) = 1`. Write
`ε := ω(2) = 1`; for another 2-adic field `ε` would be its absolute ramification index.
Let `E = F(δ)` with `δ = √2`, so `δ̄ = -δ` and `ω(δ) = 1/2`. Write `N` and `tr` for
the norm and trace of `E/F`.

**Group.** `G = SU(h)` for the hermitian form `h(x, y) = x̄ᵀ J y` with
`J = antidiag(1, 1, 1)`, so `G(F) = {g ∈ SL_3(E) : ḡᵀ J g = J}`. This is the
quasi-split SU_3 of `E/F` (KP §2.7, printed pp.108–109 / PDF pp.139–140). KP use
`J = antidiag(1, -1, 1)`, but every hermitian form in three variables is similar to
it, so the special unitary groups are isomorphic. Only the signs in the coordinates
below differ from KP's.

The relative root system is `BC_1 = {±a, ±2a}`.

**Root groups.**
- `U_a(F) = {u(α, β)}`, where `u(α, β) = [[1, α, β], [0, 1, -ᾱ], [0, 0, 1]]` and
  `tr β = -N(α)`.
- `U_{2a}(F)` is the subgroup `α = 0`, `β ∈ Fδ`.
- `U_{-a}(F) = {u⁻(p, q)}`, where `u⁻(p, q) = [[1, 0, 0], [p, 1, 0], [q, -p̄, 1]]` and
  `tr q = -N(p)`.
- `U_{-2a}(F)` is the subgroup `p = 0`, `q ∈ Fδ`.

**Torus and its filtration.**
- `Z = T`, with `T(F) ≅ E^×` via `t(γ) = diag(γ, γ̄/γ, 1/γ̄)`.
- `Z(F)^0 = t(O_E^×)`.
- For `M ≥ 0`, `T_M := t(1 + 𝔭_E^{≥M})`, where `𝔭_E^{≥M} = {y : ω(y) ≥ M}` and
  `T_0 := t(O_E^×)`. This is KP's filtration `T(k)_r` (§3.2(a), printed p.148 /
  PDF p.179). It is also the minimal congruent filtration of the induced torus `T`
  (Definition 7.2.2(2), printed p.245 / PDF p.276).

**Normalizer.** `N(F) = T(F) ∪ w T(F)`, where `w = antidiag(1, -1, 1) ∈ G(F)`.
Conjugation by `w` sends `t(γ)` to `t(1/γ̄)` and exchanges `U_{±a}` and `U_{∓a}`.

**Valuation.** We use
- `φ_a(u(α, β)) = ω(β)/2` and `φ_{2a}(u(0, β)) = ω(β)`;
- `φ_{-a}(u⁻(p, q)) = ω(q)/2` and `φ_{-2a}(u⁻(0, q)) = ω(q)`.

KP's (3.2.3) (printed p.149 / PDF p.180) is `φ_a = (ω(v) - μ)/2`, where
`μ = sup{ω(x) : tr x = 1}`. The elements of trace 1 are `1/2 + bδ` with `b ∈ F`. The
valuations `ω(1/2) = -1 ∈ Z` and `ω(bδ) = ω(b) + 1/2 ∈ Z + 1/2` never coincide, so
`ω(1/2 + bδ) = min(-1, ω(b) + 1/2) ≤ -1`, with equality at `b = 0`. Hence `μ = -1`.
So our `φ` is KP's valuation translated by a vector `v` with `a(v) = μ/2`. That makes it
a point of the standard apartment.

The normalization on `U_{-2a}` fits Axiom V 5. For `u = u(0, β)`, the product
`u⁻(0, -1/β) · u · u⁻(0, -1/β)` is antidiagonal, and
`φ_{-2a}(u⁻(0, -1/β)) = -φ_{2a}(u)`.

**Point.** At the point `x` with shift `θ`, the depths are
- `x_a = ω(β)/2 + θ` and `x_{2a} = ω(β) + 2θ`;
- `x_{-a} = ω(q)/2 - θ` and `x_{-2a} = ω(q) - 2θ`.

Sums of opposite depths do not depend on `x`. The witnesses below use `θ = 0`.

## Commutator `Z`-components and the key inequality

**The `Z`-component.** Let `u = u(α, β)` and `u' = u⁻(p, q)`. The `(1,1)` entry of
`u u'` is `γ := 1 + αp + βq`. If `γ ≠ 0`, then `u u' = v'' t(γ) v'''`, with
`v'' ∈ U_{-a}(F)` and `v''' ∈ U_a(F)`. This is the SU(3) computation in the proof of
KP Proposition 7.1.1 (printed p.239 / PDF p.270), in KP's coordinates there
`γ = 1 + αα' + ββ'`. Hence

`u'⁻¹ u u' u⁻¹ = (u'⁻¹ v'') t(γ) (v''' u⁻¹) ∈ U_{-a}(F) · t(γ) · U_a(F)`.

So the `Z`-component of KP Definition 7.1.3 is `t(γ)`. This is the `z` of
`CentralizerFiltration.IsCommutatorFriendly`. It is unique, by
`ParahoricBuildingData.oppositeRootTripleProduct_injective`.

For the root `-a`, the roles swap: `u = u⁻(p, q) ∈ U_{-a}` and `u' = u(α, β) ∈ U_a`.
Then `u'⁻¹ u u' u⁻¹ ∈ U_a(F) · t(γ') · U_{-a}(F)`, where
`γ' = 1/conj(1 + d)` with `d := qβ + p̄ᾱ`, read off from the `(3,3)` entry of `u u'`.
Then `γ' - 1 = -conj(d)/conj(1 + d)`, so in general
`ω(γ' - 1) = ω(d) - ω(1 + d)`. This equals `ω(d)` only when `1 + d` is a unit, which
holds for positive depth sums (see below). Equivalently, conjugate the first case by
`w`.

**Key inequality.** Write `β = β_0 + β_1δ` with `β_i ∈ F`. Then `tr β = 2β_0 = -N(α)`.
Hence

`2ω(α) = ω(N α) = ε + ω(β_0) ≥ ε + ω(β)`,

that is, `ω(α) ≥ φ_a(u) + ε/2`. Likewise `ω(p) ≥ φ_{-a}(u') + ε/2`.

Let `σ := φ_a(u) + φ_{-a}(u') > 0` be the depth sum. Then `ω(αp) ≥ σ + ε` and
`ω(βq) = 2σ`, so every `±a` pair satisfies

`ω(γ - 1) ≥ min(σ + ε, 2σ)`.  (∗)

For the root `-a`, the same two estimates apply to the two terms of `d = qβ + p̄ᾱ`, with
`σ = φ_{-a}(u) + φ_a(u') > 0`. So `ω(d) ≥ min(σ + ε, 2σ) > 0`. Hence `1 + d` is a unit,
`ω(γ' - 1) = ω(d)`, and (∗) holds for `γ'` too.

For a `±2a` pair, `α = p = 0` and `β, q ∈ Fδ`, so `βq ∈ F` and
`γ = 1 + βq ∈ 1 + F`. In that case `ω(γ - 1) = σ'`, where
`σ' = φ_{2a}(u) + φ_{-2a}(u')`. For the root `-2a`, `γ' = 1/(1 + qβ) ∈ 1 + F`. If
`σ' > 0`, then `1 + qβ` is a unit, so again `ω(γ' - 1) = σ'`.

## The minimal filtration `Z'`

For a depth sum `r > 0`, the *forced components* are the `Z`-components `t(γ)` of the
pairs that `IsCommutatorFriendly` covers with sum exactly `r`. These range over all
points `x`, all four roots and all `u ≠ 1`, `u' ≠ 1`. Define:

- `Z'_r` (`r > 0`) is the subgroup of `T(F)` generated by the `N(F)`-conjugates of all
  forced components with sum `≥ r`;
- `Z'_0 := Z(F)^0 = t(O_E^×)`.

By (∗), a `±a` component with sum `σ ≥ r` lies in
`T_{min(σ+ε, 2σ)} ⊆ T_{min(r+ε, 2r)} ⊆ T_r`. A `±2a` component with sum `σ ≥ r` lies in
`t(1 + 𝔭_F^{≥σ}) ⊆ t(1 + 𝔭_F^{≥r}) ⊆ T_r`. Both of these groups are stable under
`γ ↦ 1/γ̄`, which is conjugation by `w`. Hence `Z'_r ⊆ T_r` for all `r ≥ 0`, and more
precisely

`Z'_r ⊆ t(1 + 𝔭_F^{≥r}) · T_{min(r+ε, 2r)} ⊆ t(F^×) · T_{min(r+ε, 2r)}`  for `r > 0`.  (∗∗)

The right-hand sides are subgroups of the abelian group `T(F)`, stable under `N(F)`.

## `Z'` satisfies every published axiom

These are the fields of `ParahoricBuildingData.CentralizerFiltration` and the four
conjuncts of `SatisfiesFiltrationAxioms` in module `KPMoyPrasadFiltration`.

- **`filtration_zero`**: `Z'_0 = Z(F)^0` by definition. `Z(F)^0 = t(O_E^×)` for the
  induced torus `T` (KP printed p.148, `T(k)_0 = O_𝓁^×`).
- **`antitone`**: `Z'_r` shrinks as `r` grows, by definition. For `r > 0`,
  `Z'_r ⊆ T_r ⊆ T_0 = Z'_0`.
- **`separated`**: `⋂_r Z'_r ⊆ ⋂_r T_r = {1}`.
- **`IsCommutatorFriendly`**: holds by construction. A pair with sum exactly `r > 0`
  has its component in `Z'_r`.
- **`IsNormalizerStable`**: `Z'_r` is generated by an `N(F)`-stable set for `r > 0`.
  `t(O_E^×)` is stable under `t(γ) ↦ t(1/γ̄)` and under `T(F)`. Equality of the images
  follows by applying the same inclusion to `n⁻¹`.
- **`IsCommutatorFiltered`**: `T(F)` is abelian, so `[Z'_r, Z'_s] = 1`.
- **`IsRootCompatible`**: since `Z'_r ⊆ T_r`, it suffices to treat `t(γ)` with
  `ω(γ - 1) ≥ r` (a unit `γ` when `r = 0`) and `u = u(α, β) ∈ U_{a,x,s}` with `s ≥ 0`.
  Put `λ = γ²/γ̄` and `μ' = γγ̄`, so `ω(λ - 1) ≥ r` and `ω(μ' - 1) ≥ r`. Then
  - `t(γ) u t(γ)⁻¹ u⁻¹ = u(α', β')`, where `α' = (λ - 1)α` and
    `β' = (μ' - 1)β + (λ - 1)N(α)`.
  - Split `u(α', β') = u(α', β'') · u(0, β''')` with `β'' := -N(α')/2` and
    `β''' := β' - β'' ∈ Fδ`. The product formula is
    `u(α_1, β_1) u(α_2, β_2) = u(α_1 + α_2, β_1 + β_2 - α_1 ᾱ_2)`.
  - The `a`-factor is deep enough. By the key inequality,
    `ω(β'')/2 = ω(α') - ε/2 ≥ r + ω(α) - ε/2 ≥ r + ω(β)/2`. Since
    `ω(β)/2 + θ ≥ s`, this gives `u(α', β'') ∈ U_{a,x,r+s}`.
  - The `2a`-factor is deep enough. We have `ω(β') ≥ r + ω(β)`, because
    `2ω(α) ≥ ω(β)`, and `ω(β'') ≥ 2r + ω(β)`. So
    `ω(β''') + 2θ ≥ r + ω(β) + 2θ ≥ r + 2s ≥ r + s`, and
    `u(0, β''') ∈ U_{2a,x,r+s}`.
  - For `±2a`, the commutator is `u(0, (μ' - 1)β)`. The root `-a` follows by
    conjugation by `w`.

  So the commutator lies in the block `U_{a,x,r+s} U_{2a,x,r+s}`.

## Witness against `MoyPrasadCommutatorStatement`

Let `P'_{x,r} := Zf.moyPrasad x r` for `Zf = Z'`, at `θ = 0`. Take `r = s = 1/2` and

- `u := u(0, √2) ∈ U_{2a,x,1/2}`, since `φ_{2a}(u) = ω(√2) = 1/2`;
- `u' := u⁻(2, -2) ∈ U_{-a,x,1/2}`. Here `tr(-2) = -4 = -N(2)` and
  `φ_{-a}(u') = ω(-2)/2 = 1/2`.

Both elements lie in `P'_{x,1/2}`. Then `h := u'⁻¹ u u' u⁻¹ = ⁅u'⁻¹, u⁆` lies in
`⁅P'_{x,1/2}, P'_{x,1/2}⁆`.

**The `Z`-component of `h`.** It is `t(γ)` with `γ = 1 + δ·(-2) = 1 - 2√2`, so
`ω(γ - 1) = 3/2`.

**This component is not in `Z'_1`.** By (∗∗), `Z'_1 ⊆ t(F^×) · T_2`. Suppose
`1 - 2√2 = c(1 + y)` with `c ∈ F^×` and `ω(y) ≥ 2`. Write `y = y_0 + y_1√2`. Since
`ω(y) = min(ω(y_0), ω(y_1) + 1/2)` and `ω(F^×) = Z`, we get `ω(y_0) ≥ 2` and
`ω(y_1) ≥ 2`.
- The `F`-parts give `c(1 + y_0) = 1`, so `c` is a unit.
- The `√2`-parts give `c·y_1 = -2`, so `ω(y_1) = 1`.

This is a contradiction.

**Hence `h ∉ P'_{x,1}`.** Suppose `h ∈ P'_{x,1}`. Choose a generic cocharacter `mu`
with `a` positive. By `CentralizerFiltration.moyPrasad_eq_negative_image_positive`
(module `MoyPrasadGlobalExchange`; it needs only `hP` and `IsCommutatorFriendly`),
`h = n · z · q` with `n ∈ U_{-a}(F)`, `z ∈ Z'_1` and `q ∈ U_a(F)`. Also
`h = v' t(γ) v` with `v' ∈ U_{-a}(F)` and `v ∈ U_a(F)`. By
`ParahoricBuildingData.oppositeRootTripleProduct_injective` (module `MoyPrasadDoubleRefinement`),
`z = t(γ) ∉ Z'_1`. This is a contradiction.

Therefore `⁅P'_{x,1/2}, P'_{x,1/2}⁆ ⊄ P'_{x,1}`.

The same computation works for any 2-adic `F` with `E = F(√ϖ)`, where `ϖ` is a
uniformizer of `F`: take `u = u(0, √ϖ)` and `u' = u⁻(2, -2)`, so `r = 1/2` and
`s = ε/2`. Then `ω(γ - 1) = ε + 1/2 < ε + 1`, while
`Z'_{r+s} ⊆ t(F^×) · T_{1+ε}`. More generally, the failure occurs for `u ∈ U_{2a}` and
`u' = u⁻(p, f_0)` with `f_0 ∈ F`, taking `r = x_{2a}(u)` and `s = x_{-a}(u')`, whenever
`r > 0` and `s < ε`. The `Z`-component `1 + βf_0` has `δ`-part of valuation `r + 2s`, which
is below `min(r + s + ε, 2r + 2s)`.

## Witness against `MoyPrasadCovarianceStatement` (Task 5511)

Keep `u = u(0, √2) ∈ U_{2a,x,1/2}` and take `u'' := u⁻(√2, 1)`. Here
`tr 1 = 2 = -N(√2)` and `φ_{-a}(u'') = 0`, so `u'' ∈ U_{-a,x,0}`. The element
`u''⁻¹ u u''` has `Z`-component `t(1 + √2)`, of depth `1/2`.

Suppose `t(1 + √2) ∈ Z'_{1/2} ⊆ t(F^×) · T_1`, that is, `1 + √2 = c(1 + y)` with
`c ∈ F^×` and `ω(y) ≥ 1`. The `F`-parts make `c` a unit. The `√2`-parts give
`c·y_1 = 1`, so `ω(y_1) = 0`. But `ω(y) ≥ 1` forces `ω(y_1) ≥ 1`, a contradiction.

As above, it follows that `u''⁻¹ u u'' ∉ P'_{x,1/2}`. Now set
`Q := P'_{x,1/2}` and `Q' := u'' Q u''⁻¹`.
- `u''` fixes the image `[x]` of `x` in `P.ReducedBuilding`. This holds for the
  Library's quotient, not only for the actual building.
  `KPApartmentData.filtration_le_sharpFixer` (module `ChamberRankOne`) gives
  `U_{-a,x,0} ≤ G(F)^♯_x`. The reduced building is the quotient by the family
  `x ↦ G(F)^♯_x` (`KPApartmentData.sharpFixerFamily`), so
  `ApartmentQuotient.mk_eq_mk_iff` with `n = 1` gives `u'' • [x] = [x]`.
  Worker 45 pointed this out.
- So both `Q` and `Q'` satisfy `IsMoyPrasadAt [x] (1/2)`: use `g = 1` for `Q` and
  `g = u''` for `Q'`. Here `IsMoyPrasadAt` is `CentralizerFiltration.IsMoyPrasadAt`
  (module `KPMoyPrasadFiltration`).
- `u ∈ Q` but `u ∉ Q'`, so `Q ≠ Q'`.

So the parahoric subgroup `P_x`, which contains `u''`, does not normalize
`P'_{x,1/2}`, and the Covariance target fails.

The same pair also violates the hypothesis `hmixed` of
`CentralizerFiltration.sharpFixer_le_normalizer_moyPrasad_of_double_opposite_bound`
(module `MoyPrasadCovarianceReduction`), taken at the root `-a` with `r = 1/2`:
`u''⁻¹ ∈ U_{-a,x,0}` and `u ∈ U_{2a,x,1/2}`, but `u''⁻¹ u u'' ∉ P'_{x,1/2}`. This
matches the normality step of KP Proposition 7.3.17 (printed p.252 / PDF p.283), which
has the analogous gap.

## Odd residue characteristic

Let `p` be odd and `E/F` any quadratic extension, so `ε = ω(2) = 0`. Then the forced
filtration equals the actual one: `Z'_r = T_r` for all `r > 0`. So this construction gives
no counterexample.

- **`Z'_r ⊆ T_r`**: the key inequality holds with `ε = 0`, since
  `ω(N α) = ω(tr β) ≥ ω(β)`. So (∗) reads `ω(γ - 1) ≥ min(σ, 2σ) = σ`.
- **`T_r ⊆ Z'_r`**: given `z` with `ω(z) ≥ r > 0`, solve `x + N(x)/4 = z`. The map
  `x ↦ z - N(x)/4` is a contraction on `{ω(x) ≥ ω(z)}`, and the solution has
  `ω(x) = ω(z)`. Take `u = u(1, -1/2)` and `u' = u⁻(x, -N(x)/2)`. Their depth sum is
  `0 + ω(N(x))/2 = ω(x)`, and `γ = 1 + x + N(x)/4 = 1 + z`. So every `t(1 + z) ∈ T_r` is
  itself a forced component of depth `≥ r`.

For `p = 2`, the same choice has depth sum only `ω(x) - ε`, which is where the loss
comes from.

## Scope

- **`IsDoubleRootCommutatorFriendly` fails for `Z'`.** It would require
  `t(1 - 2√2) ∈ Z'_{3/2}`, because the pair above has `a`-depth sum `1/4 + 1/2 = 3/4`.
  KP's `T_r` satisfies it at this pair, since `ω(γ - 1) = 3/2`. So the double-root
  variants (Tasks 5645 and 5646) are not affected.
- **KP's book is not refuted.** KP Lemma 7.2.3 (printed p.245 / PDF p.276) uses the
  minimal congruent filtration `T_r`, not an arbitrary commutator-friendly one. The
  published axioms admit `Z'`, which is strictly smaller than `T_r` when `p = 2`.
- **What a correct supplied-data target needs.** It needs a premise at least as
  strong as `IsDoubleRootCommutatorFriendly`, or a filtration fixed by its
  construction (KP §9.8), rather than only the four axioms.
- **Source and corrections.** The source proof (Proposition 13.2.5, printed p.469 /
  PDF p.500, through Lemma 7.1.2 at printed p.240 / PDF p.271 and Definition 7.2.1 at
  printed p.245 / PDF p.276) bounds the `U_{2a} × U_{-a}` component only at `r/2 + s`.
  The authors' corrections (version of 1 November 2024) have no entry for Lemma 7.1.2,
  Definition 7.2.1, Proposition 7.3.17 or Proposition 13.2.5.

## Sources

- `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`: §2.7
  (printed pp.108–109); §3.2(a)–(b) and (3.2.3) (printed pp.148–149); proof of
  Proposition 7.1.1 for quasi-split `G` (printed p.239); Lemma 7.1.2 (printed p.240);
  Definition 7.1.3 (printed p.242); Definitions 7.2.1–7.2.2 and Lemma 7.2.3 (printed
  p.245); Proposition 7.3.17 (printed p.252); Proposition 13.2.5 (printed p.469). The
  PDF page is the printed page plus 31.
- `kaletha-prasad-2024-corrections`, SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`: checked for
  entries on the items above; there are none.

## Reproducing the matrix arithmetic

The following script checks two things with exact arithmetic in `Q(√2)`. First, that
`u`, `u'` and `u''` are `J`-unitary. Second, that `h` and `u''⁻¹ u u''` factor as
lower unipotent × `t(γ)` × upper unipotent with unitary factors, for `γ = 1 - 2√2` and
`γ = 1 + √2` respectively. It prints `all checks passed`. The valuation estimates above
are by hand.

```python
from fractions import Fraction as Q
# x = (x0, x1) stands for x0 + x1*sqrt(2) in Q(sqrt 2); conj(x) = (x0, -x1)
def ad(x, y): return (x[0] + y[0], x[1] + y[1])
def ng(x): return (-x[0], -x[1])
def ml(x, y): return (x[0]*y[0] + 2*x[1]*y[1], x[0]*y[1] + x[1]*y[0])
def cj(x): return (x[0], -x[1])
def nm(x): return x[0]*x[0] - 2*x[1]*x[1]
def iv(x): return (Q(x[0]) / nm(x), Q(-x[1]) / nm(x))
def e(a, b=0): return (Q(a), Q(b))
O, Z = e(1), e(0)
def mm(A, B): return [[ad(ad(ml(A[i][0], B[0][j]), ml(A[i][1], B[1][j])), ml(A[i][2], B[2][j]))
                       for j in range(3)] for i in range(3)]
J = [[Z, Z, O], [Z, O, Z], [O, Z, Z]]
def star(A): return [[cj(A[j][i]) for j in range(3)] for i in range(3)]
def unitary(A): return mm(mm(star(A), J), A) == J
def inv(A): return mm(mm(J, star(A)), J)        # inverse of a J-unitary matrix
def up(al, be): return [[O, al, be], [Z, O, ng(cj(al))], [Z, Z, O]]   # u(al, be)
def lo(p, q): return [[O, Z, Z], [p, O, Z], [q, ng(cj(p)), O]]       # u^-(p, q)
def t(g): return [[g, Z, Z], [Z, ml(cj(g), iv(g)), Z], [Z, Z, iv(cj(g))]]
def ldu(h):       # Gaussian elimination: h = L * diag(D) * U, L lower and U upper unipotent
    L = [[O if i == j else Z for j in range(3)] for i in range(3)]; R = [row[:] for row in h]
    for k in range(3):
        for i in range(k + 1, 3):
            f = ml(R[i][k], iv(R[k][k])); L[i][k] = f
            R[i] = [ad(R[i][j], ng(ml(f, R[k][j]))) for j in range(3)]
    D = [R[i][i] for i in range(3)]
    U = [[ml(R[i][j], iv(D[i])) for j in range(3)] for i in range(3)]
    return L, D, U
def check(h, g):  # the Z-part of h in U_{-a} Z U_a is t(g), with unitary unipotent factors
    L, D, U = ldu(h)
    return D == [t(g)[i][i] for i in range(3)] and unitary(L) and unitary(U)
u, u1, u2 = up(Z, e(0, 1)), lo(e(2), e(-2)), lo(e(0, 1), e(1))
assert unitary(u) and unitary(u1) and unitary(u2)
h1 = mm(mm(mm(inv(u1), u), u1), inv(u))       # witness for the commutator statement
assert check(h1, e(1, -2))
h2 = mm(mm(inv(u2), u), u2)                    # witness for the covariance statement
assert check(h2, e(1, 1))
print("all checks passed")
```
