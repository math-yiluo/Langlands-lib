# Renard IV.3.2 Remark: what one square-integrable coefficient gives without admissibility

Worker 4988, 17 November 2026, within Task 6678
(`cf5dbeda-85bf-4ad9-8db5-f2f1445f4dc8`).

This note analyses the open proof obligation
`Langlands.Renard.CompactRepresentation.SingleCoefficientSquareIntegrabilityStatement`
([statement](../../Langlands/Representation/MatrixCoefficient/SingleCoefficientSquareIntegrabilityStatement.md)).
It separates three kinds of claim. Section 2 gives proved steps (paper proofs, not
Lean). Section 3 gives an exact reformulation for discrete groups. Section 4 states the
remaining step. The note contains no Lean declaration or proof receipt. It does not
change the statement, the task or caveat C3 of the
[Chapter IV item ledger](item-ledger-iv.md). The general-scope proof gap recorded there
remains open.

## 1. Source and target

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques` (SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`). The relevant pages
are IV.3.1–IV.3.2, printed pp.99–100 / PDF pp.105–106. Chapter IV concerns a general t.d.
group, and IV.3.1 assumes it unimodular. The Remark on printed p.100 assumes a smooth
irreducible `(π, V)` with a unitary central character, without admissibility. It says
that one nonzero coefficient square-integrable modulo the centre suffices, and leaves
the "(facile)" proof to the reader. The Proposition that follows (an irreducible
essentially square-integrable representation is admissible) assumes the all-coefficients
condition. Its proof chooses a `K`-fixed smooth functional that takes the value 1 on an
infinite free family in `V^K`.

The Lean target quantifies over a Hausdorff locally compact totally disconnected group
`G`, a Haar measure `μ` on `G ⧸ Subgroup.center G` that is also right invariant, an
irreducible `π : SmoothRep ℂ G` and `c : UnitaryCentralCharacter π.representation`. From
one pair `ℓ : SmoothDual π.representation`, `x : π` with
`matrixCoefficient π.representation ℓ x ≠ 0` and `MemLp (c.coefficientNorm ℓ x) 2 μ`, it
concludes `MemLp (c.coefficientNorm m y) 2 μ` for every `m` and `y`. Here
`c.coefficientNorm m y` is `g ↦ ‖m (π g y)‖` descended to `G ⧸ Z(G)`, and smooth
functionals are those fixed by an open subgroup.

Below, `φ_{y,m}(g) = m(π(g) y)`, and "in L²" means that `|φ_{y,m}|`, viewed as a
function on `G/Z`, is in `L²(μ)`.

## 2. Proved steps (paper proofs)

**Step A (all vectors, fixed functional).** Assume `φ_{x,ℓ}` is nonzero and in L². Then
`φ_{y,ℓ}` is in L² for every `y ∈ V`.

*Proof.* The nonzero span of `π(G)x` is invariant, so by irreducibility it is all of
`V`. Moreover `φ_{π(h)x,ℓ}(g) = φ_{x,ℓ}(gh)`. Right translation by `hZ` preserves `μ`
because `μ` is right invariant, so each `|φ_{π(h)x,ℓ}|` is in `L²(μ)`. Since `L²(μ)` is a
vector space and `|φ_{Σ a_i π(h_i)x, ℓ}| ≤ Σ |a_i| |φ_{π(h_i)x,ℓ}|`, every `φ_{y,ℓ}` is
in L². ∎

Hence `A y := φ_{y,ℓ}` defines a linear map from `V` into the χ-equivariant functions in
`L²(G/Z, χ)`. It intertwines `π` with right translation, and it is injective, because
its kernel is an invariant subspace that does not contain `x`. Step A uses only
irreducibility, right invariance of `μ` and the central character. It does not use
admissibility.

**Step B (under the premise, the conclusion is equivalent to admissibility).**

- *Admissible implies the conclusion.* Let `W = span π̃(G) ℓ ⊆ Ṽ`. Fix an open compact
  `K`. For `λ ∈ W`, the average `e_K λ` is a finite combination of `π̃(k) λ`, so it lies
  in `W`. Restriction to `V^K` maps `W^K` into `(V^K)^*`. The image separates the points
  of `V^K`: if every `λ ∈ W^K` vanishes at `y ∈ V^K`, then
  `λ(y) = (e_K λ)(y) = 0` for all `λ ∈ W`, so `A y = 0` and `y = 0`. If `dim V^K < ∞`, a
  separating subspace of `(V^K)^*` is all of it. So for `m ∈ Ṽ^K` there is `m' ∈ W^K`
  with `m = m'` on `V^K`. Both are `K`-fixed, so `m(v) = m(e_K v) = m'(e_K v) = m'(v)`
  for all `v ∈ V`. Thus `Ṽ = W`. Every `m = Σ a_i π̃(g_i) ℓ` gives
  `φ_{y,m}(g) = Σ a_i φ_{y,ℓ}(g_i⁻¹ g)`, a combination of left translates of
  L²-functions from Step A. Left translation preserves the Haar measure `μ`, so every
  coefficient is in L². In this case the published admissible criterion
  `squareIntegrableCoefficientCriterion`
  ([proof](../../Langlands/Representation/MatrixCoefficient/SquareIntegrableCoefficientCriterionProof.md))
  also applies.
- *The conclusion implies admissibility.* This is Renard's Proposition, published as
  `essentiallySquareIntegrableAdmissible`
  ([proof](../../Langlands/Representation/Compact/EssentiallySquareIntegrableAdmissibleProof.md)).
  It consumes the all-coefficients condition, so it gives no initial admissibility input.

So, for irreducible `π` with one nonzero L² coefficient, the target conclusion holds if
and only if `π` is admissible.

## 3. Exact reformulation for discrete groups

A discrete group is a Hausdorff locally compact totally disconnected group, so it lies
within the target's scope. For discrete `G`: `{1}` is open compact, every linear
functional is smooth, `G/Z` is discrete, and `μ` gives every point the same mass
`μ({1}) > 0`, which makes it right invariant automatically.

**Lemma 3.1.** If `π` is irreducible and infinite-dimensional, some coefficient is not
in L².

*Proof.* Fix `y ≠ 0`. The orbit `π(G)y` spans `V`, so a maximal linearly independent
subset `B` of the orbit is a basis of `V`, and `B` is infinite. Let `m` be the linear
form equal to 1 on `B`. If `π(g)y, π(g')y ∈ B` and `gZ = g'Z`, the two vectors are
proportional, because `π(z)` is a scalar, so they are equal. Thus `|φ_{y,m}| = 1` at
infinitely many points of `G/Z`, and `φ_{y,m}` is not in L². ∎

**Lemma 3.2.** If a nonzero finite-dimensional subspace `F` of `ℓ²(G/Z, χ)` is invariant
under right translation, then `G/Z` is finite.

*Proof.* Take an orthonormal basis `f_1, …, f_n` of `F`. Right translation `R(g)` is
unitary on `F`, so `(R(g) f_i)_i` is again orthonormal. Hence
`Σ_i |f_i(g)|² = Σ_i |(R(g) f_i)(1)|²` equals `Σ_i |f_i(1)|² =: C` for every `g`.
Summing over `G/Z` with `μ({1}) = μ₀ > 0` gives `n = μ₀ · C · |G/Z|`. Since `n ≥ 1`,
`G/Z` is finite. ∎

**Proposition 3.3.** For discrete groups, the target is equivalent to:

> **(D)** For every group `G` and every unitary character `χ` of `Z(G)` with `G/Z(G)`
> infinite, the space `ℓ²(G/Z(G), χ)` of χ-equivariant square-summable functions,
> under right translation, has no algebraically simple `ℂ[G]`-submodule.

*Proof.* Suppose (D) holds, and `π` satisfies the premise for discrete `G`. By Step A, `A`
embeds `V` as a simple submodule of `ℓ²(G/Z, χ)`, with `χ = c`. By (D), `G/Z` is finite,
and every function on the finite measure space `G/Z` is in L². Conversely, let `S` be a simple submodule
with `G/Z` infinite. Right translation on `S` is a smooth irreducible representation with
unitary central character `χ`. The functional `ℓ = (f ↦ f(1))` has `φ_{f,ℓ} = f`, which is
nonzero and in L² for `f ≠ 0`. By Lemma 3.2, `S` is infinite-dimensional, so Lemma 3.1
contradicts the target. ∎

Untwisted form: when `Z(G) = 1`, transport (D) to the left regular action by inversion.
It then says that no nonzero projection `q` in the group von Neumann algebra `L(G)`
makes `ℂ[G] q` a simple left `ℂ[G]`-module. A simple `ℂ[G] f ⊆ ℓ²(G)` with annihilator
`I` gives the projection `q ∈ L(G)` onto `{h : I h = 0}`. If `ℂ[G] q` is simple, then
for every `a ∈ ℂ[G]` with `a q ≠ 0` there is `b ∈ ℂ[G]` with `b a q = q`, so `a q` is
bounded below on `q ℓ²(G)`.

**Cases of (D) with proofs.**

- *Locally finite `G/Z`.* Let `S = ℂ[G] f` be simple, write `Q = G/Z`, and let `ℂ^χ[Q]`
  denote the twisted group algebra through which `ℂ[G]` acts on `ℓ²(Q, χ)`. For a finite
  subgroup `H ⊆ Q`, let `q_H` be the projection of the finite-dimensional C*-algebra
  `ℂ^χ[H]` with annihilator `Ann_H(f) = ℂ^χ[H](1 − q_H)`. Then `f = q_H f`, the `q_H`
  decrease as `H` grows, and their infimum `q_∞` satisfies `q_∞ f = f ≠ 0`. Hence
  `dim ℂ^χ[H] f / |H| = τ(q_H) ≥ τ(q_∞) > 0`, where `τ` is the faithful trace. For any
  generator `w` of `S`, the ratio `dim ℂ^χ[H] w / |H|` is non-increasing in `H`, and for
  large `H` it does not depend on the choice of generator. Choose `w = e f ≠ 0`, where `e` is
  a minimal projection of `ℂ^χ[H₀]`. Then the ratio at `H₀` is
  `dim σ / |H₀| ≤ |H₀|^{-1/2}` for a simple module `σ`. Since `Q` has arbitrarily large
  finite subgroups, the limit is 0, which contradicts `τ(q_∞) > 0`.
- *Torsion-free `G` with `Z(G) = 1` and the analytic zero-divisor property.* The property
  is: `a f = 0` with `a ∈ ℂ[G] ∖ 0` and `f ∈ ℓ²(G)` forces `f = 0`, and it is a
  hypothesis here. Take `g ≠ 1` and `a = 1 − g`, and let `f ≠ 0`. Then `a f ≠ 0`. If
  `ℂ[G] f` were simple, `b a f = f` for some `b`. Then `(b a − 1) f = 0`, so `b a = 1`. Then `1 − λ(g)` would be invertible in the finite von Neumann
  algebra `L(G)`. That is false, because `λ(g)` has full circle spectrum, since `g` has
  infinite order.

## 4. The unresolved step

The target is equivalent to the following claim.

> An irreducible smooth representation of a unimodular t.d. group, with unitary central
> character and one nonzero coefficient square-integrable modulo the centre, is
> admissible.

For discrete groups this is exactly (D). The author knows no proof of (D) for all
groups and no counterexample. This note makes no claim about its status in the
literature. Approaches that do not close the gap:

- **Renard's admissibility argument with only `W = span π̃(G)ℓ`.** It needs a functional
  in `W^K` with prescribed values on infinitely many independent vectors of `V^K`.
- **Godement's square-integrability theory on the Hilbert closure of `A(V)`.** It
  requires topological irreducibility, and the closure of an algebraically simple dense
  submodule need not be topologically irreducible a priori.
- **Schur's lemma `End = ℂ`.** It needs countable dimension, which the target does not
  assume, and even with it no contradiction was found.

A Lean proof of the target would in particular prove (D) for every group in the
universe `u`.
