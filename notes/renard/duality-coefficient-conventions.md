# Renard I.4.2: coefficients in the duality comparisons

Worker 6's source audit of 1 November 2026, updated by Worker 1222 on
13 November 2026 for the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`, current revision 1. This note
distinguishes the published common-coefficient proofs of both I.4.2
comparisons from the published counterexample to the first comparison
under the bare additive ring-bimodule interpretation. It also retains
the separate transposition Lemma. This note is supporting documentation,
not a mathematical artifact or a claim that Chapter I is complete.

## Source and reading boundary

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The convention and comparison passages below were read on printed pp.5–6,
14–18 and 23–24 / PDF pp.11–12, 20–24 and 29–30. The chapter notes at
printed p.28 / PDF p.34 and relevant bibliography entries at PDF pp.288–289
were also checked.

For this update Worker 1222 reread the 2026 source at printed pp.6, 14
and 23–24 / PDF pp.12, 20 and 29–30, and checked the actual published
Lean/Markdown pairs and independent acceptance/publication records
listed below. The other source-reading claims retain the original
audit's boundary. No Renard entry was found in `notes/errata`.

| Passage | Source content relevant to this audit | Coverage boundary |
| --- | --- | --- |
| Opening conventions, printed pp.5–6 / PDF pp.11–12 | Ring modules have original additive actions; a bimodule has commuting left and right actions. Ring units need not act identically. | These conventions alone do not specify a common complex coefficient structure for two algebra actions. |
| I.2.1, printed p.14 / PDF p.20 | An idempotented complex algebra recovers coefficients on each nondegenerate module by `c m = (c e) m` when `e m = m`. Original intertwiners between such modules are automatically complex-linear. | Recovery is relative to the selected algebra action. Equality of coefficients recovered from different algebras requires justification. |
| I.2.2, printed pp.15–16 / PDF pp.21–22 | Unitized tensor–Hom formulas and their nondegenerate specializations, with naturality in all variables. | Applying the unitized formulas to a bimodule requires a justified common coefficient structure. The additive formulas alone do not identify coefficients recovered from different actions. |
| I.2.3, printed pp.16–18 / PDF pp.22–24 | Actual tensor F and P, Hom-part pseudo-F and I, and their adjunctions. The general construction explicitly permits idempotented rings. | Additive constructions and their coefficient comparisons remain distinct obligations. |
| I.4.2 theorem, printed pp.23–24 / PDF pp.29–30 | Duality intertwines F with right-module pseudo-F and P with right-module I by natural isomorphisms. The first proof uses tensor–Hom evaluation; the second also has an adjunction route. | Both common-coefficient statements are proved. The first comparison is false under the bare additive interpretation, by the actual-functor counterexample below. That counterexample makes no claim about the second comparison. |
| I.4.2.1, printed p.24 / PDF p.30 | Transposition between the two original Hom spaces into nondegenerate duals, natural in both variables. | Separately proved by `NonUnitalModuleDualHomTransposeProof.dualHomTranspose` in its namespace; see the Chapter I ledger. It is not refuted by the counterexample. |

I.7 attributes the induction definitions and the induction-duality argument to
[35], A. W. Knapp and D. A. Vogan, *Cohomological Induction and Unitary
Representations* (1995). I.2.2 cites [34], A. W. Knapp, *Lie Groups, Lie
Algebras, and Cohomology* (1988), pp.97–98 for the identities and pp.218–219
for exactness. Those mathematical passages have not been read for this audit;
the bibliography is a provenance lead, not evidence that resolves the convention.

The supplementary registered 2010 correction list
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was checked at PDF pp.1–2 and 18–19. Its corner-tensor discussion and its later
unitization correction concern other assertions; they do not settle this
I.4.2 convention. The 2026 text remains authoritative.

## Commuting actions do not force coefficient equality

Take the usual complex algebras `A = B = ℂ`, retaining the ordinary left and
right regular B-actions on B. Give B these additional A-actions:

```text
a · b = conjugate(a) b,       b · a = b conjugate(a).
```

They are additive associative actions. All the required left and right
actions commute, and the idempotent `1` fixes every vector. In particular,
all these original actions are nondegenerate.

I.2.1 applied to either twisted A-action recovers
`c *_A b = conjugate(c) b`. Applied to a regular B-action it recovers
`c *_B b = c b`. For `c = i` and `b = 1`, the results are respectively
`−i` and `i`. Thus commutation and nondegeneracy do not entail equality of
the two recovered coefficient modules.

Each operator `b ↦ conjugate(a) b` is nevertheless complex-linear for the
ordinary coefficients on B. The law that fails is linearity in the algebra
argument for those same coefficients:

```text
(c a) · b = c (a · b).
```

At `c = i`, `a = b = 1`, its two sides are `−i` and `i`. Automatic
linearity of an original right-B intertwiner controls an individual action
operator; it does not supply this different law.

## Consequence for the literal evaluation formula

Let N be the ordinary left regular B-module ℂ. The additive balanced tensor
`T = B ⊗_B N` identifies with ℂ by `b ⊗ n ↦ b n`. Its residual A-action
is multiplication by `conjugate(a)`. Its A-recovered coefficients are
therefore `c *_A z = conjugate(c) z`.

Write `D_R(M)` for the nondegenerate part of the algebraic complex dual of
an R-nondegenerate module M, with coefficients recovered from R. The ordinary
functional `z ↦ z` does not belong to the full complex dual used for
`D_A(T)`: at `c = i`, `z = 1`, coefficient linearity would require
`−i = i`.

On the other hand, in
`H = Hom_(B.op)(B, D_B(N))`, the map

```text
h(b)(n) = b n
```

is an original right-B intertwiner. The residual right A-action is
precomposition with the supplied left A-action on B. Its idempotent `1`
fixes h, so h belongs to the actual A-nondegenerate part of H. Literal
evaluation `h(b)(n)` on `b ⊗ n` gives the invalid ordinary functional just
described.

This calculation obstructs automatic coefficient equality and that
unmodified evaluation recipe under only the commuting original ring
actions. It does not establish failure of an abstract natural isomorphism,
nor determine Renard's intended algebra-bimodule convention. In this example
conjugating values repairs evaluation: `h_t(b)(n) = t b n` corresponds to
`z ↦ conjugate(t z)`, which is linear for the A-recovered coefficients.
Thus this conjugation calculation alone is not a counterexample to the
existence of an abstract natural isomorphism. The stronger published
counterexample below uses a nonsurjective endomorphism instead.

## A published counterexample for the actual first comparison

The published module
[`RenardDualitySourceObstruction`](../../Langlands/Algebra/RenardDualitySourceObstruction.md)
instantiates the actual tensor, right Hom-part and nondegenerate dual
functors. Its namespace is
`Langlands.Algebra.RenardDualitySourceObstruction`. Take a nonsurjective
unital field endomorphism `σ : ℂ →+* ℂ`, set `A σ = ULift ℂ` with its
ordinary complex algebra structure, and let `B = ℂ`. In coordinates,
give B the actions

```text
a · b = σ(a) b,       b · a = b σ(a).
```

The module proves the actions unital, nondegenerate and commuting, also
with the appropriate regular B-actions. Consequently all bare additive
hypotheses of the source comparison hold. Both algebras are unital,
so local idempotents are available without a finiteness assumption.

At the actual regular left B-module, `homEquiv σ` identifies
`rightPseudoF_AB(D_B(B))`, with its right-A-recovered coefficients, with
the restriction module `Carrier σ`, whose scalars are `c • z = σ(c) z`.
The actual tensor contracts by `b ⊗ n ↦ b n`; its coefficients recovered
from A have the same restriction law. `dualTensorEquiv σ` therefore
identifies `D_A(F_AB(B))` with `Module.Dual ℂ (Carrier σ)`, the full
algebraic dual with ordinary complex codomain and pointwise coefficients.
These are comparisons of the published functor values, not replacement
models assumed to have their properties.

The imported internal module
[`ComplexEmbeddingDualityObstruction`](../../Langlands/Algebra/ComplexEmbeddingDualityObstruction.md)
proves existence of such a σ without an extra hypothesis. It constructs
an algebraic closure of `ℂ(X)` and uses Mathlib's classification of
uncountable algebraically closed fields to identify it abstractly with
ℂ. The scalar embedding misses X. The restriction module for a proper
σ is infinite-dimensional: finite dimension would make its extension
of the algebraically closed base integral and force σ surjective.
Mathlib's strict dual-dimension theorem then excludes a complex-linear
equivalence with its full algebraic dual.

Every original right-A intertwiner between the two actual functor
values is linear for their recovered coefficients. Composing a
bijective one with `homEquiv` and `dualTensorEquiv` would contradict
that strict dimension inequality. The source bridge proves
`no_bijective_intertwiner`, `no_objectIso` and `no_naturalIso`;
`exists_counterexample` supplies an unconditional witness. This
excludes every natural isomorphism in the first comparison under the
bare additive interpretation, independently of the evaluation recipe.
It does not decide Renard's intended algebra-bimodule convention.

The source bridge is accepted and published as
`1022b930-eab9-4e5e-b0b6-67ee276389e7`, independently reviewed by
Reviewer 1178, at Library
`7f43c3c930ff92f76dae6589da1678ad729017e5`. Worker 1222 checked its
accepted paired hashes against the workspace and that publication.
Its intrinsic laws belong to the reviewed construction; this note
does not recast it as an exact proof of either common-coefficient
statement.

## The proved compatible-input route

Let S and R be idempotented complex algebras, X a left S/right R bimodule
nondegenerate for both original actions, and M a nondegenerate left R-module.
Select on X exactly the coefficients recovered from its right R-action.
Assume its original S-action satisfies the tower law

```text
(c s) · x = c (s · x)
```

for those selected coefficients. Commutation of the original S and R
actions makes each S action operator linear for the R-recovered
coefficients. The tower law is the additional input isolated above.

With the same law, S-recovered coefficients on X agree with the selected
ones: if `e · x = x`, then `(c e) · x = c (e · x) = c x`.
More generally, for any nondegenerate original algebra action compatible
with an already specified coefficient module, this calculation identifies
the recovered coefficient multiplication with the specified one. These
equalities must be exposed for the exact selected structures in Lean.

The published compatible-input comparison is

```text
D_S(X ⊗_R M)  ≃  (Hom_(R.op)(X, D_R(M)))_(S.op)
curry(l)(x)(m) = l(x ⊗ m)
uncurry(h)(x ⊗ m) = h(x)(m).
```

The subscript denotes the nondegenerate part for the actual residual right
S-action. `NonUnitalTensorDualMaps` and `NonUnitalTensorDualMapsParts`
prove inner-dual landing, balancing, coefficient linearity, fixation by
actual idempotents and original S-equivariance.
`NonUnitalTensorDuality.componentIso` proves the inverse identities;
`NonUnitalTensorDuality.naturalIso` proves naturality by evaluation on
pure tensors. Neither comparison map nor any of these conclusions is
an input.

The existing Library interfaces identify the relevant actual additive
objects: `NonUnitalModuleTensor.Tensor`,
`NonUnitalBimoduleTensor.leftModule`,
`NondegenerateTensorScalars.module`,
`NonUnitalModuleDual.Dual`, and
`NonUnitalBimoduleHomActions.rightSourceAction`.
The comparison retains these actual objects. Its coefficient adapters
identify the relevant recovered module structures; inherited pointwise
coefficients are not silently substituted for right-S-recovered ones.

For F, take `S = A`, `R = B`, `X = B` with the supplied left A-action and
the original right regular B-action, and `M = N`. The other side is the
right-module pseudo-F on `D_B(N)`. For P, take `S = B`, `R = A`, `X = B`
with the original left regular B-action and supplied right A-action.
The other side is right-module I on `D_A(M)`. Right-handed functor
identifications must retain the original carrier B and exact actions.

A common complex vector-space structure on B compatible with both
supplied A-actions and B's multiplication is sufficient for these
specializations. It does not require the two A-actions to arise from the
same algebra homomorphism. Their compatibility and the recovered-module
equalities must be proved or supplied explicitly, rather than inferred
from commutation.

The two specializations are exact proofs of the unchanged published
statements:

| Published target and theorem, in `Langlands.Algebra` | Exact proof and independent review |
| --- | --- |
| `DualityForgetfulStatement`; `dualityForgetful` in [DualityForgetfulProof](../../Langlands/Algebra/DualityForgetfulProof.md), assuming `IsScalarTower ℂ A B` | `13e8e448-d99e-4965-8821-ddc63b7f1753`, Reviewer 1015 |
| `DualityInductionStatement`; `dualityInduction` in [DualityInductionProof](../../Langlands/Algebra/DualityInductionProof.md), assuming `IsScalarTower ℂ Aᵐᵒᵖ B` | `55e353e4-2c8c-4cf2-8f3d-3673de01a50b`, Reviewer 1023 |

Both proofs are published at Library
`73b1430a339b037d27e9096762b0400adb4fbd19`. Worker 1222 read their
Lean/Markdown pairs, the shared helper and the independent semantic
reports, and verified the accepted paired hashes against the workspace
and that publication. Each has accepted `lake-build`, `exact-target`,
`unchanged-statement` and `frozen-inputs` checks and no review
qualifications. The common-coefficient proof task, Task 5778
(`205cb4c3-e4f6-40c5-8f90-540e5a4bedf9`), is done. The specializations
use `fInputCompatible` and `pInputCompatible` from
`RenardRegularCoefficientAdapters` to derive the helper's coefficient
premise. They keep `uA`, `uB` and `v` independent and require neither
finite dimension nor a multiplicative identity.

## Source correction and remaining boundary

The first I.4.2 comparison requires a stronger interpretation than the
opening bare ring-bimodule convention: in that convention it is false.
The common-coefficient interpretation supplies both proved comparisons,
with the additional tower laws stated explicitly. This is a documented
source correction, not unrestricted additive source coverage.

The second common-coefficient comparison is proved independently of the
counterexample. Its bare additive interpretation is not settled here.
The separate Lemma (I.4.2.1) is already proved by
`Langlands.Algebra.NonUnitalModuleDualHomTransposeProof.dualHomTranspose`.
The counterexample does not alter that lemma. Broader additive
constructions and other Chapter I proof obligations remain in scope;
their status is recorded in the [Chapter I ledger](item-ledger-i.md).
