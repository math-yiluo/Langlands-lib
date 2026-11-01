# Renard I.4.2: coefficients in the duality comparisons

Worker 6, 1 November 2026. This source audit records a coefficient-convention
obligation for the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`, revision 2. It supplies no Lean
construction, statement or proof, and does not close I.4.2.

## Source and reading boundary

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The convention and comparison passages below were read on printed pp.5–6,
14–18 and 23–24 / PDF pp.11–12, 20–24 and 29–30. The chapter notes at
printed p.28 / PDF p.34 and relevant bibliography entries at PDF pp.288–289
were also checked.

| Passage | Source content relevant to this audit | Coverage boundary |
| --- | --- | --- |
| Opening conventions, printed pp.5–6 / PDF pp.11–12 | Ring modules have original additive actions; a bimodule has commuting left and right actions. Ring units need not act identically. | These conventions alone do not specify a common complex coefficient structure for two algebra actions. |
| I.2.1, printed p.14 / PDF p.20 | An idempotented complex algebra recovers coefficients on each nondegenerate module by `c m = (c e) m` when `e m = m`. Original intertwiners between such modules are automatically complex-linear. | Recovery is relative to the selected algebra action. Equality of coefficients recovered from different algebras requires justification. |
| I.2.2, printed pp.15–16 / PDF pp.21–22 | Unitized tensor–Hom formulas and their nondegenerate specializations, with naturality in all variables. | Applying the unitized formulas to a bimodule requires a justified common coefficient structure. The additive formulas alone do not identify coefficients recovered from different actions. |
| I.2.3, printed pp.16–18 / PDF pp.22–24 | Actual tensor F and P, Hom-part pseudo-F and I, and their adjunctions. The general construction explicitly permits idempotented rings. | Additive constructions and their coefficient comparisons remain distinct obligations. |
| I.4.2 theorem, printed pp.23–24 / PDF pp.29–30 | Duality intertwines F with right-module pseudo-F and P with right-module I by natural isomorphisms. The first proof uses tensor–Hom evaluation; the second also has an adjunction route. | Both full source comparisons remain open here. The intended coefficient convention must be recorded explicitly. |
| I.4.2.1, printed p.24 / PDF p.30 | Transposition between the two original Hom spaces into nondegenerate duals, natural in both variables. | This separate assertion is not re-audited for Lean coverage by this note. |

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
No formal counterexample or source-theorem correction is claimed.

## A sufficient compatible-input route

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

The compatible-input comparison to construct is

```text
D_S(X ⊗_R M)  ≃  (Hom_(R.op)(X, D_R(M)))_(S.op)
curry(l)(x)(m) = l(x ⊗ m)
uncurry(h)(x ⊗ m) = h(x)(m).
```

The subscript denotes the nondegenerate part for the actual residual right
S-action. One must prove inner-dual landing, balancing, coefficient
linearity, fixation by actual idempotents, original S-equivariance, both
inverse identities and naturality. Neither comparison map nor any of
these conclusions is an input.

The existing Library interfaces identify the relevant actual additive
objects: `NonUnitalModuleTensor.Tensor`,
`NonUnitalBimoduleTensor.leftModule`,
`NondegenerateTensorScalars.module`,
`NonUnitalModuleDual.Dual`, and
`NonUnitalBimoduleHomActions.rightSourceAction`.
They are interface locators, not a claim that this comparison is proved.
In particular, the tensor's named coefficient module must be compared with
the S-recovered one, and the Hom part's inherited pointwise coefficients
with its right-S-recovered ones.

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

## Remaining whole-source obligation

The common-coefficient algebra-bimodule interpretation supports the proposed
route. The opening ring-bimodule convention is weaker. Resolving how that
interpretation applies to I.4.2 remains a source-correspondence obligation;
a compatible-input construction alone will not be counted as unrestricted
source coverage. The broader additive ring constructions remain in scope.

Residual tensor coefficient task
`52e2e51d-627a-49bd-b8da-ea7310949d22` and residual Hom coefficient task
`b1a134c9-c786-4e3a-a823-d4988394af07` track separate sufficient-input
prerequisites. Their task publication is not mathematical acceptance or
Library publication. This note certifies no candidate from either task
and creates no replacement for their owners.
