# Silberger's continuation parameters and varying inductions

Authors: Worker 359 and Worker 430.

The continuation sentences in Silberger 1978, printed pp.101–102, vary
unitary parameters. In particular, Proposition 5.8 has a parameter on the
ambient inducing representation as well as on its asserted class exponent.
Dropping that subscript changes the assertion. This note records the
original formulas and the obligations they leave for formalization. It is
a source-reading note, not a Lean continuation proof or an author erratum.

## Original and notation

The source is A. J. Silberger, *The Langlands quotient theorem for p-adic
groups*, Math. Ann. 236 (1978), 95–104, retained at
`literature/Silberger (1978), The Langlands quotient theorem for p-adic groups.pdf`.
Its registered ID is
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`;
SHA-256 is
`4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
PDF page 1 is printed p.95. The relevant page images are PDF pages 2, 7
and 8 for printed pp.96, 101 and 102. Printed p.103 was also inspected
for the subsequent uniqueness argument. No source-specific erratum file
was present in the supplied errata locations when this note was prepared.

The images must be consulted: text extraction obscures the imaginary unit,
Greek nu versus Latin v, and the subscript on the ambient representation.
Here `v₀` and `v''` denote the fixed real vectors in the nested setup;
`ν'` and `ν''` denote the varying real source parameters.
Write `i = √(-1)` and retain the source's class-exponent notation
`𝔇_π(P,A)`. This is the class spectrum of the normalized opposite Jacquet
module, rather than a claim about a chosen irreducible quotient of `π`.

Printed p.96 defines

\[
\chi_\nu(m)=q^{\,i\langle\nu,H(m)\rangle},
\qquad \sigma_\nu(m)=\sigma(m)\chi_\nu(m).
\]

Thus a real source parameter varies a unitary character. In the Library's
established determinant coordinates, the corresponding complex exponent
is `z = i ν`. This gives the following coordinate dictionary:

| Source subscript | Library determinant exponent |
| --- | --- |
| `ν = u`, with `u` real | `i u` |
| `ν = -i t`, with `t` real | `t` |
| `ν = i r`, with `r` real | `-r` |
| `ν = i(v₀-v'')` | `-v₀ + v''` restricted to the fine Levi |

These are parameter conversions, not new identifications of representation
carriers. Block-scalar weights still multiply determinant exponents by
the block sizes. The signs agree with
[`RealTwistFamilies.nestedParameter`](../../Langlands/Representation/Exponents/RealTwistFamilies.md),
whose actual formula is `-v₀ + restrictParameter B S t`.

## Lemma 5.6, printed p.101

Lemma 5.6 assumes that the tempered coarse-Levi input is a quotient of
the specified inner induction. Its proof considers a fixed set of Weyl
labels `X` and the stabilizer-related set `Y`. In the paragraph beginning
with a label `s ∈ X − Y`, the source assumes

\[
s(v_0-v'')=v_0-v''
\]

and asserts, by analytic continuation,

\[
\omega_{s\nu'+i\,s v_0}
\in \mathfrak D_{\,C^G_{M'}(\omega'_{\nu'})}(P,A)
\quad\text{for almost all }\nu'\in\mathfrak a'^*.
\]

The varying parameter belongs to the **middle Levi** `M'`; the family in
the subscript is the source's tempered family. Both occurrences of `ν'`
are part of the formula. Its candidate has complex determinant coordinate
`-s v₀ + i s ν'`. This sentence does not assert variation of an arbitrary
coarse real-power parameter inside a fixed induction.

The proof then uses temperedness to obtain the source's closed positive
root-cone condition on `s v₀`, followed by a Weyl-invariant inner-product
argument. The coordinate conversion alone supplies neither the
class-exponent occurrence nor the cone condition. In particular, an
almost-everywhere assertion cannot be specialized to `ν'=0` without an
additional argument.

The inner-quotient hypothesis must remain present. The separate
[Lemma 5.3 scope audit](silberger-lemma53-scope.md) explains why its
unrestricted printed wording cannot supply the generic comparison for
arbitrary unrelated inducing representations.

## Proposition 5.8, printed p.102

This proposition treats an arbitrary irreducible tempered representation
`σ''` of the coarse Levi `M''`. In its contradiction argument the source
selects a set `Y` relative to the fixed real twist
`I(P'',σ''_{-i v''})`, with `Y` disjoint from the coarse Weyl group.
For `s ∈ Y`, the printed continuation sentence is

\[
\omega_{i\,s v_0+\nu''}
\in \mathfrak D_{\,I(P'',\sigma''_{\nu''})}(P,A)
\quad\text{for all }\nu''\in\mathfrak a''^*.
\]

Three details are visible in the enlarged original:

- The sign before `i s v₀` is positive.
- The added parameter is `ν''`, with no printed `s` acting on it.
- The ambient inducing representation is `σ''_{ν''}`, including its subscript.

The candidate therefore has complex determinant coordinate
`-s v₀ + i ν''`, with the coarse parameter restricted as appropriate.
The ambient induction varies by the unitary twist `i ν''`.
The earlier internal paraphrase that `s(v₀-t)+t` occurs for every real `t`
in a fixed untwisted induction is superseded: it is not a transcription
or a consequence established by this note.

At `ν''=0`, the printed universal assertion gives

\[
\omega_{i\,s v_0}
\in\mathfrak D_{\,I(P'',\sigma'')}(P,A).
\]

This specialization is conditional on establishing the source's selected
branch and continuation assertion. The source uses temperedness of this
untwisted induction to obtain `s v₀ ∈ +𝔞*`. Separately, the fixed-parameter
stabilizer equation gives

\[
v_0-sv_0=v''-sv''.
\]

The source's chamber and inner-product argument uses these two inputs.
The universal unitary family and the fixed real stabilizer parameter must
not be identified with each other. If only the unshifted cone input is
needed downstream, a narrower theorem proving that occurrence could
suffice; this is a proposed proof boundary, not a theorem established here.

## Formalization boundary

The accepted
[`RealTwistFamilies`](../../Langlands/Representation/Exponents/RealTwistFamilies.md)
constructs real-twist inductions, affine transported candidates and
same-parameter opposite-Jacquet occurrence loci. Those definitions
have no continuation, genericity or fixed-label persistence property.
The existing scalar complex powers in
[`Shahidi.Induction`](../../Langlands/Representation/Shahidi/Induction.md)
provide character constructions, not continuation either. Actual complex
product-Levi twists and induced families are construction prerequisites
for directly expressing the source's varying unitary families.

A usable continuation theorem still needs to justify selection of the
responsible branches, the quantifiers in the relevant source passage, and
their actual opposite-Jacquet occurrences. Equality of candidate classes
at one collision does not by itself identify their parameterized families.
Likewise, a pointwise existential Weyl label does not give a single label
valid uniformly in the parameter.

The source's inference from almost-all middle-Levi occurrences in Lemma
5.6, the all-parameter assertion for the selected coarse-Levi branches in
Proposition 5.8, and the continuation comparison in Proposition 6.1 remain
distinct proof obligations. General class-exponent finiteness and elementary
cone rigidity do not prove these representation-theoretic inputs.

Finally, an occurrence in the whole induced representation supplies no
automatic occurrence in an arbitrary irreducible quotient, equality of
Jordan–Hölder multiplicities, or comparison of Hom dimensions. None of
these stronger conclusions, nor unrestricted Lemma 5.3 or Corollary 5.4,
is asserted by this note.
