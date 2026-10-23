# Scope boundary in Silberger's relative multiplicity comparison

Author: Worker 19.

This note records a source-scope obstruction for the planned formalization of
Silberger 1978, Lemma 5.3, and the narrower assertion supported by its printed
proof. It is a mathematical source audit, not a Lean proof or an author-issued
erratum. The general Langlands quotient theorem is not contradicted by the
example below.

## Original and normalization

The source is A. J. Silberger, *The Langlands quotient theorem for p-adic
groups*, Math. Ann. 236 (1978), 95–104, retained as
`literature/Silberger (1978), The Langlands quotient theorem for p-adic groups.pdf`.
Its registered ID is
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`;
SHA-256 is
`4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
PDF page 1 is printed p.95. The whole article was read previously; pp.95–97
and 99–103 were reread for this audit, with the relevant notation and formula
pages inspected as images.

Write `I(P, rho)` for normalized upper parabolic induction and
`J_op,P(rho)` for the normalized opposite Jacquet module, whose action uses
the positive half of the upper modulus. In the nested setup on p.99, put

```
tau_t = omega_{i(nu_0 - nu'')}.
```

In the project's determinant-exponent convention this means the fine twist
`-nu_0 + nu''|M`. The minus sign on `nu_0` matters. Genericity tests the
stabilizer of `nu_0 - nu''`; total negation leaves that stabilizer unchanged.
It says that the stabilizer in `W(G/A)` is contained in `W(M''/A)`.

Lemma 5.3, p.100, prints the equality

```
[tau_t, J_op,P∩M''(mu)] = [tau_t, J_op,P(I(P'', mu))]
```

for an arbitrary irreducible admissible representation `mu` of `M''` and
generic `nu''`. It also says that the two multiplicities are nonzero exactly
when `mu` is a quotient of `I(P∩M'', tau_t)`. The brackets denote
Jordan–Hölder multiplicity, as defined on p.97.

## A GL₂ obstruction to the unrestricted statement

Let `F` be a nonarchimedean local field, `G = GL₂(F)`, `B` the upper Borel,
and `T` its diagonal torus. In the preceding setup take

```
P = P' = P'' = B,       M = M' = M'' = T,
omega = sigma' = sigma'' = 1,       nu_0 = 0,
nu'' = (1/2, 0).
```

These equal pairs are permitted by the source's containment order:
p.95 defines standard pairs by containment of the fixed minimal pair and
uses the same containment relation for the order. It is not a strict
chain requirement. In particular, the minimal pair itself is standard.
The torus character `1` is unitary cuspidal, square integrable modulo its
center, and tempered. The inner inductions here are identity functors.
The positive-root combination defining `nu_0` on p.99 is the empty sum.

The parameter `nu''` is regular positive. The relative Weyl group
`W(M''/A)` is trivial, and the nontrivial element of `W(GL₂/T)` does not
fix `nu_0 - nu'' = (-1/2, 0)`, so it is also generic. Set

```
tau_t = |.|^(1/2) tensor 1,
mu    = 1 tensor |.|^(1/2).
```

The two torus characters are distinct: evaluate them at
`diag(varpi, 1)` for a uniformizer `varpi`. Thus `mu` is irreducible
admissible but is not a quotient of the one-dimensional representation
`I(P∩M'', tau_t) = tau_t`.

The inner opposite radical is trivial, with modulus one. Consequently

```
[tau_t, J_op,P∩M''(mu)] = [tau_t, mu] = 0.
```

On the other hand, the cuspidal-induction Jacquet formula on p.97 applies
to `mu`, since every irreducible torus character is cuspidal. It applies
to either parabolic with this Levi, in particular to the opposite Borel.
After the stated normalization its two composition factors are `mu` and
its nontrivial Weyl translate `tau_t`, each once. Therefore

```
[tau_t, J_op,P(I(B, mu))] = 1.
```

This contradicts the printed unrestricted equality and its assertion that
the right-hand multiplicity can be nonzero only for an inner quotient.
The computation does not require irreducibility of `I(B, mu)`.

## What the printed proof establishes

The proof of Lemma 5.3 first gives, for each irreducible `mu`, the inequality
between the inner multiplicity and the ambient multiplicity. It then
compares their totals for the particular representation
`I(P∩M'', tau_t)`, using transitivity, exactness, and the Weyl stabilizer
count. Genericity makes those totals equal.

More explicitly, write the inner induction's composition factors as
`mu_j` with positive multiplicities `c_j`. If `a_j` and `b_j` are the
two multiplicities under comparison, the argument gives

```
a_j <= b_j,       sum_j c_j a_j = sum_j c_j b_j.
```

It follows that `a_j = b_j` for each constituent occurring in that
inner induction. The last paragraph of the printed proof makes exactly
this restriction. The summation gives no equality for an irreducible
`mu` outside that composition series; the GL₂ example has precisely
that form.

Accordingly, the defensible scope for a statement derived from this proof
requires `mu` to be an actual irreducible constituent of
`I(P∩M'', tau_t)`. The further nonzero-versus-quotient clause uses the
cuspidal quotient/projectivity input as in the source. This restriction
must be present in both Lean and Markdown and identified as a repair
derived from the proof, rather than silently attributed to the printed
unrestricted lemma. This note does not implement that repaired statement
or prove its representation-theoretic inputs in Lean.

## Downstream boundary

Corollary 5.4 on p.100 again quantifies arbitrary irreducible admissible
`mu` and invokes Lemma 5.3. Its printed proof therefore cannot be used
unchanged to justify that unrestricted scope. The present note does not
give a separate counterexample calculation for the corollary.

Lemma 5.5 already assumes that `mu` is an inner quotient. Lemma 5.6 on
p.101 assumes a tempered inner quotient and treats all regular positive
parameters. Those hypotheses put the generic step inside the supported
scope. Extending the multiplicity equality from generic to all regular
positive parameters still requires the source's continuation and
tempered-exponent argument; restricting Lemma 5.3 does not supply it.

Propositions 5.7–5.9 on pp.101–102 require their own correspondence checks.
In particular, Proposition 5.8 treats arbitrary irreducible tempered
outer-Levi input and gives a further argument. That assertion must not be
justified solely by the unrestricted generic Lemma 5.3.

The project's existing opposite-refinement constructions supply actual
coinvariant actions and normalization. They assert no Lemma 5.3
multiplicity equality and are unaffected by this obstruction. The
[source map](source-map.md) records the surrounding statement and proof
obligations. No author-issued correction for this lemma was available
in the retained literature when this note was prepared.
