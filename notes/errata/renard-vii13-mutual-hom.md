# Hom dimensions and semisimplicity in Renard VII.1.3

Worker 1222, Task 1222 (`f5d1f399-a1f8-4ab5-a981-90b92abd4857`).

After (VII.1.3.2), Renard uses the common composition factors and the
one-dimensional Hom spaces between \(\pi\) and \(\pi'\) to claim that
both inductions fail to be semisimple. Those data exclude simultaneous
semisimplicity. To exclude semisimplicity of each induction separately,
one can apply the same adjunction to its endomorphisms.

## A length-two example

Let \(B\) be the algebra of upper triangular \(2\times2\) complex
matrices. Let \(X=\mathbb C^2\) be its natural module and \(Y=\mathbb C^2\)
the module on which a matrix acts through its two diagonal entries.
Both have a composition series with the line \(\mathbb C e_1\) and
one-dimensional quotient. The two simple factors are the distinct
characters given by the first and second diagonal entries.

The module \(Y\) is the sum of its two coordinate lines. In \(X\), a
complement of \(\mathbb C e_1\) would have to be \(\mathbb C e_2\) by
invariance under the diagonal idempotents. The matrix unit \(E_{12}\)
maps \(e_2\) to \(e_1\), which excludes that complement.

Any map between \(X\) and \(Y\) that commutes with the two diagonal
idempotents is diagonal in these coordinates. For a map \(X\to Y\),
commuting with \(E_{12}\) forces the first diagonal entry to be zero.
For a map \(Y\to X\), it forces the second diagonal entry to be zero.
Both Hom spaces are one-dimensional. Thus the same Hom dimensions
and the same composition factors occur with \(Y\) semisimple and
\(X\) a nonsplit extension.

## Applying adjunction to each induction

In the distinct-Levi case of the source argument, VI.5.3 gives
\(r_P^G\pi\simeq\rho\) and \(r_{P'}^G\pi'\simeq\rho'\).
Frobenius reciprocity for each induction and Schur's lemma give
\[
  \operatorname{End}_G(\pi)\simeq\operatorname{End}_M(\rho)\simeq\mathbb C,
  \qquad
  \operatorname{End}_G(\pi')\simeq\operatorname{End}_{M'}(\rho')\simeq\mathbb C.
\]
Each induction has length two in the situation considered. A direct
sum of two nonzero factors would have a nonscalar projection onto one
factor. Thus each induction is nonsemisimple. In the unitary branch,
one can also use the mutual Hom calculation directly. Both inductions
are admissible and unitarizable there, so both would be semisimple.

The published `maximalLeviSupercuspidalInductionEndomorphism` supplies
the self-endomorphism argument on the represented parabolics. It shows
that a nonscalar endomorphism requires a point outside the Levi that
normalizes the Levi and intertwines the inducing representation with
its conjugate. The published `exists_nonscalar_endomorphism_of_semisimple`
gives the projection argument for a reducible semisimple smooth
representation. The general reducibility proof remains the target of
Task `004e00e1-5995-4dc1-884e-a5f512150d0c`.
[Induction endomorphisms](../../Langlands/Representation/Exponents/MaximalLeviSupercuspidalInductionEndomorphismProof.md) ·
[Semisimple projection](../../Langlands/Representation/Exponents/MaximalLeviReducibilityUnitaryProof.md)

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026. VII.1.3, from (VII.1.3.1) to the paragraph
after (VII.1.3.2), printed p. 225 (PDF p. 231). VI.5.3, printed p. 173
(PDF p. 179), gives the Jacquet calculations. VI.1.2, printed p. 136
(PDF p. 142), gives the normalized adjunction. B.II, printed p. 272
(PDF p. 278), gives Schur's lemma. Registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
