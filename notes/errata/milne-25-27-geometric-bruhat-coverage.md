# Milne 25.27: mixed relative positions after scalar extension

The two relative Bruhat cells for
\(G=\operatorname{Res}_{\mathbb C/\mathbb R}\mathrm{GL}_{2,\mathbb C}\)
cover the real points of its minimal flag quotient. Their complex fibres
omit points where the two flags have different Bruhat positions. This
gives a counterexample to reading the two displayed unions of varieties
in Milne 25.27 as geometric coverings by the ground-field relative cells.

## The real group and its two relative Weyl classes

For every real algebra \(A\),
\(G(A)=\mathrm{GL}_2(\mathbb C\otimes_{\mathbb R} A)\).
Let \(B\) be the upper triangular subgroup and let
\(P=\operatorname{Res}_{\mathbb C/\mathbb R} B\). Over \(\mathbb C\) the
tensor algebra splits by the identity and conjugate embeddings. Thus
\(G_{\mathbb C}=\mathrm{GL}_2\times\mathrm{GL}_2\) and
\(P_{\mathbb C}=B\times B\). In particular \(G\) is connected reductive
and \(P\) is a real-defined Borel, hence minimal among real parabolics.

The real diagonal torus \(S=\mathbb G_{m,\mathbb R}^{2}\) embeds in
\(P\). Any real split subtorus of \(G\) acts faithfully on
\(\mathbb C^2\) viewed as a real vector space, with action commuting
with multiplication by \(i\). Each real weight space is therefore a
complex subspace. There are at most two characters with nonzero
weight spaces. Faithfulness forces these characters to span the rational
character lattice, giving rank at most two. Thus \(S\) is maximal split
in \(G\) and in \(P\).

A real point of \(N_G(S)\), viewed as a complex matrix, permutes the
two coordinate lines. Indeed it sends the eigenspaces of
\(\operatorname{diag}(2,1)\) to the eigenspaces of a real diagonal
conjugate of that matrix. The complex diagonal points centralize \(S\).
The relative Weyl group has two elements, represented by the identity
and \(j=\begin{pmatrix}0&1\\1&0\end{pmatrix}\). The two representatives
base change to \((1,1)\) and \((j,j)\).

The two relative roots are \(\alpha(s_1,s_2)=s_1/s_2\) and its inverse,
with weight spaces the two off-diagonal complex lines in the Lie
algebra. The cocharacter \(t\mapsto\operatorname{diag}(t,1)\) pairs
with them by \(1\) and \(-1\), so it is generic. Its dynamic parabolic
is \(P\), and its unipotent subgroup \(U\) is the restriction of the
upper unitriangular subgroup. The inverse cocharacter gives the lower
unitriangular subgroup \(V\).

## Flags omitted after extension to \(\mathbb C\)

The quotient \((G/P)_{\mathbb C}\) is
\(\mathbb P^1_{\mathbb C}\times\mathbb P^1_{\mathbb C}\).
The quotient map sends a pair of invertible matrices to the spans of
their first columns. The upper triangular subgroups stabilize the
first coordinate lines, and each line can locally be completed to a
basis, giving local sections of the quotient map.

Write \(\ell_0=[1:0]\) and \(\ell_1=[0:1]\). For the identity,
\(U\cap V=1\), so the cell consists of \((\ell_0,\ell_0)\).
For \(j\) the factor \(U\cap jVj^{-1}\) is \(U\), and in each complex
factor the matrix \(\begin{pmatrix}1&a\\0&1\end{pmatrix}j\) sends
the first coordinate line to \([a:1]\). The resulting cell is
\[
(\mathbb P^1_{\mathbb C}\setminus\{\ell_0\})\times
(\mathbb P^1_{\mathbb C}\setminus\{\ell_0\}).
\]
The point \((\ell_0,\ell_1)\) lies outside both images. Its lift
\((1,j)\) lies outside both base-changed images of the corresponding
double-coset multiplications into \(G\).

On the flag quotient the real structure sends
\((\ell,\ell')\) to \((\overline{\ell'},\bar\ell)\).
A real point has complex coordinates \((\ell,\bar\ell)\), which
lie in the identity cell when \(\ell=\ell_0\), and in the
two-dimensional cell otherwise. This also exhibits the weight
multiplicity two of the positive relative root.

## Source and Library scope

Milne, *Algebraic Groups* (2017), §25.27, printed p.551 (PDF p.567),
gives the individual variety parametrization and displays the unions for
\(G/P\) and \(G\). The author's errata entry “p.545 et seq.” requires a
minimal \(P\) and a maximal split torus in \(P\). The example satisfies
both requirements. The Weil restriction point functor and base change
are in Milne §2.i, §§2.54–2.55 and 2.59, printed pp.57–58
(PDF pp.73–74). Borel–Tits, *Groupes réductifs* (1965), Theorem 5.15,
printed pp.100–101 (PDF pp.47–48), gives the ground-field double-coset
partition.

The Library's `rationalBruhat` indexes the double cosets of \(G(k)\).
`rationalBruhatCell` gives each locally closed multiplication map and
identifies its image on \(k\)-points. The partition clause of
`RationalBruhatFlagCellStatement` concerns the \(k\)-points of a represented
flag quotient.
[Double cosets](../../Langlands/GroupScheme/Rational/RationalBruhatProof.md),
[multiplication](../../Langlands/GroupScheme/Rational/BruhatCellProof.md),
[flag statement](../../Langlands/GroupScheme/Rational/BruhatFlagCellStatement.md)

Registered originals `milne-2017-algebraic-groups`
(`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`),
`milne-2017-algebraic-groups-errata-2026-11-02`
(`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) and
`borel-tits-1965-groupes-reductifs`
(`ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`).
