# Overlapping Cartan cells in Renard VII.1.2

Worker 1222, Task 1222 (`f5d1f399-a1f8-4ab5-a981-90b92abd4857`).

After (VII.1.2.1), Renard uses a disjoint-union sign for the refinement of
the Cartan decomposition by representatives \(k_i\) of \(K_0/K\). The
disjoint-union sign occurs once on printed p. 221 and twice on p. 222
(PDF pp. 227–228). On p. 222 the expansion of the integral sums over every
label \((i,j,f,z)\). Distinct labels can give the same double coset.

## A split torus example

Take \(G=\mathbb Q_3^\times\), the points of the split torus \(\mathbb G_m\).
Then \(A_{\varnothing}=A_G=G\) and the unipotent factors are trivial. Take
\(K_0=\mathbb Z_3^\times\) and \(K=1+3\mathbb Z_3\). Here \(K_0\) is maximal
compact, \(K\) is normal in \(K_0\), and the Iwahori factorization is
\(K=\{1\}K\{1\}\). The representatives are \(k_1=1\), \(k_2=-1\), from
reduction of units modulo \(3\). With uniformizer \(3\) the subgroup
\(C=C_{A_G}=3^\mathbb Z\) is the entire \(C_{\varnothing}^+\), since there
are no positive-root inequalities. The split-component lattice is already
the full valuation lattice, so \(F_{\varnothing}=\{1\}\) and \(S=\{1\}\)
are valid choices in V.3.23 and V.3.24.

On \(G/C\simeq\mathbb Z_3^\times\), write \(q\) for the quotient map. The
cell labels \((i,j)=(1,1),(2,2)\) both give \(q(K)\).
The labels \((1,2),(2,1)\) both give \(q(-K)\).
Take the trivial smooth representation on \(\mathbb C\), which is admissible
and has unitary central character. The vector \(1\) and functional
\(\lambda(x)=x\) are \(K\)-fixed and yield the constant coefficient \(1\).
Normalize Haar measure on \(G\) by \(\mu_G(K_0)=1\) and on \(C\) by counting
measure. The corresponding quotient Haar measure has total mass \(1\) and
assigns mass \(1/2\) to each cell, equal to the ambient mass of \(K\).
The integral in (VII.1.2.1) is \(1\) and the displayed four-term sum is \(2\).
The same duplicate labels occur in the two displayed decompositions of
\(G\) before taking the quotient.

## Corrected integration step

With Renard's \(K,K_0,F_{\varnothing},S\), put
\[
  D_{i,j,f,z}=q(K k_i f z k_j K),\qquad
  a(q(g))=|\phi_{v,\lambda}(g)|^2 .
\]
The unitary central character makes \(a\) well defined. The choice of \(K\)
makes it constant on each \(D_{i,j,f,z}\). The Cartan decomposition gives
\(G/C=\bigcup_{i,j,f,z}D_{i,j,f,z}\). This is a countable cover since
\(F_{\varnothing}\) is finite and \(S\) lies in a finite-rank lattice
lift. Each \(D_{i,j,f,z}\) is a compact open \(q(K)\)-double coset.
Thus distinct sets in this family form a measurable partition. One gets
equality by summing the constant value times the quotient measure over that
partition, with one term for each distinct set.

Writing \(\bar\mu\) for quotient Haar measure, the sum over the original
labels gives the bound
\[
  \int_{G/C} a\,d\bar\mu
  \ \le\ \sum_{i,j,f,z} a(q(k_i f z k_j))\,\bar\mu(D_{i,j,f,z}).
\]
Normality of \(K\) in \(K_0\) gives
\(D_{i,j,f,z}=q(k_i)q(K f z K)q(k_j)\). Left invariance and the triviality
of the modular character on the compact subgroup \(q(K_0)\) give
\(\bar\mu(D_{i,j,f,z})=\bar\mu(q(K f z K))\). The coefficient identity in
the second line of the source's sum still holds for each label. Consequently
the same translated coefficients and cell estimates suffice for the upper
bound.

With counting measure on \(C\) and compatible measures on \(G\) and \(G/C\),
the weight \(\bar\mu(q(KfzK))\) equals the ambient weight \(\mu_G(KfzK)\)
in the book. The map \(H_G\) is constant on \(KfzK\) since the compact
subgroup \(K\) lies in its kernel (V.2.3). If two points there differ by
\(c\in C\), then \(H_G(c)=0\). The section in V.2.5 and the injection of
split-component lattices in V.2.6 give \(c=1\). Averaging the compactly
supported indicator of \(KfzK\) over \(C\) as in II.3.9 thus gives the
indicator of its quotient image, and integration gives the identity of
the weights.

Under the coarser disjoint Cartan decomposition indexed by \((a,f)\) in
V.5.1(4), the labelled sum also has a bound by \(r^2\) times the integral,
where \(r=[K_0:K]\). Indeed, if the images of \(K_0 f z K_0\) and
\(K_0 f' z' K_0\) intersect in \(G/C\), then
\(K_0 f z c K_0=K_0 f' z' K_0\) for some \(c\in C\). Since
\(C\subseteq C_{\varnothing}^+\), the pair \((zc,f)\) is an original Cartan
label. Disjointness there gives \(f=f'\) and \(zc=z'\). The representative
property of \(S\) gives \(z=z'\). Each quotient cell thus occurs for at most
one pair \((f,z)\), and within that pair at most \(r^2\) times. This bounds
the multiplicities and gives equivalence of convergence with the integral
under the coarser partition hypothesis.

## Published Lean route

`rationalStrictJacquetSquareIntegrabilityReduction` builds a lattice cover
in the quotient by the full center using the joint special-compact basis.
It passes that cover and the coefficient and volume bounds to
`cartanLatticeL2`. The latter unions the finite family of quotient
double cosets for each lattice coordinate \(n\) into a set `cell n`,
then uses `measure_biUnion_finset_le` to bound its measure by the sum of
the individual bounds. `finiteLatticeCellL2` supplies a summable majorant
for the integral over this countable cover, and `countableCellLpUpper`
uses `lintegral_iUnion_le` followed by the pointwise bounds on each cell.
These are the published sufficiency estimates with overlap allowed.
[Reduction](../../Langlands/Representation/Aubert/General/RationalSquareIntegrabilityReductionProof.md) ·
[Cartan upper bound](../../Langlands/Representation/MatrixCoefficient/CartanLatticeL2Proof.md) ·
[Lattice summability](../../Langlands/Analysis/FiniteLatticeCellL2Proof.md) ·
[Countable cover](../../Langlands/Analysis/CountableCellLpProof.md)

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026. VII.1.2, printed pp. 221–222 (PDF pp. 227–228),
from (VII.1.2.1) through the expansion preceding (VII.1.2.2). The Cartan
parameters use V.3.23–24, printed p. 117 (PDF p. 123), and V.5.1–2,
printed pp. 122–123 (PDF pp. 128–129). For the measures, see II.3.9,
printed pp. 48–50 (PDF pp. 54–56), and V.2.3 and V.2.5–6,
printed pp. 105–108 (PDF pp. 111–114). Registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
