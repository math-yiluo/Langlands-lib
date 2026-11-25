# The Levi index in the double-coset volume of Renard VII.1.2

In the calculation after (VII.1.2.2), Renard takes \(m=fz\) with
\(f\in F_{\varnothing}\) and \(z\in S_M(n)\). The calculation uses
\(m^{-1}K_Mm=K_M\) to obtain \(\mu_G(KmK)=\delta_P(m)\mu_G(K)\), where
\(K_H=K\cap H\). A bounded exponent in \(z\) can change the Levi
intersection and hence the volume. The two radical contractions alone
give an exact formula with an additional Levi index.

## A standard \(\mathrm{GL}_3\) example

Let \(F\) be a nonarchimedean local field with integer ring \(\mathcal O\),
uniformizer \(\varpi\) and residue field of size \(q\). Take
\(G=\mathrm{GL}_3(F)\), the upper standard parabolic \(P=MN\) of type
\((2,1)\), and its block-diagonal Levi \(M\). Take \(K_0=\mathrm{GL}_3(\mathcal O)\)
and \(K=I+\varpi^r\operatorname{Mat}_3(\mathcal O)\) for \(r\geq 1\).
These principal congruence subgroups are compact open, normal in \(K_0\),
and a neighborhood basis at the identity. Block Gaussian elimination gives
their Iwahori factorization for the standard parabolics. In the \(2+1\)
case, the leading block \(A\) is in \(I+\varpi^r\operatorname{Mat}_2(\mathcal O)\).
For the other blocks \(B,C,D\), the radical factors have entries \(CA^{-1}\)
and \(A^{-1}B\), both in \(\varpi^r\mathcal O\), and the second Levi block
is \(D-CA^{-1}B\in 1+\varpi^r\mathcal O\). Elimination in the \(1+2\) and
three-block cases uses the same unit pivots. On the split component of each
Levi, conjugation by a chamber element scales the corresponding radical
entries by uniformizer powers, giving the contraction and exhaustion
properties by entrywise valuations.

The minimal Levi is the diagonal split torus, so \(F_{\varnothing}=\{1\}\)
is valid. Modulo scalar uniformizer powers, use
\(t_{12}=\operatorname{diag}(\varpi,1,1)\) and
\(t_{23}=\operatorname{diag}(\varpi,\varpi,1)\) for the two simple-root rays.
For \(n=1\), the choice
\[
  m=z=t_{12}t_{23}^2=\operatorname{diag}(\varpi^3,\varpi^2,1)
\]
belongs to \(S_M(1)\). The exponent on the Levi simple root \(\alpha_{12}\)
is \(1\), while the outside exponent is \(2>1\). Conjugation by \(m\)
contracts \(K_N\), and conjugation by \(m^{-1}\) contracts \(K_{\bar N}\).
However, \(k=I+\varpi^r E_{12}\in K_M\) has
\(m^{-1}km=I+\varpi^{r-1}E_{12}\notin K_M\). Also
\(km\notin m(m^{-1}K_Nm)K\), since left multiplication by an element of
\(N\) leaves the upper-left \(2\times2\) block of \(m^{-1}km\) unchanged.
The conjugated intersection in the source's proposed set identity is
\(m^{-1}(K\cap N)m\). The notation \(K_{m^{-1}Nm}\) would denote \(K_N\)
under the prior definition of \(K_H\), since \(m\) normalizes \(N\).

Write \(a=(3,2,0)\). The intersection \(K\cap mKm^{-1}\) consists of the
matrices \(I+X\) with \(X_{ij}\in\varpi^{r+\max(a_i-a_j,0)}\mathcal O\).
Both \(K\) and its intersection with \(mKm^{-1}\) contain the principal
congruence subgroup at level \(r+3\). Counting the allowed entry residues
modulo \(\varpi^{r+3}\) gives
\[
  [K:K\cap mKm^{-1}]=q^{1+3+2}=q^6 .
\]
The left cosets in \(KmK\) therefore give
\(\mu_G(KmK)=q^6\mu_G(K)\). The forward Haar scaling on \(N\) is
\(q^{-3}q^{-2}=q^{-5}\). Renard's convention in V.5.4 gives
\(\delta_P(m)=q^5\). The extra factor \(q\) comes from the \((1,2)\)
entry of the Levi intersection. The discrepancy occurs at every level \(r\).

## Corrected set, index and volume formulas

Suppose \(K\) is compact open with the Iwahori factorization, the Levi \(M\)
normalizes both radicals, and the ambient multiplication
\(\bar N\times M\times N\to G\) is injective. Let \(m\in M\) satisfy
\(mK_Nm^{-1}\subseteq K_N\) and \(m^{-1}K_{\bar N}m\subseteq K_{\bar N}\).
In the reversed factorization \(K=K_NK_MK_{\bar N}\), move \(K_{\bar N}\)
past \(m\) and absorb it into the last \(K\). This gives \(KmK=K_NK_MmK\).

Put \(J=mKm^{-1}\), \(L=K_MK_N=K_NK_M\), and
\(H=(J\cap K_M)K_N=K_N(J\cap K_M)\). Both products \(L,H\) are subgroups
because \(K_M\) normalizes \(K_N\). As \(K=LK_{\bar N}\) and
\(K_{\bar N}\subseteq J\), representatives in \(L\) give
\([K:K\cap J]=[L:L\cap J]\). For \(x\in L\cap J\), compare its
factorization \(1\cdot \ell\cdot u\) in \(L\) with the conjugate by \(m\)
of the Iwahori factorization of \(m^{-1}xm\). Injectivity of the ambient
product puts \(\ell\) in \(J\cap K_M\), so \(L\cap J=H\cap J\). The index
tower \(H\cap J\le H\le L\) now has factors
\[
  [L:H]=[K_M:J\cap K_M],\qquad
  [H:H\cap J]=[K_N:J\cap K_N].
\]
Indeed, \(K_M\) represents the left cosets of \(H\) in \(L\), with
\(K_M\cap H=J\cap K_M\) by injectivity. Similarly \(K_N\) represents the
left cosets of \(H\cap J\) in \(H\). Normalization of \(M,N\) by \(m\)
gives \(J\cap K_M=K_M\cap mK_Mm^{-1}\) and \(J\cap K_N=mK_Nm^{-1}\),
using forward contraction for the last equality. Thus
\[
  [K:K\cap mKm^{-1}]
    =[K_M:K_M\cap mK_Mm^{-1}]\,[K_N:mK_Nm^{-1}].
\]

For \(N\) closed, \(K_N\) is compact open in \(N\). The second index is the
reciprocal of the factor by which \(u\mapsto mum^{-1}\) scales left Haar
measure on \(N\), by partitioning \(K_N\) into translates of \(mK_Nm^{-1}\).
This reciprocal is \(\delta_P(m)\) in the source's setting. Left Haar
measure \(\mu_G\) on \(G\) therefore satisfies
\[
  \mu_G(KmK)=[K_M:K_M\cap mK_Mm^{-1}]\,\delta_P(m)\,\mu_G(K).
\]
When \(m\) lies in the split component of \(M\) and satisfies the two
radical contractions, it centralizes \(K_M\) and the Levi index is one.

## The upper bound used for sufficiency

For fixed \(n\), write \(z=z_1z'\) as in VII.1.2, collecting the bounded
Levi exponents in \(z_1\). The elements \(a=fz_1\) then form a finite set.
For \(d_K(g)=[K:K\cap gKg^{-1}]\), the submultiplicativity
\(d_K(az')\le d_K(a)d_K(z')\) bounds each original cell. With the compatible
split-component lifts and the two contractions at \(z'\), the corrected
formula gives
\[
  \mu_G(Ka z' K)\ \le\ d_K(a)\,\delta_P(z')\,\mu_G(K).
\]
The finite set of translates gives a uniform constant for these volume
weights. This bound pairs with coefficient decay in a sum over a Cartan
cover. The earlier Cartan-cell calculation gives the passage from the
ambient weights to the central lattice quotient with compatible Haar
normalizations. [Cartan cover and integral bound](renard-vii12-cartan-cover.md)

The published `rationalLatticeQuotientVolume` uses
`standardBasisMember_rayIndex` and `latticeCentralQuotientVolume` to combine
the ray estimates by index submultiplicativity, absorb the finite translates
and bound cell measures on the quotient by the full center.
`rationalStrictJacquetSquareIntegrabilityReduction` uses those same ray
weights in the coefficient estimate on the common compact-open basis.
[Volume proof](../../Langlands/Representation/Aubert/General/RationalLatticeQuotientVolumeProof.md) ·
[Square-integrability reduction](../../Langlands/Representation/Aubert/General/RationalSquareIntegrabilityReductionProof.md)

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026. VII.1.2, printed pp. 222–223 (PDF pp. 228–229),
from (VII.1.2.2) through the reduction to the \(S'_M(n)\) series.
The ray and transversal choices use V.3.23–24, printed p. 117 (PDF p. 123).
The compact-open basis and modulus conventions are V.5.2 and V.5.4,
printed pp. 123 and 126–127 (PDF pp. 129 and 132–133).
Registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
