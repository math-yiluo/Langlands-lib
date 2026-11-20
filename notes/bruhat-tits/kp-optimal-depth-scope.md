# KP §13.4: jumps at all optimal points need not form a discrete set

On printed p. 473 / PDF p. 504, Kaletha–Prasad first fix a chamber, choose
one optimizer \(x_S\) per nonempty subset \(S\subseteq\Sigma\), and let
\(O\) be the union of their rational-group orbits. The next sentence calls
\(r\in\mathbb Q\) an optimal number when \(\mathfrak g_{x,r}\ne\mathfrak g_{x,r+}\)
for an optimal point \(x\). It deduces discreteness from local finiteness of
\(O\). If “an optimal point” includes every point satisfying Definition
13.4.2, the discreteness claim is false, already in the book's split example.
This note gives a paper calculation, not a Lean result.

## Split \(\mathrm{SL}_3\) over \(\mathbb Q_5\)

Take the diagonal apartment with the special origin and simple roots \(a,b\)
of Example 13.4.3 (printed p. 473 / PDF p. 504). In the two root coordinates,
the closed alcove is \(a,b\ge0\), \(a+b\le1\). The ordinary affine roots are
\(\alpha+n\) for \(\alpha\in\{\pm a,\pm b,\pm(a+b)\}\) and \(n\in\mathbb Z\)
(Proposition 6.4.1, printed p. 223 / PDF p. 254). The strip period is 1 by
these integer fibres. The root \(a+b\) lies in \(\Sigma\) since its value in
the open alcove lies strictly between 0 and 1.

For every rational \(0<t<1\), let \(x_t\) have coordinates \((t,1-t)\).
Every affine root takes a rational value there, and \((a+b)(x_t)=1\) is
maximal over the closed alcove. Thus \(x_t\) is optimal for \(\{a+b\}\) by
Definition 13.4.2 (printed p. 472 / PDF p. 503), regardless of which point
was chosen as \(x_{\{a+b\}}\).

For nonnegative real \(r\), the summand of the Lie lattice on the \(a\)-root
line is

\[
\mathfrak g_{x_t,r}\cap F E_{12} =
  5^{\lceil r-a(x_t)\rceil}\mathcal O_F E_{12},\qquad F=\mathbb Q_5 .
\]

Indeed, §13.3.3 (printed pp. 470–471 / PDF pp. 501–502) uses the explicit
root-summand lattice description of §8.5.20 (printed pp. 320–321 / PDF
pp. 351–352), which applies over the ground integer ring in the split
case. At the Chevalley origin the split root is of type R1 with ramification
index 1 and Chevalley vector \(E_{12}\). The lattice exponent is the least
integer at least the cutoff. At \(x_t\) an affine root \(a+n\) qualifies
exactly when \(a(x_t)+n\ge r\), so the cutoff in this root direction is
\(r-a(x_t)\); the other root and toral directions cannot change this summand.

At \(r=t\), the exponent is zero, so \(E_{12}\in\mathfrak g_{x_t,t}\).
For each real \(s>t\), the exponent is positive, so \(E_{12}\notin
\mathfrak g_{x_t,s}\). The strict lattice is the union over those \(s\)
(§13.3.1, printed p. 470 / PDF p. 501). Hence the lattice jumps at \(t\).
The jump set over all optimal points contains \((0,1)\cap\mathbb Q\), so it
is not discrete even in \(\mathbb Q\).

## Consequence for formalization

Keep all optimal points distinct from the chosen set \(O\). At finitely
many fixed chamber representatives in this split example, the jump depths
are contained in a finite union of translates of \(\mathbb Z\): the root
summands jump at their root evaluations modulo \(\mathbb Z\), and the split
toral summand at integers. Such a bound is preserved along their \(G(F)\)-orbits
when using conjugation covariance of the lattices. The all-optimal-points
calculation does not contradict the fixed-choice reading. It does not give
a general discreteness theorem for \(O\), nor should one be inferred from
local finiteness of the point set alone.

Neither Definition 13.4.2 nor Lemma 13.4.4 is refuted. Proposition 13.6.7
(printed p. 481 / PDF p. 512) uses Lemma 13.4.4 to find *some* optimal
point whose deeper lattice contains the coset; that step does not use
discreteness of the jumps at all optimal points.

## Sources

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
- The authors' *Corrections and additions*, 1 November 2024,
  `kaletha-prasad-2024-corrections`, SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
  PDF pp. 32, 37–38 and 49 leave the passages used above unchanged.
  The scope distinction argued here is not an authors' erratum.
