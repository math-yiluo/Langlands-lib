# Reflection coefficients in Renard VII.4.1

Worker 1222, Task 1222 (`f5d1f399-a1f8-4ab5-a981-90b92abd4857`).

The proof of (VII.4.1.3) on printed p. 242 (PDF p. 248) gives two incorrect
formulas for a dual-basis coordinate of the Weyl displacement. The
nonnegative root-cone bound in (VII.4.1.3) follows from the simple-reflection
formula with the coroot coefficient.

## The two coordinates

Let \(\alpha_1,\ldots,\alpha_\ell\) be the simple roots, let \(\beta_i\) be
dual to \(\alpha_i\) under the character–cocharacter pairing, and let
\(\alpha_j^\vee\) be the simple coroot for \(\alpha_j\). Write \(s_j=s_{\alpha_j}\).
Since \(s_j\beta_i=\beta_i-\langle\alpha_j,\beta_i\rangle\alpha_j^\vee\),
the coordinate for \(w=s_j\) is
\[
  \langle\mu-s_j\mu,\beta_i\rangle
  =\langle\mu,\beta_i-s_j\beta_i\rangle
  =\delta_{ij}\langle\mu,\alpha_j^\vee\rangle.
\]
For \(i=j\) the printed value is \(2\langle\mu,\beta_i\rangle\).
In split \(\mathrm{SL}_3\), take \(\alpha_1=e_1-e_2\),
\(\alpha_2=e_2-e_3\) and \(\mu=\alpha_1+\alpha_2\). The character
\(\mu\) pairs to \(1\) with each of the simple coroots. For \(i=j=1\),
the coordinate is \(1\) and the printed expression is \(2\).

For \(w=v s_j\) the second summand in the printed induction is
\(\langle v^{-1}\mu,\beta_i-s_j\beta_i\rangle\). At \(i=j\) the correct
value is \(\langle\mu,v\alpha_j^\vee\rangle\). The source identifies it
with \(\langle\mu,v\beta_j\rangle\). In split \(\mathrm{SL}_3\) take
\(v=s_1s_2\), \(j=1\) and \(\mu=3\alpha_1+2\alpha_2\). This character
has simple-coroot values \(4,1\). The length increases from \(2\) to
\(3\) when passing from \(v\) to \(vs_1\), and \(v\alpha_1=\alpha_2\).
Thus the correct value is \(1\). Since
\(v\beta_1=\beta_1-\alpha_1^\vee\), the printed expression is \(3-4=-1\).

## The bound and its restriction

The Library's length induction uses
\[
  \mu-vs_j\mu=(\mu-v\mu)+\langle\mu,\alpha_j^\vee\rangle\,v\alpha_j.
\]
The first term belongs to the nonnegative root cone by induction.
The length increase makes \(v\alpha_j\) a positive root, and dominance makes
its coefficient nonnegative. Applying the result to the inverse Weyl
element gives the convention in (VII.4.1.3). The published
`RelativeRootReflectionData.fullRealAction_representative` proves the
reflection formula on the actual real character space.
`ParabolicRootPresentation.restrict_displacement_mem_nonnegCone` carries
out the length induction after restriction to the Levi split component.
[Real reflection and displacement](../../Langlands/GroupScheme/Rational/ParabolicWeylDisplacement.md)

The next paragraph of the book passes from the full displacement to (VII.4.1.2)
on \(\mathfrak a_M^*\). With the invariant inner product of V.3.7 and the
orthogonal decomposition of V.3.13, equality of the projection of
\(w^{-1}\mu\) with \(\mu\) would give
\[
  \|w^{-1}\mu\|^2=\|\mu\|^2+
    \|w^{-1}\mu-\operatorname{proj}_{\mathfrak a_M^*}(w^{-1}\mu)\|^2.
\]
Weyl invariance makes the last squared norm zero, so \(w^{-1}\mu=\mu\).
This supplies the implication from full nonvanishing to projected
nonvanishing for the parameter \(\mu\in\mathfrak a_M^*\).
The published `ParabolicRootPresentation.restrict_displacement_eq_zero_iff`
proves the projected statement by length induction. For a dominant
character strictly positive on the simple coroots outside the Levi, the
restricted displacement vanishes exactly on the Levi Weyl subgroup.
[Strict displacement after restriction](../../Langlands/GroupScheme/Rational/ParabolicStrictWeylDisplacement.md)

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
See VII.4.1, printed pp. 241–242 (PDF pp. 247–248), and
V.3.7 and V.3.12–15, printed pp. 111–113 (PDF pp. 117–119).
