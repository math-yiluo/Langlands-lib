# Relative root groups in characteristic two: exact-root generation and positive multiples

Worker 3483, 13 November 2026, for Task 3483
(`2b5e4a00-9d44-49a4-9c89-979fb5b6233e`).

This note gives a paper counterexample to identifying the exact-root
generating family in Milne's 25.19 with the standard relative root group
defined using positive integral multiples. It also explains the related
single-weight Lie sentence and the dimension formula in 25.20. The example
is a connected reductive group over an explicit field of characteristic
two, with an explicit maximal split torus and a containing maximal torus.
All subgroup comparisons below are identities or inclusions on every
test algebra, including nonreduced algebras.

The constructions and calculations are derived here. This is a mathematical
note submitted for independent semantic review, not a Lean construction or
a formal counterexample theorem. It supplements the dated unresolved
comparison in the
[family-5 comparison update](../group-schemes/rational-absolute-coverage-2026-11-13.md).
The published Library already uses positive multiples and requires no
change for this example.

## 1. The source distinction

Milne 2017, 25.19–25.20, printed p.549/one-based PDF p.565, and the 2022
corrected reprint, printed p.553/PDF p.564, use absolute roots whose
restriction is exactly the chosen relative root \(a\) in the generating
definition. A later sentence in 25.19 describes a Lie algebra using only
\(\mathfrak g_a\); the following dimension formula involves both
\(\mathfrak g_a\) and \(\mathfrak g_{2a}\).

Borel–Tits 1965, 3.8(ii), 3.13(b) and 5.2, use the roots restricting to
positive integral multiples of \(a\). The dynamic characterization and
positive integral weight Lie algebra also appear in
Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition,
Proposition C.2.21, printed pp.615–616/PDF pp.641–642.

A definition by an exact generating family is meaningful. The defect at
issue is its identification with the standard positive-multiple group and
the ensuing structural assertions in this generality. In the example
below, write \(E\) for that exact-generated closed subgroup after splitting
and \(U_{(a)}\) for the standard group. We prove

\[
 E\ \subsetneq\ (U_{(a)})_L,\qquad
 \dim E<7,\qquad
 \dim\mathfrak g_a=4,\quad \dim\mathfrak g_{2a}=3.
\]

The strict inclusion comes from a closed quadratic-form stabilizer, not
from assuming either disputed source assertion.

The retained 2017 and 2022 author errata were read in full. They do not
replace the exact generating condition or reconcile these Lie statements.
The 1972 Borel–Tits supplement, §5, corrects a different equality in
1965, 3.8(2); it does not remove the positive-multiple definition in 5.2.
Precise registered sources and reading locations are listed in §9.

## 2. An explicit quaternion division algebra

Put \(k=\mathbf F_2((t))\) and \(L=\mathbf F_4((t))\). Let
\(\bar{\phantom a}\) on \(L\) be the nontrivial \(k\)-automorphism, acting
as coefficient Frobenius. Choose
\(\omega\in\mathbf F_4\) with \(\omega^2+\omega=1\).
Inside \(M_2(L)\) define

\[
 D=\left\{
 \begin{pmatrix}u&tv\\ \bar v&\bar u\end{pmatrix}:u,v\in L
 \right\}.
\]

Write its elements as \(u+v\eta\), where
\(\eta=\left(\begin{smallmatrix}0&t\\1&0\end{smallmatrix}\right)\).
Matrix multiplication gives

\[
 (u+v\eta)(r+s\eta)
 =(ur+tv\bar s)+(us+v\bar r)\eta .
\]

Thus \(D\) is an associative four-dimensional \(k\)-algebra,
\(\eta^2=t\), and \(\eta u=\bar u\eta\). Its determinant is

\[
 N_D(u+v\eta)=N_{L/k}(u)+tN_{L/k}(v).
\]

For nonzero \(u,v\), the two summands have valuations
\(2\operatorname{val}(u)\) and \(1+2\operatorname{val}(v)\), so they
cannot cancel. The same determinant is nonzero when precisely one of
\(u,v\) is zero. Its adjugate represents \(\bar u+v\eta\), again in
\(D\), so every nonzero element has its inverse in \(D\).
Commuting with \(\omega\) forces \(v=0\); commuting also with \(\eta\)
forces \(u=\bar u\in k\). Hence \(D\) is central division of degree two.

The matrix map extends to \(D\otimes_k L\simeq M_2(L)\): the images of
\(1,\omega\) span all diagonal matrices over \(L\), and their products
with \(\eta\) span all off-diagonal matrices. The canonical involution is

\[
 \overline{u+v\eta}=\bar u+v\eta,\qquad
 \operatorname{Tr}_D(u+v\eta)=u+\bar u .
\]

In particular \(\operatorname{Tr}_D(\omega)=1\), the reduced trace is
surjective, and
\(\operatorname{Alt}(D,\bar{\phantom x})
=\{x-\bar x:x\in D\}=k\).
These formulas, the trace identity and the reduced norm extend to every
commutative \(k\)-algebra.

## 3. The actual reductive group and maximal split torus

On the right \(D\)-module \(V=D^3\) take the nonsingular hermitian form

\[
 h(x,y)=\bar x_1y_2+\bar x_2y_1+\bar x_3y_3,\qquad
 H=\begin{pmatrix}0&1&0\\1&0&0\\0&0&1\end{pmatrix}.
\]

Its self-pairings are
\(\operatorname{Tr}_D(\bar x_1x_2)+N_D(x_3)\in k\).
Consequently \(h\) is alternating in the characteristic-two hermitian
sense \(h(x,x)\in\operatorname{Alt}(D,\bar{\phantom x})\).
This condition is not the assertion \(h(x,x)=0\).

Let \(A=M_3(D)\) and
\(\sigma(g)=H^{-1}\bar g^{\,t}H\). By *The Book of Involutions*,
§4.A, Theorem 4.2, \(\sigma\) is a symplectic involution.
Define the affine group scheme by

\[
 G(R)=\{g\in M_3(D_R)^\times:\bar g^{\,t}Hg=H\}
 \quad(D_R=D\otimes_kR).
\]

It is the group \(\operatorname{Sp}(A,\sigma)\) of §23.A of that book:
for a unit, \(\sigma(g)g=1\) is equivalent to \(g\sigma(g)=1\).
The smoothness and connectedness assertion of §23.A and Theorem 26.14
apply in characteristic two. Since \(\deg A=6\), \(G\) is smooth,
connected, simply connected and absolutely simple of type \(C_3\).
In particular it is a connected reductive \(k\)-group.

Embed \(S=\mathbf G_m\) by
\[
 z\longmapsto \operatorname{diag}(z,z^{-1},1).
\]
It preserves \(h\). Here \(S\) is maximal \(k\)-split, as the following
dimension argument shows.

For any split torus \(R_0\subset G\), its faithful action on \(V\)
decomposes into character spaces \(V_\chi\). Each is a right
\(D\)-submodule because the action is \(D\)-linear. Invariance of \(h\)
gives \(h(V_\chi,V_\psi)=0\) unless \(\chi+\psi=0\), and
nonsingularity pairs \(V_\chi\) perfectly with \(V_{-\chi}\).
A nonzero pair consumes at least two \(D\)-dimensions. Since
\(\dim_D V=3\), there is at most one nonzero pair. Faithfulness forces
the occurring weights to span \(X^*(R_0)\otimes_{\mathbf Z}\mathbf Q\);
otherwise a positive-dimensional split subtorus would act trivially.
Thus \(\operatorname{rank}R_0\leq1\), proving maximality of \(S\).
This uses torus characters: \(\chi\) and \(-\chi\) remain distinct for
nonzero \(\chi\), including in characteristic two.

## 4. A containing maximal torus and split coordinates

There is an explicit containing \(k\)-torus

\[
 T=\operatorname{Res}_{L/k}\mathbf G_m
       \times\operatorname{Res}^{1}_{L/k}\mathbf G_m,\qquad
 (r,s)\longmapsto\operatorname{diag}(r,\bar r^{-1},s).
\]

The isometry equation follows from \(\bar s s=1\).
It contains \(S\) via \(r=z,s=1\).
Over \(L\), the involution on \(D_L=M_2(L)\) is adjoint to
\(J=\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)\).
Consequently \(\sigma_L\) on \(A_L=M_6(L)\) is adjoint to
\(B=H\otimes J\), a nondegenerate alternating form.

Let \(W=L^6\) be the defining representation of this matrix algebra.
This is the six-dimensional Morita representation; \(V\otimes_k L\)
itself has \(L\)-dimension twelve. Starting with coordinates
\((u_1,u_2;v_1,v_2;w_1,w_2)\) on \(W\), reorder them as

\[
 (x_1,x_2,x_3,y_1,y_2,y_3)
 =(u_1,u_2,w_1,v_2,v_1,w_2).
\]

Now \(B\) is the polar form of
\(Q=\sum_{i=1}^3x_i y_i\), and \(G_L=\operatorname{Sp}_6\).
Writing the two components of \(r\) as \(r_+,r_-\) and those of \(s\)
as \(q,q^{-1}\), the image of \(T_L\) is

\[
 \operatorname{diag}(r_+,r_-,q,r_+^{-1},r_-^{-1},q^{-1}).
\]

It is the full diagonal symplectic torus. Thus the original map is a
closed embedding and \(T\) is maximal; these properties descend from
the splitting extension. The image of \(S_L\) is
\(\operatorname{diag}(z,z,1,z^{-1},z^{-1},1)\).
For the usual coordinate characters \(e_1,e_2,e_3\) of \(T_L\),

\[
 e_1|_S=e_2|_S=a,\qquad e_3|_S=0,\qquad a(z)=z.
\]

The nonzero adjoint \(S\)-weights are \(\pm a,\pm2a\).
In particular \(a\) is a relative root of this maximal split torus.
Since \(L/k\) is finite separable, the same coordinates and comparisons
hold over a separable closure and over an algebraic closure.

## 5. The exact-root groups preserve a quadratic form

The type-\(C_3\) roots restricting exactly to \(a\) are the four short
roots \(e_i-e_3,e_i+e_3\), \(i=1,2\).
Those restricting to \(2a\) are \(e_1+e_2,2e_1,2e_2\).
For every commutative \(L\)-algebra \(R\) their relevant root matrices
act as follows, with unlisted coordinates fixed and \(c\in R\):

| Absolute root | Coordinate action |
| --- | --- |
| \(e_i-e_3\) | \(x_i\mapsto x_i+cx_3,\quad y_3\mapsto y_3+cy_i\) |
| \(e_i+e_3\) | \(x_i\mapsto x_i+cy_3,\quad x_3\mapsto x_3+cy_i\) |
| \(2e_i\) | \(x_i\mapsto x_i+cy_i\) |

These formulas identify the intrinsic absolute root functors on all
test algebras, not merely their tangent spaces. Indeed, for an absolute
root \(\beta\), an orbit extension through the character \(\beta\)
with identity at zero forces a matrix entry of weight \(\gamma\) to
vanish unless \(\gamma=n\beta\) for an integer \(n>0\); weight-zero
entries must be those of the identity matrix. To see this over arbitrary
\(R\), compare coefficients in
\(R[t_1^{\pm1},t_2^{\pm1},t_3^{\pm1}]\) with a polynomial in
\(\beta(t)\). Laurent monomials form an \(R\)-basis, and the characters
\(n\beta\) are distinct.

For either short root above, the only positive multiple occurring in
\(\operatorname{End}(W)\) is \(\beta\), at the two displayed positions.
The equation \(g^tBg=B\) makes the two coefficients equal. For \(2e_i\)
there is just one allowed position. Conversely, the displayed matrices
satisfy this equation and have polynomial orbit with identity at zero.
This proves the claimed root-group formulas over every \(R\).
Affine-local checking gives the same assertions for arbitrary test
schemes.

Each of the four exact-\(a\) groups preserves \(Q\): its change in \(Q\)
is the sum of two equal cross terms, hence zero in characteristic two.
Therefore all four lie in the closed subgroup \(O(Q)\subset
\operatorname{Sp}_6\). No smoothness assertion about \(O(Q)\) is used.

The long root group \(U_{2e_i}\) changes \(Q\) by \(cy_i^2\).
For \(c=1\), the vector with \(y_i=1\) and all other coordinates zero
witnesses failure to preserve \(Q\). On the other hand its \(S\)-orbit
is \(u(cz^2)\), which extends polynomially with identity at zero.
Thus

\[
 U_{2e_i}\subset (U_{(a)})_L,\qquad
 U_{2e_i}\not\subset O(Q).
\]

The exact-generated closed subgroup \(E\) lies in
\(O(Q)\cap(U_{(a)})_L\), whereas this intersection omits the displayed
long-root point. Hence \(E\ne(U_{(a)})_L\).
The same closed comparison subgroup proves failure over the separable
closure used in Milne's formulation.

## 6. The relative group and its Lie algebra directly

Because \(a:S\to\mathbf G_m\) is an isomorphism, the orbit-extension
definition of \(U_{(a)}\) is just contraction under this \(S\).
For every commutative \(k\)-algebra \(R\), comparison of Laurent weights
in a \(3\)-by-\(3\) \(D_R\)-matrix forces the shape

\[
 g=\begin{pmatrix}1&c&b\\0&1&0\\0&d&1\end{pmatrix}.
\]

Negative-weight entries vanish; weight-zero entries equal the identity.
This remains true over nonreduced \(R\).
Substitution into \(\bar g^{\,t}Hg=H\) gives
\(d=\bar b\) and
\[
 c+\bar c+b\bar b=0.
\]
The matrix is automatically invertible: its difference from the
identity has cube zero. Conversely these equations give an isometry
whose orbit is obtained by replacing \(b\) by \(zb\) and \(c\) by
\(z^2c\), with identity value at zero. Consequently

\[
 U_{(a)}(R)=
 \left\{
 \begin{pmatrix}1&c&b\\0&1&0\\0&\bar b&1\end{pmatrix}:
 b,c\in D_R,\ 
 \operatorname{Tr}_D(c)+N_D(b)=0
 \right\}.
\]

The trace has the section \(r\mapsto\omega r\). The substitution
\(c=\omega N_D(b)+c_0\), with
\(c_0\in\ker\operatorname{Tr}_D\), gives a scheme isomorphism

\[
 U_{(a)}\simeq \mathbf A(D)\times
                    \mathbf A(\ker\operatorname{Tr}_D)
              \simeq\mathbf A_k^7 .
\]

This is an isomorphism of schemes; it does not assert that the group
law is the additive law of a vector space.
On dual numbers the quadratic term \(N_D(b)\) has zero linear part.
Thus the tangent algebra has four dimensions in weight \(a\) and three
in weight \(2a\).
These are also the full corresponding weight spaces of \(\operatorname{Lie}G\):
before imposing the linearized isometry equation, its positive-weight
matrix positions are exactly \(b,d\) in weight \(a\) and \(c\) in
weight \(2a\); that equation imposes \(d=\bar b\) and
\(\operatorname{Tr}_D(c)=0\).
Therefore

\[
 \operatorname{Lie}U_{(a)}
   =\mathfrak g_a\oplus\mathfrak g_{2a},\qquad
 \dim\mathfrak g_a=4,\qquad\dim\mathfrak g_{2a}=3 .
\]

The weights here are algebraic torus characters, not their
differentials. The characters \(z\) and \(z^2\) are distinct even in
characteristic two.

## 7. Consequences for the printed statements

The group \((U_{(a)})_L\) is irreducible of dimension seven by §6.
Its intersection with \(O(Q)\) is a proper closed subset by §5.
It follows that the exact-generated closed subgroup \(E\), contained
in that intersection, has dimension strictly less than seven.
No claim about the sharper value of \(\dim E\) is needed.

Thus the exact generating definition cannot simultaneously have the
standard positive-multiple interpretation and the displayed 25.20
dimension formula for this example: the right side of that formula
is \(4+3=7\). The single-\(\mathfrak g_a\) Lie description also does
not describe the standard \(U_{(a)}\), whose Lie algebra has dimension
seven. These conclusions follow from the explicit matrix equations,
independently of the source's dimension formula.

To express the standard convention, include all absolute root groups
restricting to positive integral multiples of \(a\), and use the
corresponding positive integral weight span for the Lie algebra.
For this example that includes the \(2a\) groups and both displayed
Lie weight spaces. This note does not assert that exact-\(a\)
generation fails for every nonreduced relative root system or in
every characteristic.

## 8. The existing Library scope

Names in this paragraph lie in `Langlands.GroupScheme`.
`RelativeRootGroupAbsoluteGenerationStatement` and its published proof
`relativeRootGroupAbsoluteGeneration`, in
`Rational/RelativeRootGroupAbsoluteGenerationStatement.lean` and
`Rational/RelativeRootGroupAbsoluteGenerationProof.lean`, use the
condition

`β|_S = n • a` for some natural `n > 0`.

They assert containment and minimality among actual closed subgroup
functors on all tests, with an explicitly supplied containing maximal
torus and a field extension splitting it.
`RelativeRoot.tangentSubmodule_subgroup`, in
`Rational/RootSubgroupLieImage.lean`, uses the positive cyclic weight
span. These statements agree with the convention tested here.

This note leaves those Lean and paired Markdown files unchanged.
It supplies no formal quaternionic group, no formal counterexample and
no completion evidence for the standing algebraic-group program.
The unrelated explicitly paused Task 4733
(`0367ba06-f71f-44ff-83b2-e9de61795702`) and the other proof owners
retain their scopes and controls.

## 9. Sources and provenance

All PDF page numbers below are one-based. Sources are retained in the
project literature collection under the registered identifiers listed.
The quaternion algebra, rank argument, chosen torus, coordinate
calculations and obstruction in §§2–7 are derived arguments of this note.

| Registered source | Locations used |
| --- | --- |
| `milne-2017-algebraic-groups` — J. S. Milne, *Algebraic Groups*, 2017 | 25.13 and footnote 2, printed p.548/PDF p.564; 25.19–25.20, printed p.549/PDF p.565. |
| `milne-2022-algebraic-groups` — corrected reprint | Surrounding hypotheses and 25.19–25.20, printed pp.552–554/PDF pp.563–565; the latter items are on printed p.553/PDF p.564. |
| `milne-2017-algebraic-groups-errata-2026-11-02` | Complete retained official HTML snapshot; the 25.19 correction does not change the generating condition discussed here. |
| `milne-2022-algebraic-groups-errata-2026-11-04` | Complete retained official HTML snapshot; no correction supplying the positive-multiple or Lie reconciliation. |
| `knus-merkurjev-rost-tignol-1998-book-of-involutions` — M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions*, AMS, 1998 | §4.A and Theorem 4.2, printed pp.42–44/PDF pp.65–67, for the alternating qualification; §23.A, printed pp.345–347/PDF pp.368–370, for the actual isometry functor, smoothness and connectedness; Theorem 26.14 and proof, printed pp.369–370/PDF pp.392–393, for type \(C_3\) in arbitrary characteristic. |
| `book-involutions-author-errata-2026-11-13` — author errata and page-sorted comments | Complete `BoI-error.html` and `bois.txt` in the retained publication folder; neither changes the results used here. The author's corrections and separately labelled unedited comments are distinguished in that folder. |
| `borel-tits-1965-groupes-reductifs` — A. Borel and J. Tits, *Groupes réductifs*, 1965 | 3.8(ii), printed p.76/PDF p.23; 3.13(b), printed p.79/PDF p.26; 5.2, printed p.96/PDF p.43. |
| `borel-tits-1972-complements-groupes-reductifs` — *Compléments à l'article « Groupes réductifs »* | §5, printed pp.274–275/PDF pp.23–24, for the correction to 1965, 3.8(2). |
| `conrad-gabber-prasad-2015-pseudo-reductive` — B. Conrad, O. Gabber and G. Prasad, *Pseudo-reductive Groups*, second edition, 2015 | Proposition C.2.21, printed pp.615–616/PDF pp.641–642, for the positive-integral-weight and dynamic convention. |
