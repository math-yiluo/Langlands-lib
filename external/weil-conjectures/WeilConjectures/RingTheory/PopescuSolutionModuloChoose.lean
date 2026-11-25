/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.PopescuAdmissibleSubalgebra
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.RingTheory.PopescuQuotientBasisEnlargement
import Mathlib.RingTheory.LocalRing.Module

/-!
# Choosing elements in an admissible Popescu subalgebra

Source: Stacks Project, proofs of Tags 07FH and 07FI; the enlargement argument recorded
in the blueprint (blueprint: lem-weil-pbc-popescu-solution-modulo-choose).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

/-- Given an admissible `A₀`, enlarge it so elements of `Λ` mapping into it have residue
differentials forming a basis, and elements of `q` mapping into it generate `q L`.
The residue field is embedded into `κ(q)` compatibly with the quotient map.
Source: Stacks Project, proofs of Tags 07FH and 07FI, with the enlargement argument
recorded in the blueprint (blueprint: lem-weil-pbc-popescu-solution-modulo-choose).

Proof (the fifteen steps recorded in the blueprint):

1. *Setup.* $\Lambda_{\mathfrak q}$ is a local ring with maximal ideal $\mathfrak
q\Lambda_{\mathfrak q}$ and residue field $K$, and $\mathfrak q\Lambda_{\mathfrak
q}\cap\Lambda=\mathfrak q$ [def-weil-pbc-localization-at-prime]; it is Noetherian [lem-weil-pbc-
localization-noetherian]. Write $\pi:\Lambda\to\Lambda_{\mathfrak q}\to\bar\Lambda$ and
$x\mapsto\hat x$ for the residue map $\bar\Lambda\to K$. By [lem-weil-pbc-noetherian-local-
quotient-artinian-local] $\bar\Lambda$ is an Artinian local ring with maximal ideal
$\bar{\mathfrak m}=\mathfrak q\bar\Lambda$, $\bar{\mathfrak m}^n=0$; the kernel of
$\Lambda_{\mathfrak q}\to\bar\Lambda$ is $\mathfrak q^n\Lambda_{\mathfrak q}\subseteq\mathfrak
q\Lambda_{\mathfrak q}$, so the preimage of $\bar{\mathfrak m}$ in $\Lambda_{\mathfrak q}$ is
$\mathfrak q\Lambda_{\mathfrak q}$. Every element of $\bar\Lambda$ is the image of some $\mu/s$,
$\mu\in\Lambda$, $s\in\Lambda\setminus\mathfrak q$, and $\pi(s)$ is a unit of $\bar\Lambda$ for
$s\notin\mathfrak q$. As $k\to\bar\Lambda$ is injective, $p\cdot1=0$ in $\bar\Lambda$ and in
$K$. *The parenthetical claims of the statement.* Let $A\subseteq\bar\Lambda$ be admissible.
From $\mathfrak m_A\bar\Lambda=\bar{\mathfrak m}$ we get $\mathfrak m_A\subseteq
A\cap\bar{\mathfrak m}$, a proper ideal of $A$ ($1\notin\bar{\mathfrak m}$), so $\mathfrak
m_A=A\cap\bar{\mathfrak m}$ by maximality; hence $F=A/\mathfrak m_A\to\bar\Lambda/\bar{\mathfrak
m}=K$ is injective, a $k$-algebra map, and we regard $F$ as a subfield of $K$ containing $k$. An
element $x\in A$ with $\hat x\neq0$ lies outside $\mathfrak m_A$, hence is a unit of $A$. By
[lem-weil-pbc-artinian-local-noetherian-nilpotent] $A$ is Noetherian with nilpotent maximal
ideal, and by [lem-weil-pbc-artinian-local-unique-prime] $\mathfrak m_A$ is its only prime.
Uses: def-weil-pbc-localization-at-prime, lem-weil-pbc-localization-noetherian, lem-weil-pbc-
noetherian-local-quotient-artinian-local, lem-weil-pbc-artinian-local-noetherian-nilpotent, lem-
weil-pbc-artinian-local-unique-prime.

2. *The residue field $F_0$ of $A_0$ and the elements $a_j$.* $A_0$ is essentially of finite
type over $k$ [def-weil-pbc-essentially-finite-type-algebra]: $A_0\cong W^{-1}B$ with
$B=k[g_1,\dots,g_u]$ a finitely generated $k$-algebra [def-weil-pbc-finite-type-algebra]. Every
element of $A_0$ is $b/w$ with $b,w\in B$, so its residue lies in the subfield of
$F_0=A_0/\mathfrak m_{A_0}\subseteq K$ generated over $k$ by the residues of $g_1,\dots,g_u$:
$F_0/k$ is a finitely generated field extension [def-pc-field-extension]. By [lem-weil-pbc-
cartier-equality] $\Omega_{F_0/k}$ [def-weil-pbc-kahler-differentials] is a finite dimensional
$F_0$-vector space; it is spanned by the $\mathrm dc$, $c\in F_0$, so this spanning set contains
a basis $\mathrm dc_1,\dots,\mathrm dc_t$ ($t\ge0$). Choose $a_j\in A_0$ with $\hat a_j=c_j$
($A_0\to F_0$ is surjective).
Uses: def-weil-pbc-essentially-finite-type-algebra, def-weil-pbc-finite-type-algebra, def-pc-
field-extension, lem-weil-pbc-cartier-equality, def-weil-pbc-kahler-differentials.

3. *Generators.* If $n\ge2$: $A_0$ is Noetherian (step 1), so $\mathfrak
m_{A_0}=(b_1,\dots,b_r)$ for some $b_i\in\mathfrak m_{A_0}$ [def-weil-pbc-noetherian-ring];
since $A_0$ is admissible, $b_1,\dots,b_r$ generate the ideal $\mathfrak
m_{A_0}\bar\Lambda=\bar{\mathfrak m}$ of $\bar\Lambda$. If $n=1$: $\Lambda$ is Noetherian, so
$\mathfrak q=(\lambda'_1,\dots,\lambda'_r)$ for some $\lambda'_i\in\mathfrak q$ [def-weil-pbc-
noetherian-ring]; their images generate $\mathfrak q\Lambda_{\mathfrak q}$, and since
$\bar{\mathfrak m}=\mathfrak q\bar\Lambda=\mathfrak q\Lambda_{\mathfrak q}/\mathfrak
q\Lambda_{\mathfrak q}=0$, $\pi(\lambda'_i)=0$ lies in every subring of $\bar\Lambda$: these
$\lambda'_i$ satisfy (a) and (c) for every admissible $A$.
Uses: def-weil-pbc-noetherian-ring.

4. *A common denominator.* By step 1 write $a_j$ ($j\le t$) and, if $n\ge2$, $b_i$ ($i\le r$) as
images of fractions $\mu_j/s_j$, $\mu'_i/s'_i$ with $\mu_j,\mu'_i\in\Lambda$,
$s_j,s'_i\in\Lambda\setminus\mathfrak q$; with
$s=\prod_js_j\prod_is'_i\in\Lambda\setminus\mathfrak q$ ($\mathfrak q$ prime) and the numerators
multiplied by the other denominators we get $s\in\Lambda\setminus\mathfrak q$ and
$\mu_j,\mu'_i\in\Lambda$ with $\pi(\mu_j)=a_j\pi(s)$ and $\pi(\mu'_i)=b_i\pi(s)$. Since
$b_i\pi(s)\in\bar{\mathfrak m}$, $\mu'_i/1$ lies in the preimage $\mathfrak q\Lambda_{\mathfrak
q}$ of $\bar{\mathfrak m}$, so $\mu'_i\in\mathfrak q\Lambda_{\mathfrak q}\cap\Lambda=\mathfrak
q$ (step 1). Put $\bar s=\pi(s)$, a unit of $\bar\Lambda$, and $\alpha=\hat{\bar s}\in K$,
$\alpha\neq0$.
Uses: def-weil-pbc-localization-at-prime.

5. *Claim (first part of the proof of 07FI).* Let $D_1\subseteq\bar\Lambda$ be a subring which
is a local ring with $\mathfrak m_{D_1}=D_1\cap\bar{\mathfrak m}$, so that its residue field
$F_1$ is a subfield of $K$, and let $x\in\bar\Lambda$ with $\hat x\in F_1\setminus\{0\}$. Then
$x^q\in D_1$ for every power $q=p^e$ of $p$ with $q\ge n$. Proof: choose $y\in D_1$ with $\hat
y=\hat x^{-1}$; then $y\notin\mathfrak m_{D_1}$, so $y$ is a unit of $D_1$, and
$\varepsilon=yx-1\in\bar{\mathfrak m}$. As $p=0$ in $\bar\Lambda$,
$(1+\varepsilon)^{p^e}=1+\varepsilon^{p^e}$ (induction on $e$), and
$\varepsilon^q\in\bar{\mathfrak m}^q\subseteq\bar{\mathfrak m}^n=0$. So $(yx)^q=1$ and
$x^q=(y^{-1})^q\in D_1$.

6. *Two cases.* Either $\alpha$ is transcendental over $F_0$ (not a root of a nonzero polynomial
with coefficients in $F_0$ [def-weil-algebraic-element]; case T, steps 7-9) or $\alpha$ is
algebraic over $F_0$ (case S, steps 10-13). In each case we construct an admissible $A\supseteq
A_0$ with residue field $F\subseteq K$ and a power $N\ge p$ of $p$ with $\bar s^N\in A$, such
that in case T, $\bar s\in A$ and $\mathrm dc_1,\dots,\mathrm dc_t,\mathrm d\alpha$ is a basis
of $\Omega_{F/k}$, and in case S, $\mathrm dc_1,\dots,\mathrm dc_t$ is a basis of $\Omega_{F/k}$
(here $\mathrm dc_j$ denotes $\mathrm d$ of $c_j\in F_0\subseteq F$ in $\Omega_{F/k}$).
Uses: def-weil-algebraic-element.

7. *Case T: the ring $D'$ (as in 07FI, case transcendental).* Let $\theta:A_0[t]\to\bar\Lambda$
be the $A_0$-algebra map with $t\mapsto\bar s$ and $\mathfrak n=\theta^{-1}(\bar{\mathfrak m})$.
Since $A_0\subseteq\bar\Lambda$ is local, $\mathfrak m_{A_0}[t]\subseteq\mathfrak n$, and modulo
$\mathfrak m_{A_0}[t]$ the map $A_0[t]\to K$ is $F_0[t]\to K$, $t\mapsto\alpha$, which is
injective as $\alpha$ is transcendental over $F_0$; so $\mathfrak n=\mathfrak m_{A_0}[t]$, a
prime ideal ($A_0[t]/\mathfrak n=F_0[t]$ is a domain). Let $D'=A_0[t]_{\mathfrak n}$ [def-weil-
pbc-localization-at-prime]. $A_0[t]$ is Noetherian [lem-weil-pbc-finite-type-algebra-noetherian]
and so is $D'$ [lem-weil-pbc-localization-noetherian]. $D'/\mathfrak
m_{A_0}D'=(F_0[t])_{(0)}=F_0(t)$ is a field and $\mathfrak m_{A_0}D'$ is nilpotent ($\mathfrak
m_{A_0}$ is, step 1), so $\mathfrak m_{A_0}D'$ lies in every prime of $D'$ and is the maximal
ideal of the local ring $D'$; $D'$ is Artinian local [lem-weil-pbc-noetherian-local-quotient-
artinian-local] (with $K=0$ there), with residue field $F_0(t)$, and $A_0\to D'$ is local. Every
element of $A_0[t]\setminus\mathfrak n$ maps outside $\bar{\mathfrak m}$, i.e. to a unit of
$\bar\Lambda$, so $\theta$ extends to $\psi':D'\to\bar\Lambda$ [def-weil-pbc-localization-at-
prime], local ($\psi'^{-1}(\bar{\mathfrak m})=\mathfrak nD'$), restricting to the inclusion on
$A_0$, with $\psi'(t/1)=\bar s$; on residue fields it is $F_0(t)\to K$, $t\mapsto\alpha$.
Uses: def-weil-pbc-localization-at-prime, lem-weil-pbc-finite-type-algebra-noetherian, lem-weil-
pbc-localization-noetherian, lem-weil-pbc-noetherian-local-quotient-artinian-local.

8. *Case T: $A=\psi'(D')$ is admissible.* Apply [lem-weil-pbc-criterion-flatness-fibre-
noetherian] to $R=A_0$, $S=D'$, $S'=M=\bar\Lambda$: Noetherian local rings (steps 1, 7) and
local homomorphisms; $M$ is generated by $1$ and nonzero; $M/\mathfrak m_{A_0}M$ is a vector
space over the field $D'/\mathfrak m_{A_0}D'$, hence free and flat [def-weil-pbc-flat-ring-map];
$M$ is flat over $A_0$ ($A_0$ admissible). So $\psi'$ is flat; being local it is faithfully flat
[lem-weil-pbc-flat-local-hom-faithfully-flat] and so injective [lem-weil-pbc-faithfully-flat-
ideal-contraction] ($I=0$). Let $A=\psi'(D')\cong D'$, a $k$-subalgebra of $\bar\Lambda$
containing $A_0=\psi'(A_0)$ and $\bar s$: it is Artinian local, $A\to\bar\Lambda$ is flat, and
$\mathfrak m_A\bar\Lambda=\mathfrak m_{A_0}\bar\Lambda=\bar{\mathfrak m}$. Its residue field
$F\subseteq K$ is the image of $F_0(t)$, i.e. $F=F_0(\alpha)\cong F_0(t)$ ($t\mapsto\alpha$),
finitely generated over $k$ (by $\alpha$ and generators of $F_0$, step 2). Writing
$F=k(e_1,\dots,e_v)$, $F=W^{-1}k[e_1,\dots,e_v]$ with $W$ the nonzero elements of the domain
$k[e_1,\dots,e_v]$, so $k\to F$ is essentially of finite type [def-weil-pbc-essentially-finite-
type-algebra] [def-weil-pbc-finite-type-algebra], and by [lem-weil-pbc-artinian-local-
essentially-finite-type-residue] $A$ is essentially of finite type over $k$. So $A$ is
admissible, $A_0\subseteq A$, $\bar s\in A$; put $N=p$ (then $\bar s^N\in A$).
Uses: lem-weil-pbc-criterion-flatness-fibre-noetherian, def-weil-pbc-flat-ring-map, lem-weil-
pbc-flat-local-hom-faithfully-flat, lem-weil-pbc-faithfully-flat-ideal-contraction, def-weil-
pbc-essentially-finite-type-algebra, def-weil-pbc-finite-type-algebra, lem-weil-pbc-artinian-
local-essentially-finite-type-residue.

9. *Case T: a basis of $\Omega_{F/k}$.* By [lem-weil-pbc-kahler-differentials-polynomial-
extension] ($R=k$, $A=F_0$, $e=1$)
$\Omega_{F_0[t]/k}\cong(F_0[t]\otimes_{F_0}\Omega_{F_0/k})\oplus F_0[t]\,\mathrm dt$ via
$b\otimes\mathrm dc\mapsto b\,\mathrm dc$; as $\mathrm dc_1,\dots,\mathrm dc_t$ is an
$F_0$-basis of $\Omega_{F_0/k}$ (step 2), $\mathrm dc_1,\dots,\mathrm dc_t,\mathrm dt$ is an
$F_0[t]$-basis of $\Omega_{F_0[t]/k}$ [def-weil-pbc-kahler-differentials]. $F_0(t)$ is the
localization of $F_0[t]$ at its nonzero elements, so by [lem-weil-pbc-kahler-differentials-
localization] $\Omega_{F_0(t)/k}$ is the localization of $\Omega_{F_0[t]/k}$ and $\mathrm
dc_1,\dots,\mathrm dc_t,\mathrm dt$ is an $F_0(t)$-basis of it. Transporting along the
$k$-algebra isomorphism $F_0(t)\cong F$, $t\mapsto\alpha$, identity on $F_0$ (step 8), $\mathrm
dc_1,\dots,\mathrm dc_t,\mathrm d\alpha$ is an $F$-basis of $\Omega_{F/k}$.
Uses: theorem-finite-etale-covers-proper-henselian--2, def-weil-pbc-kahler-differentials,
lem-weil-pbc-kahler-differentials-localization.

10. *Case S: the field $F_1=F_0(\beta)$ (as in 07FI, case algebraic).* $\alpha$ is algebraic
over $F_0$, so $F_0(\alpha)/F_0$ is an algebraic extension and by [lem-weil-pbc-separable-first-
purely-inseparable] there is $Q=p^e$ ($e\ge0$) with $\beta:=\alpha^Q$ separable over $F_0$ [def-
weil-pbc-separable-algebraic-extension]; $\beta\neq0$. Let $F_1=F_0(\beta)\subseteq K$; it is
generated by $\beta$, so $F_1\cong F_0[T]/(\bar g)$, $\bar g$ the minimal polynomial of $\beta$,
is finite over $F_0$, and as the elements of $F_1$ separable over $F_0$ form a subfield
containing $F_0$ and $\beta$ [lem-weil-pbc-separable-first-purely-inseparable], $F_1/F_0$ is
finite and separable algebraic. Hence $\operatorname{Spec}F_1\to\operatorname{Spec}F_0$ is etale
[lem-weil-pbc-finite-separable-extension-etale]. $A_0$ and $\bar\Lambda$ are local rings whose
only prime is the maximal ideal [lem-weil-pbc-artinian-local-unique-prime], hence henselian
[lem-weil-pbc-henselian-of-nil-maximal-ideal]. By the essential surjectivity in [lem-weil-pbc-
henselian-finite-etale-equivalence] for $A_0$ and the finite etale $F_0$-algebra $F_1$ there is
a finite etale $A_0$-algebra $D'$ with an $F_0$-algebra isomorphism $D'/\mathfrak m_{A_0}D'\cong
F_1$. $D'$ is finite over $A_0$, hence Noetherian [lem-weil-pbc-finite-type-algebra-noetherian];
$\mathfrak m_{A_0}D'$ is nilpotent with quotient a field, so it is the maximal ideal of the
local ring $D'$, which is Artinian [lem-weil-pbc-noetherian-local-quotient-artinian-local] with
residue field $F_1$, and $A_0\to D'$ is local.
Uses: lem-weil-pbc-separable-first-purely-inseparable, def-weil-pbc-separable-algebraic-
extension, lem-weil-pbc-finite-separable-extension-etale, lem-weil-pbc-artinian-local-unique-
prime, lem-weil-pbc-henselian-of-nil-maximal-ideal, lem-weil-pbc-henselian-finite-etale-
equivalence, lem-weil-pbc-finite-type-algebra-noetherian, lem-weil-pbc-noetherian-local-
quotient-artinian-local.

11. *Case S: a factorization $A_0\to D'\to\bar\Lambda$ (Stacks: 'since $\bar\Lambda$ is
henselian and $F(\alpha^q)$ is contained in its residue field we can find a factorization').*
Let $\rho:D'\to F_1\subseteq K$ be the residue map composed with the isomorphism of step 10; on
$A_0$ it is the residue map $A_0\to F_0\subseteq K$. Let $B=D'\otimes_{A_0}\bar\Lambda$;
$\bar\Lambda\to B$, $x\mapsto1\otimes x$, is etale [lem-weil-pbc-etale-ring-base-change]. The
maps $\rho$ and $x\mapsto\hat x$ are ring maps $D'\to K$, $\bar\Lambda\to K$ agreeing on $A_0$,
so they define a ring map $\chi:B\to K$, $d\otimes x\mapsto\rho(d)\hat x$, surjective (already
on $1\otimes\bar\Lambda$). Its kernel $\mathfrak q'$ is a prime of $B$ lying over
$\bar{\mathfrak m}$, and $K=\bar\Lambda/\bar{\mathfrak m}\to B/\mathfrak q'\cong K$ is the
identity, an isomorphism. By [lem-weil-pbc-henselian-etale-retraction] ($\bar\Lambda$ henselian,
step 10) there is a $\bar\Lambda$-algebra map $\sigma:B\to\bar\Lambda$ with
$\sigma^{-1}(\bar{\mathfrak m})=\mathfrak q'$. Put $\psi'(d)=\sigma(d\otimes1)$. For $a\in A_0$,
$\psi'(a)=\sigma(1\otimes a)=a$, so $\psi'$ restricts to the inclusion on $A_0$. Reducing
$\sigma$ modulo $\bar{\mathfrak m}$ gives a $K$-algebra map $B/\mathfrak q'\to K$, which is the
inverse of the isomorphism $K\to B/\mathfrak q'$; hence
$\widehat{\psi'(d)}=\chi(d\otimes1)=\rho(d)$ for $d\in D'$. So $\psi'$ is local
($\psi'^{-1}(\bar{\mathfrak m})$ is a prime of $D'$, i.e. $\mathfrak m_{A_0}D'$, by [lem-weil-
pbc-artinian-local-unique-prime]) and induces on residue fields the inclusion $F_1\subseteq K$.
Uses: lem-weil-pbc-etale-ring-base-change, lem-weil-pbc-henselian-etale-retraction, lem-weil-
pbc-artinian-local-unique-prime.

12. *Case S: $A=\psi'(D')$ is admissible and $\bar s^N\in A$.* As in step 8, [lem-weil-pbc-
criterion-flatness-fibre-noetherian] for $A_0\to D'\to\bar\Lambda$ and $M=\bar\Lambda$
($M/\mathfrak m_{A_0}M$ is a vector space over the field $D'/\mathfrak m_{A_0}D'\cong F_1$,
hence flat [def-weil-pbc-flat-ring-map]; $M$ flat over $A_0$) shows that $\psi'$ is flat; it is
local, hence faithfully flat [lem-weil-pbc-flat-local-hom-faithfully-flat] and injective [lem-
weil-pbc-faithfully-flat-ideal-contraction]. $A=\psi'(D')\cong D'$ is a $k$-subalgebra of
$\bar\Lambda$ containing $A_0$, Artinian local, flat into $\bar\Lambda$, with $\mathfrak
m_A\bar\Lambda=\mathfrak m_{A_0}\bar\Lambda=\bar{\mathfrak m}$ and residue field
$F=F_1=F_0(\beta)\subseteq K$ (step 11), finitely generated over $k$; as in step 8, $k\to F$ is
essentially of finite type [def-weil-pbc-essentially-finite-type-algebra] [def-weil-pbc-finite-
type-algebra] and so is $k\to A$ [theorem-finite-etale-covers-proper-henselian--2].
So $A$ is admissible and $A_0\subseteq A$. By the Claim (step 5) for $D_1=A$ (local with
$\mathfrak m_A=A\cap\bar{\mathfrak m}$, step 1) and $x=\bar s^Q$, whose residue $\beta\in F$ is
nonzero, $\bar s^{Qq'}\in A$ for a power $q'$ of $p$ with $q'\ge\max(n,p)$. Put $N=Qq'$, a power
of $p$ with $N\ge p$.
Uses: lem-weil-pbc-criterion-flatness-fibre-noetherian, def-weil-pbc-flat-ring-map, lem-weil-
pbc-flat-local-hom-faithfully-flat, lem-weil-pbc-faithfully-flat-ideal-contraction, def-weil-
pbc-essentially-finite-type-algebra, def-weil-pbc-finite-type-algebra, lem-weil-pbc-artinian-
local-essentially-finite-type-residue.

13. *Case S: a basis of $\Omega_{F/k}$.* $F/F_0$ is finite separable (step 10), so
$\operatorname{Spec}F\to\operatorname{Spec}F_0$ is etale [lem-weil-pbc-finite-separable-
extension-etale], i.e. $H_1(L_{F/F_0})=0$ and $\Omega_{F/F_0}=0$ [lem-weil-pbc-etale-ring-map-
iff-etale-affine]. The Jacobi-Zariski sequence [lem-weil-pbc-jacobi-zariski-homology-sequence]
for $k\to F_0\to F$ contains the exact piece $H_1(L_{F/F_0})\xrightarrow{\partial}F\otimes_{F_0}
\Omega_{F_0/k}\xrightarrow{w}\Omega_{F/k}\xrightarrow{z}\Omega_{F/F_0}\to0$, with
$w(c\otimes\mathrm db)=c\,\mathrm db$; so $w$ is an isomorphism. Since $\mathrm
dc_1,\dots,\mathrm dc_t$ is an $F_0$-basis of $\Omega_{F_0/k}$ (step 2), $1\otimes\mathrm dc_j$
is an $F$-basis of $F\otimes_{F_0}\Omega_{F_0/k}$, and its image $\mathrm dc_1,\dots,\mathrm
dc_t$ is an $F$-basis of $\Omega_{F/k}$ [def-weil-pbc-kahler-differentials].
Uses: lem-weil-pbc-finite-separable-extension-etale, lem-weil-pbc-etale-ring-map-iff-etale-
affine, lem-weil-pbc-jacobi-zariski-homology-sequence, def-weil-pbc-kahler-differentials.

14. *The elements $\lambda_j$ and (a), (b).* In both cases let $A$, $F$, $N$ be as constructed
(steps 8, 12). Put $\lambda_j=\mu_js^{N-1}\in\Lambda$ for $j=1,\dots,t$, and in case T also
$\lambda_{t+1}=s$ (so the number of $\lambda$'s is $t$ in case S and $t+1$ in case T). By step
4, $\pi(\lambda_j)=a_j\bar s\,\bar s^{N-1}=a_j\bar s^N\in A$ ($a_j\in A_0\subseteq A$, $\bar
s^N\in A$), and in case T $\pi(s)=\bar s\in A$. The residues are $c_j\alpha^N$ and, in case T,
$\alpha$; here $\alpha^N=\widehat{\bar s^N}\in F\setminus\{0\}$. By the Leibniz rule in
$\Omega_{F/k}$ [def-weil-pbc-kahler-differentials], $\mathrm d(c_j\alpha^N)=\alpha^N\mathrm
dc_j+Nc_j\alpha^{N-1}\mathrm d\alpha=\alpha^N\mathrm dc_j$, since $p\mid N$ and $p=0$ in $F$ (in
case S, $\alpha^{N-1}$ need not lie in $F$, but $N\alpha^{N-1}\mathrm d\alpha$ is not needed:
write $c_j\alpha^N$ as $c_j\cdot\gamma$ with $\gamma=\alpha^N\in F$ and
$\gamma=(\alpha^Q)^{q'}=\beta^{q'}$, so $\mathrm d\gamma=q'\beta^{q'-1}\mathrm d\beta=0$ as
$p\mid q'$; in case T likewise $\gamma=\alpha^p$, $\mathrm d\gamma=p\alpha^{p-1}\mathrm
d\alpha=0$). Hence the differentials of the residues are $\alpha^N\mathrm
dc_1,\dots,\alpha^N\mathrm dc_t$ in case S, a basis of $\Omega_{F/k}$ by step 13 ($\alpha^N\in
F^\times$), and $\alpha^N\mathrm dc_1,\dots,\alpha^N\mathrm dc_t,\mathrm d\alpha$ in case T, a
basis by step 9. This proves (a) and (b) for the $\lambda$'s.
Uses: def-weil-pbc-kahler-differentials.

15. *The elements $\lambda'_i$ and (a), (c).* For $n=1$ take the $\lambda'_i$ of step 3. For
$n\ge2$ put $\lambda'_i=\mu'_is^{N-1}$ ($i=1,\dots,r$); $\lambda'_i\in\mathfrak q$ as
$\mu'_i\in\mathfrak q$ (step 4), and $\pi(\lambda'_i)=b_i\bar s^N\in A$ (a). Let
$J\subseteq\mathfrak q\Lambda_{\mathfrak q}$ be the ideal generated by the images of the
$\lambda'_i$. Its image in $\bar\Lambda$ is generated by the $b_i\bar s^N$, which generate
$\bar{\mathfrak m}$ (step 3; $\bar s$ is a unit); as $\mathfrak q\Lambda_{\mathfrak q}$ is the
preimage of $\bar{\mathfrak m}$ and contains the kernel $\mathfrak q^n\Lambda_{\mathfrak q}$
(step 1), $J+\mathfrak q^n\Lambda_{\mathfrak q}=\mathfrak q\Lambda_{\mathfrak q}$, so, as
$n\ge2$, $J+(\mathfrak q\Lambda_{\mathfrak q})\cdot(\mathfrak q\Lambda_{\mathfrak q})=\mathfrak
q\Lambda_{\mathfrak q}$. The $\Lambda_{\mathfrak q}$-module $\mathfrak q\Lambda_{\mathfrak q}$
is finitely generated ($\Lambda_{\mathfrak q}$ Noetherian [def-weil-pbc-noetherian-ring]), so by
Nakayama [lem-weil-pbc-nakayama-local-generators] (submodule $J$ whose image in $M/\mathfrak mM$
is everything) $J=\mathfrak q\Lambda_{\mathfrak q}$, which is (c). Together with step 14, the
admissible $A\supseteq A_0$ with residue field $F$, the $\lambda_j$ and the $\lambda'_i$ satisfy
(a), (b), (c).
Uses: def-weil-pbc-noetherian-ring, lem-weil-pbc-nakayama-local-generators.
-/
theorem exists_popescu_admissible_differential_basis
    (k : Type u) (Λ : Type v) [Field k] [CommRing Λ] [Algebra k Λ]
    [IsNoetherianRing Λ] (p : ℕ) [CharP k p] (hp : 0 < p)
    (hreg : IsGeometricallyRegular k Λ) (q : Ideal Λ) [q.IsPrime]
    (n : ℕ) (hn : 1 ≤ n)
    (A₀ : Subalgebra k (Localization.AtPrime q ⧸
      (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))
    (hA₀ : A₀.IsPopescuAdmissible ((q.map (algebraMap Λ (Localization.AtPrime q))).map
      (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)))) :
    ∃ (A : Subalgebra k (Localization.AtPrime q ⧸
        (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)) (_ : IsLocalRing A),
      A₀ ≤ A ∧
      A.IsPopescuAdmissible ((q.map (algebraMap Λ (Localization.AtPrime q))).map
        (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))) ∧
      IsLocalRing.maximalIdeal A = Ideal.comap A.val.toRingHom
        ((q.map (algebraMap Λ (Localization.AtPrime q))).map
          (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))) ∧
      ∃ (ι : IsLocalRing.ResidueField A →ₐ[k] q.ResidueField),
        Function.Injective ι ∧
        (∀ (a : A) (x : Localization.AtPrime q),
          (a : Localization.AtPrime q ⧸
            (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) =
            Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) x →
          ι (IsLocalRing.residue A a) = IsLocalRing.residue (Localization.AtPrime q) x) ∧
        ∃ (t r : ℕ) (xs : Fin t → Λ) (ys : Fin r → Λ)
          (a : Fin t → A) (a' : Fin r → A),
          (∀ j, (a j : Localization.AtPrime q ⧸
            (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) =
            Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)
              (algebraMap Λ (Localization.AtPrime q) (xs j))) ∧
          (∀ i, ys i ∈ q ∧ (a' i : Localization.AtPrime q ⧸
            (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) =
            Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)
              (algebraMap Λ (Localization.AtPrime q) (ys i))) ∧
          (∃ b : Module.Basis (Fin t) (IsLocalRing.ResidueField A)
              (KaehlerDifferential k (IsLocalRing.ResidueField A)),
            ∀ j, b j = KaehlerDifferential.D k (IsLocalRing.ResidueField A)
              (IsLocalRing.residue A (a j))) ∧
          Ideal.span (Set.range (fun i => algebraMap Λ (Localization.AtPrime q) (ys i))) =
            q.map (algebraMap Λ (Localization.AtPrime q)) := by
  classical
  let L := Localization.AtPrime q
  let m : Ideal L := q.map (algebraMap Λ L)
  let B := L ⧸ m ^ n
  let π : L →+* B := Ideal.Quotient.mk (m ^ n)
  have hm : m = IsLocalRing.maximalIdeal L :=
    IsLocalization.AtPrime.map_eq_maximalIdeal q L
  have hpow : m ^ n ≤ m := Ideal.pow_le_self (by omega)
  let f : B →ₐ[k] q.ResidueField := Ideal.Quotient.liftₐ (m ^ n)
    (IsScalarTower.toAlgHom k L q.ResidueField) (fun x hx ↦ by
      change IsLocalRing.residue L x = 0
      exact (IsLocalRing.residue_eq_zero_iff x).mpr (hm ▸ hpow hx))
  have hf : RingHom.ker f.toRingHom = m.map π := by
    dsimp only [f, Ideal.Quotient.liftₐ]
    rw [Ideal.ker_quotient_lift]
    change (RingHom.ker (IsLocalRing.residue L)).map π = m.map π
    rw [IsLocalRing.ker_residue, ← hm]
  obtain ⟨A, hlocal, hle, hAdm, t, r, xs, ys, a, a', ha, ha', hb, hspan⟩ :=
    exists_popescu_admissible_quotient_basis k Λ p hp hreg q n hn A₀ hA₀
  let : IsLocalRing A := hlocal
  have hmap : (IsLocalRing.maximalIdeal A).map A.val.toRingHom = m.map π := by
    obtain ⟨_, _, hlocal', _, hmap⟩ := hAdm
    exact hmap
  have hmax : IsLocalRing.maximalIdeal A = Ideal.comap A.val.toRingHom (m.map π) := by
    apply Ideal.IsMaximal.eq_of_le (IsLocalRing.maximalIdeal.isMaximal A)
    · rw [← hf, RingHom.comap_ker]
      exact RingHom.ker_ne_top (f.toRingHom.comp A.val.toRingHom)
    · rw [← hmap]
      exact Ideal.le_comap_map
  let ι : IsLocalRing.ResidueField A →ₐ[k] q.ResidueField :=
    Ideal.Quotient.liftₐ (IsLocalRing.maximalIdeal A) (f.comp A.val) (fun x hx ↦ by
      apply RingHom.mem_ker.mp
      change (x : B) ∈ RingHom.ker f.toRingHom
      rw [hf]
      change x ∈ Ideal.comap A.val.toRingHom (m.map π)
      rwa [← hmax])
  refine ⟨A, hlocal, hle, hAdm, hmax, ι, ι.injective, ?_, ?_⟩
  · intro z x hz
    change f (z : B) = IsLocalRing.residue L x
    rw [hz]
    rfl
  · by_cases hn1 : n = 1
    · obtain ⟨r', zs, hzs⟩ :=
        Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian q)
      have hzmem : ∀ i, zs i ∈ q := fun i ↦ hzs ▸ Ideal.subset_span ⟨i, rfl⟩
      have hzero : ∀ i, π (algebraMap Λ L (zs i)) = 0 := by
        intro i
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        simpa [hn1] using (Ideal.mem_map_of_mem (algebraMap Λ L) (hzmem i))
      refine ⟨t, r', xs, zs, a, fun _ ↦ 0, ha, ?_, hb, ?_⟩
      · intro i
        exact ⟨hzmem i, (hzero i).symm⟩
      · have h := congrArg (Ideal.map (algebraMap Λ L)) hzs
        rwa [Ideal.map_span, ← Set.range_comp] at h
    · have hn2 : 2 ≤ n := by omega
      have hJle : Ideal.span (Set.range (fun i ↦ algebraMap Λ L (ys i))) ≤ m := by
        apply Ideal.span_le.mpr
        rintro _ ⟨i, rfl⟩
        exact Ideal.mem_map_of_mem _ (ha' i).1
      have hJmap : (Ideal.span (Set.range (fun i ↦ algebraMap Λ L (ys i)))).map π =
          m.map π := by
        rw [Ideal.map_span, ← Set.range_comp]
        exact hspan
      have hsup : m ≤ Ideal.span (Set.range (fun i ↦ algebraMap Λ L (ys i))) ⊔ m ^ n := by
        have h := congrArg (Ideal.comap π) hJmap
        rw [Ideal.comap_map_quotientMk, Ideal.comap_map_mk hpow] at h
        exact le_of_eq (h.symm.trans (sup_comm _ _))
      have hJ : Ideal.span (Set.range (fun i ↦ algebraMap Λ L (ys i))) = m := by
        apply le_antisymm hJle
        apply Submodule.le_of_le_smul_of_le_jacobson_bot (I := m)
          (IsNoetherian.noetherian m)
        · rw [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal L) bot_ne_top, ← hm]
        · exact hsup.trans (sup_le_sup_left
            (by simpa [Ideal.smul_eq_mul, pow_two] using
              (Ideal.pow_le_pow_right (I := m) hn2)) _)
      exact ⟨t, r, xs, ys, a, a', ha, ha', hb, hJ⟩

end Algebra
