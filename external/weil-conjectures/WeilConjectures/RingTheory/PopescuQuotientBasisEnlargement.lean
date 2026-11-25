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
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Localization.Integer
import WeilConjectures.RingTheory.PopescuDenominatorBasisEnlargement

/-!
# Enlargement before lifting generators

Source: Stacks Project, proofs of Tags 07FH and 07FI, and steps 2–14 of
lem-weil-pbc-popescu-solution-modulo-choose.
(blueprint: lem-weil-pbc-popescu-quotient-basis-enlargement).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

private theorem exists_residue_differential_basis
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [EssFiniteType k A] :
    ∃ (t : ℕ) (a : Fin t → A)
      (b : Module.Basis (Fin t) (IsLocalRing.ResidueField A)
        (KaehlerDifferential k (IsLocalRing.ResidueField A))),
      ∀ j, b j = KaehlerDifferential.D k (IsLocalRing.ResidueField A)
        (IsLocalRing.residue A (a j)) := by
  classical
  let F := IsLocalRing.ResidueField A
  let : EssFiniteType k F :=
    EssFiniteType.of_surjective (Ideal.Quotient.mkₐ k (IsLocalRing.maximalIdeal A))
      Ideal.Quotient.mk_surjective
  let b := Module.Basis.ofSpan
    (le_of_eq (KaehlerDifferential.span_range_derivation k F).symm)
  have finish {ι : Type v} (b : Module.Basis ι F (KaehlerDifferential k F))
      (hb : Set.range b ⊆ Set.range (KaehlerDifferential.D k F)) :
      ∃ (t : ℕ) (a : Fin t → A)
        (b : Module.Basis (Fin t) F (KaehlerDifferential k F)),
        ∀ j, b j = KaehlerDifferential.D k F (IsLocalRing.residue A (a j)) := by
    have : Finite ι := b.linearIndependent.finite
    let : Fintype ι := Fintype.ofFinite _
    let e := Fintype.equivFin ι
    let b' := b.reindex e
    have hb' : ∀ j, ∃ a : A, b' j = KaehlerDifferential.D k F (IsLocalRing.residue A a) := by
      intro j
      obtain ⟨c, hc⟩ := hb (Set.mem_range_self (e.symm j))
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := A) c
      exact ⟨a, by simpa [b', Module.Basis.reindex_apply] using hc.symm⟩
    choose a ha using hb'
    exact ⟨Fintype.card ι, a, b', ha⟩
  exact finish b (Module.Basis.ofSpan_subset _)


private theorem common_denominator
    {Λ : Type v} [CommRing Λ] (q : Ideal Λ) [q.IsPrime]
    (n : ℕ) {ι : Type*} [Finite ι]
    (z : ι → Localization.AtPrime q ⧸ (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) :
    ∃ (s : Λ) (_ : s ∉ q) (μ : ι → Λ), ∀ i,
      Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)
        (algebraMap Λ (Localization.AtPrime q) (μ i)) =
      z i * Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)
        (algebraMap Λ (Localization.AtPrime q) s) := by
  classical
  let L := Localization.AtPrime q
  let J := q.map (algebraMap Λ L)
  choose l hl using fun i ↦ Ideal.Quotient.mk_surjective (I := J ^ n) (z i)
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite q.primeCompl l
  choose μ hμ using hs
  refine ⟨s, s.property, μ, fun i ↦ ?_⟩
  have he := congrArg (Ideal.Quotient.mk (J ^ n)) (hμ i)
  simpa only [Algebra.smul_def, map_mul, hl, mul_comm] using he

private theorem span_range_mul_unit
    {B : Type*} [CommRing B] {ι : Type*} (z : ι → B) {c : B} (hc : IsUnit c) :
    Ideal.span (Set.range (fun i ↦ z i * c)) = Ideal.span (Set.range z) := by
  simp_rw [Ideal.span_range_eq_iSup, Ideal.span_singleton_mul_right_unit hc]

/-- Enlarge an admissible subalgebra to obtain a differential basis from elements of the
original ring and generators of the maximal ideal in the truncated quotient. This statement
only concerns the quotient: it does not assert generation of the localized prime ideal.
Source: Stacks Project, proofs of Tags 07FH and 07FI, with the enlargement argument in
steps 2–14 of lem-weil-pbc-popescu-solution-modulo-choose.
(blueprint: lem-weil-pbc-popescu-quotient-basis-enlargement).

Proof (the enlargement part of the original fifteen-step argument):

1. *Setup.* $\Lambda_{\mathfrak q}$ is a local ring with maximal ideal $\mathfrak
q\Lambda_{\mathfrak q}$ and residue field $K$, and $\mathfrak q\Lambda_{\mathfrak
q}\cap\Lambda=\mathfrak q$ [def-weil-pbc-localization-at-prime]; it is Noetherian
[lem-weil-pbc-localization-noetherian]. Write $\pi:\Lambda\to\Lambda_{\mathfrak q}\to\bar\Lambda$
and $x\mapsto\hat x$ for the residue map $\bar\Lambda\to K$. By
[lem-weil-pbc-noetherian-local-quotient-artinian-local] $\bar\Lambda$ is an Artinian local ring with
maximal ideal $\bar{\mathfrak m}=\mathfrak q\bar\Lambda$, $\bar{\mathfrak m}^n=0$; the kernel of
$\Lambda_{\mathfrak q}\to\bar\Lambda$ is $\mathfrak q^n\Lambda_{\mathfrak q}\subseteq\mathfrak
q\Lambda_{\mathfrak q}$, so the preimage of $\bar{\mathfrak m}$ in $\Lambda_{\mathfrak q}$ is
$\mathfrak q\Lambda_{\mathfrak q}$. Every element of $\bar\Lambda$ is the image of some $\mu/s$,
$\mu\in\Lambda$, $s\in\Lambda\setminus\mathfrak q$, and $\pi(s)$ is a unit of $\bar\Lambda$ for
$s\notin\mathfrak q$. As $k\to\bar\Lambda$ is injective, $p\cdot1=0$ in $\bar\Lambda$ and in $K$.
*The parenthetical claims of the statement.* Let $A\subseteq\bar\Lambda$ be admissible. From
$\mathfrak m_A\bar\Lambda=\bar{\mathfrak m}$ we get $\mathfrak m_A\subseteq A\cap\bar{\mathfrak m}$,
a proper ideal of $A$ ($1\notin\bar{\mathfrak m}$), so $\mathfrak m_A=A\cap\bar{\mathfrak m}$ by
maximality; hence $F=A/\mathfrak m_A\to\bar\Lambda/\bar{\mathfrak m}=K$ is injective, a $k$-algebra
map, and we regard $F$ as a subfield of $K$ containing $k$. An element $x\in A$ with $\hat x\neq0$
lies outside $\mathfrak m_A$, hence is a unit of $A$. By
[lem-weil-pbc-artinian-local-noetherian-nilpotent] $A$ is Noetherian with nilpotent maximal ideal,
and by [lem-weil-pbc-artinian-local-unique-prime] $\mathfrak m_A$ is its only prime.
Uses: def-weil-pbc-localization-at-prime, lem-weil-pbc-localization-noetherian,
lem-weil-pbc-noetherian-local-quotient-artinian-local,
lem-weil-pbc-artinian-local-noetherian-nilpotent, lem-weil-pbc-artinian-local-unique-prime.

2. The residue field F₀ of A₀ is essentially of finite type over k, since it is the quotient of A₀
by its maximal ideal (Algebra.EssFiniteType quotient instance). Thus KaehlerDifferential.finite
gives finiteness of Ω[F₀/k] directly, without the Cartier equality.
KaehlerDifferential.span_range_derivation says it is spanned by exact differentials. Select a finite
basis from this spanning set and lift its elements through the surjective residue map A₀ → F₀. This
is the basis dc₁,...,dc_t and the lifts a_j needed for the common-denominator argument.
Uses: def-weil-pbc-essentially-finite-type-algebra, def-weil-pbc-kahler-differentials.

3. If n ≥ 2, A₀ is Noetherian because it is Artinian. Choose finite generators b_i of its maximal
ideal. Admissibility says that their images generate the ambient quotient maximal ideal. If n = 1,
the ambient quotient maximal ideal is zero; choose the empty generator family. No generators of q in
the original ring are needed at this stage.
Uses: def-weil-pbc-noetherian-ring.

4. *A common denominator.* By step 1 write $a_j$ ($j\le t$) and, if $n\ge2$, $b_i$ ($i\le r$) as
images of fractions $\mu_j/s_j$, $\mu'_i/s'_i$ with $\mu_j,\mu'_i\in\Lambda$,
$s_j,s'_i\in\Lambda\setminus\mathfrak q$; with $s=\prod_js_j\prod_is'_i\in\Lambda\setminus\mathfrak
q$ ($\mathfrak q$ prime) and the numerators multiplied by the other denominators we get
$s\in\Lambda\setminus\mathfrak q$ and $\mu_j,\mu'_i\in\Lambda$ with $\pi(\mu_j)=a_j\pi(s)$ and
$\pi(\mu'_i)=b_i\pi(s)$. Since $b_i\pi(s)\in\bar{\mathfrak m}$, $\mu'_i/1$ lies in the preimage
$\mathfrak q\Lambda_{\mathfrak q}$ of $\bar{\mathfrak m}$, so $\mu'_i\in\mathfrak
q\Lambda_{\mathfrak q}\cap\Lambda=\mathfrak q$ (step 1). Put $\bar s=\pi(s)$, a unit of
$\bar\Lambda$, and $\alpha=\hat{\bar s}\in K$, $\alpha\neq0$.
Uses: def-weil-pbc-localization-at-prime.

5. *Claim (first part of the proof of 07FI).* Let $D_1\subseteq\bar\Lambda$ be a subring which is a
local ring with $\mathfrak m_{D_1}=D_1\cap\bar{\mathfrak m}$, so that its residue field $F_1$ is a
subfield of $K$, and let $x\in\bar\Lambda$ with $\hat x\in F_1\setminus\{0\}$. Then $x^q\in D_1$ for
every power $q=p^e$ of $p$ with $q\ge n$. Proof: choose $y\in D_1$ with $\hat y=\hat x^{-1}$; then
$y\notin\mathfrak m_{D_1}$, so $y$ is a unit of $D_1$, and $\varepsilon=yx-1\in\bar{\mathfrak m}$.
As $p=0$ in $\bar\Lambda$, $(1+\varepsilon)^{p^e}=1+\varepsilon^{p^e}$ (induction on $e$), and
$\varepsilon^q\in\bar{\mathfrak m}^q\subseteq\bar{\mathfrak m}^n=0$. So $(yx)^q=1$ and
$x^q=(y^{-1})^q\in D_1$.
Uses: .

6. *Two cases.* Either $\alpha$ is transcendental over $F_0$ (not a root of a nonzero polynomial
with coefficients in $F_0$ [def-weil-algebraic-element]; case T, steps 7-9) or $\alpha$ is algebraic
over $F_0$ (case S, steps 10-13). In each case we construct an admissible $A\supseteq A_0$ with
residue field $F\subseteq K$ and a power $N\ge p$ of $p$ with $\bar s^N\in A$, such that in case T,
$\bar s\in A$ and $\mathrm dc_1,\dots,\mathrm dc_t,\mathrm d\alpha$ is a basis of $\Omega_{F/k}$,
and in case S, $\mathrm dc_1,\dots,\mathrm dc_t$ is a basis of $\Omega_{F/k}$ (here $\mathrm dc_j$
denotes $\mathrm d$ of $c_j\in F_0\subseteq F$ in $\Omega_{F/k}$).
Uses: def-weil-algebraic-element.

7. *Case T: the ring $D'$ (as in 07FI, case transcendental).* Let $\theta:A_0[t]\to\bar\Lambda$ be
the $A_0$-algebra map with $t\mapsto\bar s$ and $\mathfrak n=\theta^{-1}(\bar{\mathfrak m})$. Since
$A_0\subseteq\bar\Lambda$ is local, $\mathfrak m_{A_0}[t]\subseteq\mathfrak n$, and modulo
$\mathfrak m_{A_0}[t]$ the map $A_0[t]\to K$ is $F_0[t]\to K$, $t\mapsto\alpha$, which is injective
as $\alpha$ is transcendental over $F_0$; so $\mathfrak n=\mathfrak m_{A_0}[t]$, a prime ideal
($A_0[t]/\mathfrak n=F_0[t]$ is a domain). Let $D'=A_0[t]_{\mathfrak n}$
[def-weil-pbc-localization-at-prime]. $A_0[t]$ is Noetherian
[lem-weil-pbc-finite-type-algebra-noetherian] and so is $D'$ [lem-weil-pbc-localization-noetherian].
$D'/\mathfrak m_{A_0}D'=(F_0[t])_{(0)}=F_0(t)$ is a field and $\mathfrak m_{A_0}D'$ is nilpotent
($\mathfrak m_{A_0}$ is, step 1), so $\mathfrak m_{A_0}D'$ lies in every prime of $D'$ and is the
maximal ideal of the local ring $D'$; $D'$ is Artinian local
[lem-weil-pbc-noetherian-local-quotient-artinian-local] (with $K=0$ there), with residue field
$F_0(t)$, and $A_0\to D'$ is local. Every element of $A_0[t]\setminus\mathfrak n$ maps outside
$\bar{\mathfrak m}$, i.e. to a unit of $\bar\Lambda$, so $\theta$ extends to
$\psi':D'\to\bar\Lambda$ [def-weil-pbc-localization-at-prime], local ($\psi'^{-1}(\bar{\mathfrak
m})=\mathfrak nD'$), restricting to the inclusion on $A_0$, with $\psi'(t/1)=\bar s$; on residue
fields it is $F_0(t)\to K$, $t\mapsto\alpha$.
Uses: def-weil-pbc-localization-at-prime, lem-weil-pbc-finite-type-algebra-noetherian,
lem-weil-pbc-localization-noetherian, lem-weil-pbc-noetherian-local-quotient-artinian-local.

8. *Case T: $A=\psi'(D')$ is admissible.* Apply [lem-weil-pbc-criterion-flatness-fibre-noetherian]
to $R=A_0$, $S=D'$, $S'=M=\bar\Lambda$: Noetherian local rings (steps 1, 7) and local homomorphisms;
$M$ is generated by $1$ and nonzero; $M/\mathfrak m_{A_0}M$ is a vector space over the field
$D'/\mathfrak m_{A_0}D'$, hence free and flat [def-weil-pbc-flat-ring-map]; $M$ is flat over $A_0$
($A_0$ admissible). So $\psi'$ is flat; being local it is faithfully flat
[lem-weil-pbc-flat-local-hom-faithfully-flat] and so injective
[lem-weil-pbc-faithfully-flat-ideal-contraction] ($I=0$). Let $A=\psi'(D')\cong D'$, a
$k$-subalgebra of $\bar\Lambda$ containing $A_0=\psi'(A_0)$ and $\bar s$: it is Artinian local,
$A\to\bar\Lambda$ is flat, and $\mathfrak m_A\bar\Lambda=\mathfrak m_{A_0}\bar\Lambda=\bar{\mathfrak
m}$. Its residue field $F\subseteq K$ is the image of $F_0(t)$, i.e. $F=F_0(\alpha)\cong F_0(t)$
($t\mapsto\alpha$), finitely generated over $k$ (by $\alpha$ and generators of $F_0$, step 2).
Writing $F=k(e_1,\dots,e_v)$, $F=W^{-1}k[e_1,\dots,e_v]$ with $W$ the nonzero elements of the domain
$k[e_1,\dots,e_v]$, so $k\to F$ is essentially of finite type
[def-weil-pbc-essentially-finite-type-algebra] [def-weil-pbc-finite-type-algebra], and by
[theorem-finite-etale-covers-proper-henselian--2] $A$ is essentially of finite type over
$k$. So $A$ is admissible, $A_0\subseteq A$, $\bar s\in A$; put $N=p$ (then $\bar s^N\in A$).
Uses: lem-weil-pbc-criterion-flatness-fibre-noetherian, def-weil-pbc-flat-ring-map,
lem-weil-pbc-flat-local-hom-faithfully-flat, lem-weil-pbc-faithfully-flat-ideal-contraction,
def-weil-pbc-essentially-finite-type-algebra, def-weil-pbc-finite-type-algebra,
theorem-finite-etale-covers-proper-henselian--2.

9. *Case T: a basis of $\Omega_{F/k}$.* By [theorem-finite-etale-covers-proper-henselian--2]
($R=k$, $A=F_0$, $e=1$) $\Omega_{F_0[t]/k}\cong(F_0[t]\otimes_{F_0}\Omega_{F_0/k})\oplus
F_0[t]\,\mathrm dt$ via $b\otimes\mathrm dc\mapsto b\,\mathrm dc$; as $\mathrm dc_1,\dots,\mathrm
dc_t$ is an $F_0$-basis of $\Omega_{F_0/k}$ (step 2), $\mathrm dc_1,\dots,\mathrm dc_t,\mathrm dt$
is an $F_0[t]$-basis of $\Omega_{F_0[t]/k}$ [def-weil-pbc-kahler-differentials]. $F_0(t)$ is the
localization of $F_0[t]$ at its nonzero elements, so by
[lem-weil-pbc-kahler-differentials-localization] $\Omega_{F_0(t)/k}$ is the localization of
$\Omega_{F_0[t]/k}$ and $\mathrm dc_1,\dots,\mathrm dc_t,\mathrm dt$ is an $F_0(t)$-basis of it.
Transporting along the $k$-algebra isomorphism $F_0(t)\cong F$, $t\mapsto\alpha$, identity on $F_0$
(step 8), $\mathrm dc_1,\dots,\mathrm dc_t,\mathrm d\alpha$ is an $F$-basis of $\Omega_{F/k}$.
Uses: theorem-finite-etale-covers-proper-henselian--2, def-weil-pbc-kahler-differentials,
lem-weil-pbc-kahler-differentials-localization.

10. *Case S: the field $F_1=F_0(\beta)$ (as in 07FI, case algebraic).* $\alpha$ is algebraic over
$F_0$, so $F_0(\alpha)/F_0$ is an algebraic extension and by
[lem-weil-pbc-separable-first-purely-inseparable] there is $Q=p^e$ ($e\ge0$) with $\beta:=\alpha^Q$
separable over $F_0$ [def-weil-pbc-separable-algebraic-extension]; $\beta\neq0$. Let
$F_1=F_0(\beta)\subseteq K$; it is generated by $\beta$, so $F_1\cong F_0[T]/(\bar g)$, $\bar g$ the
minimal polynomial of $\beta$, is finite over $F_0$, and as the elements of $F_1$ separable over
$F_0$ form a subfield containing $F_0$ and $\beta$
[lem-weil-pbc-separable-first-purely-inseparable], $F_1/F_0$ is finite and separable algebraic.
Hence $\operatorname{Spec}F_1\to\operatorname{Spec}F_0$ is etale
[lem-weil-pbc-finite-separable-extension-etale]. $A_0$ and $\bar\Lambda$ are local rings whose only
prime is the maximal ideal [lem-weil-pbc-artinian-local-unique-prime], hence henselian
[lem-weil-pbc-henselian-of-nil-maximal-ideal]. By the essential surjectivity in
[lem-weil-pbc-henselian-finite-etale-equivalence] for $A_0$ and the finite etale $F_0$-algebra $F_1$
there is a finite etale $A_0$-algebra $D'$ with an $F_0$-algebra isomorphism $D'/\mathfrak
m_{A_0}D'\cong F_1$. $D'$ is finite over $A_0$, hence Noetherian
[lem-weil-pbc-finite-type-algebra-noetherian]; $\mathfrak m_{A_0}D'$ is nilpotent with quotient a
field, so it is the maximal ideal of the local ring $D'$, which is Artinian
[lem-weil-pbc-noetherian-local-quotient-artinian-local] with residue field $F_1$, and $A_0\to D'$ is
local.
Uses: lem-weil-pbc-separable-first-purely-inseparable, def-weil-pbc-separable-algebraic-extension,
lem-weil-pbc-finite-separable-extension-etale, lem-weil-pbc-artinian-local-unique-prime,
lem-weil-pbc-henselian-of-nil-maximal-ideal, lem-weil-pbc-henselian-finite-etale-equivalence,
lem-weil-pbc-finite-type-algebra-noetherian, lem-weil-pbc-noetherian-local-quotient-artinian-local.

11. *Case S: a factorization $A_0\to D'\to\bar\Lambda$ (Stacks: 'since $\bar\Lambda$ is henselian
and $F(\alpha^q)$ is contained in its residue field we can find a factorization').* Let $\rho:D'\to
F_1\subseteq K$ be the residue map composed with the isomorphism of step 10; on $A_0$ it is the
residue map $A_0\to F_0\subseteq K$. Let $B=D'\otimes_{A_0}\bar\Lambda$; $\bar\Lambda\to B$,
$x\mapsto1\otimes x$, is etale [lem-weil-pbc-etale-ring-base-change]. The maps $\rho$ and
$x\mapsto\hat x$ are ring maps $D'\to K$, $\bar\Lambda\to K$ agreeing on $A_0$, so they define a
ring map $\chi:B\to K$, $d\otimes x\mapsto\rho(d)\hat x$, surjective (already on
$1\otimes\bar\Lambda$). Its kernel $\mathfrak q'$ is a prime of $B$ lying over $\bar{\mathfrak m}$,
and $K=\bar\Lambda/\bar{\mathfrak m}\to B/\mathfrak q'\cong K$ is the identity, an isomorphism. By
[lem-weil-pbc-henselian-etale-retraction] ($\bar\Lambda$ henselian, step 10) there is a
$\bar\Lambda$-algebra map $\sigma:B\to\bar\Lambda$ with $\sigma^{-1}(\bar{\mathfrak m})=\mathfrak
q'$. Put $\psi'(d)=\sigma(d\otimes1)$. For $a\in A_0$, $\psi'(a)=\sigma(1\otimes a)=a$, so $\psi'$
restricts to the inclusion on $A_0$. Reducing $\sigma$ modulo $\bar{\mathfrak m}$ gives a
$K$-algebra map $B/\mathfrak q'\to K$, which is the inverse of the isomorphism $K\to B/\mathfrak
q'$; hence $\widehat{\psi'(d)}=\chi(d\otimes1)=\rho(d)$ for $d\in D'$. So $\psi'$ is local
($\psi'^{-1}(\bar{\mathfrak m})$ is a prime of $D'$, i.e. $\mathfrak m_{A_0}D'$, by
[lem-weil-pbc-artinian-local-unique-prime]) and induces on residue fields the inclusion
$F_1\subseteq K$.
Uses: lem-weil-pbc-etale-ring-base-change, lem-weil-pbc-henselian-etale-retraction,
lem-weil-pbc-artinian-local-unique-prime.

12. *Case S: $A=\psi'(D')$ is admissible and $\bar s^N\in A$.* As in step 8,
[lem-weil-pbc-criterion-flatness-fibre-noetherian] for $A_0\to D'\to\bar\Lambda$ and $M=\bar\Lambda$
($M/\mathfrak m_{A_0}M$ is a vector space over the field $D'/\mathfrak m_{A_0}D'\cong F_1$, hence
flat [def-weil-pbc-flat-ring-map]; $M$ flat over $A_0$) shows that $\psi'$ is flat; it is local,
hence faithfully flat [lem-weil-pbc-flat-local-hom-faithfully-flat] and injective
[lem-weil-pbc-faithfully-flat-ideal-contraction]. $A=\psi'(D')\cong D'$ is a $k$-subalgebra of
$\bar\Lambda$ containing $A_0$, Artinian local, flat into $\bar\Lambda$, with $\mathfrak
m_A\bar\Lambda=\mathfrak m_{A_0}\bar\Lambda=\bar{\mathfrak m}$ and residue field
$F=F_1=F_0(\beta)\subseteq K$ (step 11), finitely generated over $k$; as in step 8, $k\to F$ is
essentially of finite type [def-weil-pbc-essentially-finite-type-algebra]
[def-weil-pbc-finite-type-algebra] and so is $k\to A$
[theorem-finite-etale-covers-proper-henselian--2]. So $A$ is admissible and
$A_0\subseteq A$. By the Claim (step 5) for $D_1=A$ (local with $\mathfrak m_A=A\cap\bar{\mathfrak
m}$, step 1) and $x=\bar s^Q$, whose residue $\beta\in F$ is nonzero, $\bar s^{Qq'}\in A$ for a
power $q'$ of $p$ with $q'\ge\max(n,p)$. Put $N=Qq'$, a power of $p$ with $N\ge p$.
Uses: lem-weil-pbc-criterion-flatness-fibre-noetherian, def-weil-pbc-flat-ring-map,
lem-weil-pbc-flat-local-hom-faithfully-flat, lem-weil-pbc-faithfully-flat-ideal-contraction,
def-weil-pbc-essentially-finite-type-algebra, def-weil-pbc-finite-type-algebra,
theorem-finite-etale-covers-proper-henselian--2.

13. *Case S: a basis of $\Omega_{F/k}$.* $F/F_0$ is finite separable (step 10), so
$\operatorname{Spec}F\to\operatorname{Spec}F_0$ is etale
[lem-weil-pbc-finite-separable-extension-etale], i.e. $H_1(L_{F/F_0})=0$ and $\Omega_{F/F_0}=0$
[lem-weil-pbc-etale-ring-map-iff-etale-affine]. The Jacobi-Zariski sequence
[lem-weil-pbc-jacobi-zariski-homology-sequence] for $k\to F_0\to F$ contains the exact piece
$H_1(L_{F/F_0}) \to F\otimes_{F_0}\Omega_{F_0/k} \to \Omega_{F/k}
\to \Omega_{F/F_0} \to 0$,
with $w(c\otimes\mathrm db)=c\,\mathrm db$; so $w$ is an isomorphism. Since $\mathrm
dc_1,\dots,\mathrm dc_t$ is an $F_0$-basis of $\Omega_{F_0/k}$ (step 2), $1\otimes\mathrm dc_j$ is
an $F$-basis of $F\otimes_{F_0}\Omega_{F_0/k}$, and its image $\mathrm dc_1,\dots,\mathrm dc_t$ is
an $F$-basis of $\Omega_{F/k}$ [def-weil-pbc-kahler-differentials].
Uses: lem-weil-pbc-finite-separable-extension-etale, lem-weil-pbc-etale-ring-map-iff-etale-affine,
lem-weil-pbc-jacobi-zariski-homology-sequence, def-weil-pbc-kahler-differentials.

14. *The elements $\lambda_j$ and (a), (b).* In both cases let $A$, $F$, $N$ be as constructed
(steps 8, 12). Put $\lambda_j=\mu_js^{N-1}\in\Lambda$ for $j=1,\dots,t$, and in case T also
$\lambda_{t+1}=s$ (so the number of $\lambda$'s is $t$ in case S and $t+1$ in case T). By step 4,
$\pi(\lambda_j)=a_j\bar s\,\bar s^{N-1}=a_j\bar s^N\in A$ ($a_j\in A_0\subseteq A$, $\bar s^N\in
A$), and in case T $\pi(s)=\bar s\in A$. The residues are $c_j\alpha^N$ and, in case T, $\alpha$;
here $\alpha^N=\widehat{\bar s^N}\in F\setminus\{0\}$. By the Leibniz rule in $\Omega_{F/k}$
[def-weil-pbc-kahler-differentials], $\mathrm d(c_j\alpha^N)=\alpha^N\mathrm
dc_j+Nc_j\alpha^{N-1}\mathrm d\alpha=\alpha^N\mathrm dc_j$, since $p\mid N$ and $p=0$ in $F$ (in
case S, $\alpha^{N-1}$ need not lie in $F$, but $N\alpha^{N-1}\mathrm d\alpha$ is not needed: write
$c_j\alpha^N$ as $c_j\cdot\gamma$ with $\gamma=\alpha^N\in F$ and
$\gamma=(\alpha^Q)^{q'}=\beta^{q'}$, so $\mathrm d\gamma=q'\beta^{q'-1}\mathrm d\beta=0$ as $p\mid
q'$; in case T likewise $\gamma=\alpha^p$, $\mathrm d\gamma=p\alpha^{p-1}\mathrm d\alpha=0$). Hence
the differentials of the residues are $\alpha^N\mathrm dc_1,\dots,\alpha^N\mathrm dc_t$ in case S, a
basis of $\Omega_{F/k}$ by step 13 ($\alpha^N\in F^\times$), and $\alpha^N\mathrm
dc_1,\dots,\alpha^N\mathrm dc_t,\mathrm d\alpha$ in case T, a basis by step 9. This proves (a) and
(b) for the $\lambda$'s.
Uses: def-weil-pbc-kahler-differentials.

15. For n ≥ 2 put λ'_i = μ'_i s^(N-1), using step 4. Since μ'_i ∈ q, all λ'_i lie in q. Their
quotient images are b_i s^N, which lie in A and generate the quotient maximal ideal because s is a
unit. Choose a'_i to be these elements of A. For n = 1 the empty family spans the zero maximal
ideal. Together with the elements and differential basis in step 14, this proves exactly the
quotient-level conclusion. No contraction identification of m_A, residue embedding compatibility, or
lifting of these generators to qΛ_q is asserted by this step.
Uses: def-weil-pbc-kahler-differentials.
-/
theorem exists_popescu_admissible_quotient_basis
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
          Ideal.span (Set.range (fun i ↦
            Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)
              (algebraMap Λ (Localization.AtPrime q) (ys i)))) =
            (q.map (algebraMap Λ (Localization.AtPrime q))).map
              (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)) := by
  classical
  have _ := hreg
  let L := Localization.AtPrime q
  let J := q.map (algebraMap Λ L)
  let B := L ⧸ J ^ n
  let f := Ideal.Quotient.mk (J ^ n)
  let π : Λ →+* B := f.comp (algebraMap Λ L)
  let M := J.map f
  obtain ⟨hArt₀, hEft₀, hLoc₀, hFlat₀, hMax₀⟩ := hA₀
  change (IsLocalRing.maximalIdeal A₀).map A₀.val.toRingHom = M at hMax₀
  let : IsArtinianRing A₀ := hArt₀
  let : EssFiniteType k A₀ := hEft₀
  let : IsLocalRing A₀ := hLoc₀
  obtain ⟨t₀, a₀, b₀, hb₀⟩ := exists_residue_differential_basis k A₀
  obtain ⟨r, z, hz⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsLocalRing.maximalIdeal A₀).fg_of_isNoetherianRing
  have hzmem (i : Fin r) : z i ∈ IsLocalRing.maximalIdeal A₀ := by
    rw [← hz]
    exact Submodule.subset_span (Set.mem_range_self i)
  have hzspan : Ideal.span (Set.range (fun i ↦ (z i : B))) = M := by
    have he := congrArg (Ideal.map A₀.val.toRingHom) hz
    rw [Ideal.map_span, ← Set.range_comp] at he
    exact he.trans hMax₀
  obtain ⟨s, hs, μ, hμ⟩ := common_denominator q n
    (Sum.elim (fun j ↦ (a₀ j : B)) (fun i ↦ (z i : B)))
  change ∀ i, π (μ i) =
    Sum.elim (fun j ↦ (a₀ j : B)) (fun i ↦ (z i : B)) i * π s at hμ
  have hcontract : M.comap π = q := by
    have hpre : (J.map f).comap f = J := by
      rw [Ideal.comap_map_of_surjective f Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
        sup_of_le_left (Ideal.pow_le_self (by omega))]
    change (J.map f).comap (f.comp (algebraMap Λ L)) = q
    rw [← Ideal.comap_comap, hpre]
    rw [show J = IsLocalRing.maximalIdeal L from
      Localization.AtPrime.map_eq_maximalIdeal]
    exact Localization.AtPrime.under_maximalIdeal
  have hνmem (i : Fin r) : μ (Sum.inr i) ∈ q := by
    rw [← hcontract]
    change π (μ (Sum.inr i)) ∈ M
    rw [hμ (Sum.inr i)]
    apply M.mul_mem_right
    rw [← hMax₀]
    exact Ideal.mem_map_of_mem A₀.val.toRingHom (hzmem i)
  obtain ⟨A, hLoc, hIncl, hAdm, N, hN, c, hc, t, xs, a, hxs, hb⟩ :=
    exists_popescu_denominator_basis_enlargement k Λ p hp q n hn A₀
      ⟨hArt₀, hEft₀, hLoc₀, hFlat₀, hMax₀⟩
      t₀ a₀ b₀ hb₀ s hs (fun j ↦ μ (Sum.inl j)) (fun j ↦ hμ (Sum.inl j))
  let : IsLocalRing A := hLoc
  change (c : B) = (π s) ^ N at hc
  let ys : Fin r → Λ := fun i ↦ μ (Sum.inr i) * s ^ (N - 1)
  let a' : Fin r → A := fun i ↦ (⟨(z i : B), hIncl (z i).property⟩ : A) * c
  have hys (i : Fin r) : π (ys i) = (z i : B) * (π s) ^ N := by
    change π (μ (Sum.inr i) * s ^ (N - 1)) = _
    rw [map_mul, map_pow]
    rw [hμ (Sum.inr i), mul_assoc]
    congr 1
    rw [← pow_succ', Nat.sub_add_cancel hN]
  have hunit : IsUnit ((π s) ^ N) := by
    exact ((IsLocalization.map_units L (⟨s, hs⟩ : q.primeCompl)).map f).pow N
  refine ⟨A, hLoc, hIncl, hAdm, t, r, xs, ys, a, a', hxs, ?_, hb, ?_⟩
  · intro i
    refine ⟨q.mul_mem_right _ (hνmem i), ?_⟩
    change (z i : B) * (c : B) = π (ys i)
    rw [hc, hys]
  · change Ideal.span (Set.range (fun i ↦ π (ys i))) = M
    simp_rw [hys]
    exact (span_range_mul_unit (fun i ↦ (z i : B)) hunit).trans hzspan



end Algebra
