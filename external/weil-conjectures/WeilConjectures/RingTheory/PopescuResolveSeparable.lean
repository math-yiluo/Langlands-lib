/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuResolution
public import WeilConjectures.FieldTheory.SeparableExtension
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.MvPolynomial.Ideal
import WeilConjectures.RingTheory.PopescuDelocalizeHeightZero
import WeilConjectures.RingTheory.PopescuLiftSolution
import WeilConjectures.RingTheory.PopescuResolutionSmoothBase
import WeilConjectures.RingTheory.PopescuSeparableHeightZeroLocal
import WeilConjectures.RingTheory.PopescuSeparableParameterQuotient
import WeilConjectures.RingTheory.PopescuSeparablePreparation

/-!
# Resolving Popescu's local problem with separable residue field

Source: Stacks Project, Smoothing Ring Maps, Lemma 07FE (lemma-resolve-special),
Section 07FB (blueprint: lem-weil-pbc-popescu-resolve-separable).
-/

@[expose] public section

universe u v w

namespace Algebra

private theorem power_annihilator_eq
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (r : R) (c : ℕ) (hc : 1 ≤ c)
    (h : ∀ x : M, r • x = 0 ↔ r ^ 2 • x = 0) (x : M) :
    r ^ c • x = 0 ↔ (r ^ c) ^ 2 • x = 0 := by
  have hpow (n : ℕ) : ∀ x : M, r ^ (n + 1) • x = 0 ↔ r • x = 0 := by
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ r (n + 1), mul_smul, ih (r • x)]
      simpa only [pow_two, mul_smul] using (h x).symm
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, c = n + 1 := ⟨c - 1, by omega⟩
  rw [← pow_mul]
  have he : (n + 1) * 2 = (2 * n + 1) + 1 := by omega
  rw [he]
  exact (hpow n x).trans (hpow (2 * n + 1) x).symm

private theorem polynomial_pow_mem_of_mul_mem
    {k : Type u} [CommRing k] (d c m : ℕ) (i : Fin d)
    (p : MvPolynomial (Fin d) k)
    (hp : MvPolynomial.X i ^ m * p ∈ Ideal.span
      {y : MvPolynomial (Fin d) k |
        ∃ j : Fin d, j.val < i.val ∧ y = (MvPolynomial.X j ^ c) ^ 8}) :
    p ∈ Ideal.span {y : MvPolynomial (Fin d) k |
      ∃ j : Fin d, j.val < i.val ∧ y = (MvPolynomial.X j ^ c) ^ 8} := by
  classical
  let s : Set (Fin d →₀ ℕ) := {e | ∃ j : Fin d, j.val < i.val ∧
    e = Finsupp.single j (c * 8)}
  have hset : {y : MvPolynomial (Fin d) k |
      ∃ j : Fin d, j.val < i.val ∧ y = (MvPolynomial.X j ^ c) ^ 8} =
      (fun e : Fin d →₀ ℕ ↦ MvPolynomial.monomial e (1 : k)) '' s := by
    ext p
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Finsupp.single j (c * 8), ⟨j, hj, rfl⟩, by
        rw [← pow_mul, MvPolynomial.X_pow_eq_monomial]⟩
    · rintro ⟨e, ⟨j, hj, rfl⟩, rfl⟩
      exact ⟨j, hj, by rw [← pow_mul, MvPolynomial.X_pow_eq_monomial]⟩
  rw [hset] at hp ⊢
  apply MvPolynomial.mem_ideal_span_monomial_image.mpr
  intro e he
  have hs : Finsupp.single i m + e ∈ (MvPolynomial.X i ^ m * p).support := by
    rw [MvPolynomial.mem_support_iff, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.coeff_monomial_mul, one_mul]
    exact MvPolynomial.mem_support_iff.mp he
  obtain ⟨f, ⟨j, hj, rfl⟩, hfe⟩ :=
    MvPolynomial.mem_ideal_span_monomial_image.mp hp _ hs
  refine ⟨Finsupp.single j (c * 8), ⟨j, hj, rfl⟩, ?_⟩
  rw [Finsupp.single_le_iff] at hfe ⊢
  have hji : i ≠ j := by intro h; subst j; omega
  simpa [Finsupp.single_apply, hji] using hfe

private theorem polynomial_annihilator_eq
    {k : Type u} [CommRing k] (d c : ℕ) (i : Fin d)
    (x : MvPolynomial (Fin d) k ⧸ Ideal.span
      {y : MvPolynomial (Fin d) k |
        ∃ j : Fin d, j.val < i.val ∧ y = (MvPolynomial.X j ^ c) ^ 8}) :
    (MvPolynomial.X i : MvPolynomial (Fin d) k) ^ c • x = 0 ↔
      ((MvPolynomial.X i : MvPolynomial (Fin d) k) ^ c) ^ 2 • x = 0 := by
  let J : Ideal (MvPolynomial (Fin d) k) := Ideal.span
    {y | ∃ j : Fin d, j.val < i.val ∧ y = (MvPolynomial.X j ^ c) ^ 8}
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hzero (m : ℕ) (h : (MvPolynomial.X i : MvPolynomial (Fin d) k) ^ m •
        Ideal.Quotient.mk J p = 0) :
      Ideal.Quotient.mk J p = 0 := by
    change Ideal.Quotient.mk J (MvPolynomial.X i ^ m * p) = 0 at h
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (polynomial_pow_mem_of_mul_mem d c m i p
      (Ideal.Quotient.eq_zero_iff_mem.mp h))
  constructor
  · intro h
    rw [hzero c h, smul_zero]
  · intro h
    rw [← pow_mul] at h
    rw [hzero (c * 2) h, smul_zero]

/-- A finitely presented algebra over a field admits a Popescu resolution at a prime
minimal over its extended singular ideal, provided the target is Noetherian, the local
ring at that prime is regular, and its residue field is separable over the base field.
Source: Stacks Project, Smoothing Ring Maps, Lemma 07FE (lemma-resolve-special),
Section 07FB (blueprint: lem-weil-pbc-popescu-resolve-separable).

Proof (the blueprint's twelve steps, including its repairs of the source's proof):

Step 1. (Generators of $H_{A/k}$ and the exponent $n$.) $k$ is Noetherian (its only ideals are $0$
and $k$) and $A$ is of finite type over $k$, so $A$ is Noetherian
[lem-weil-pbc-finite-type-algebra-noetherian] and $H_{A/k}$ [def-weil-pbc-singular-ideal] is
generated by finitely many elements $a_1,\dots,a_r$ ($r\ge0$). Put
$I=H_{A/k}\Lambda=(\alpha(a_1),\dots,\alpha(a_r))\Lambda$, so $\mathfrak h_A=\sqrt I$
[def-weil-pbc-popescu-resolution]. By (2), $I\subset\mathfrak h_A\subset\mathfrak q$.
$\Lambda_{\mathfrak q}$ [def-weil-pbc-localization-at-prime] is a Noetherian local ring
[lem-weil-pbc-localization-noetherian]. A prime of $\Lambda_{\mathfrak q}$ containing
$I\Lambda_{\mathfrak q}$ is $\mathfrak q'\Lambda_{\mathfrak q}$ for a prime $\mathfrak
q'\subset\mathfrak q$ of $\Lambda$ containing $I$, hence containing $\sqrt I=\mathfrak h_A$; by
minimality (2) $\mathfrak q'=\mathfrak q$. So $\mathfrak q\Lambda_{\mathfrak q}$ is the only prime
containing $I\Lambda_{\mathfrak q}$, hence $\sqrt{I\Lambda_{\mathfrak q}}=\mathfrak
q\Lambda_{\mathfrak q}$ [lem-weil-pbc-zero-locus-eq-iff-radical-eq], and as $\mathfrak
q\Lambda_{\mathfrak q}$ is finitely generated there is $n\ge1$ with $\mathfrak
q^n\Lambda_{\mathfrak q}\subset I\Lambda_{\mathfrak q}$ [lem-weil-pbc-fg-ideal-radical-power].
(Stacks chooses $n$ with $\mathfrak q^n\Lambda_{\mathfrak q}\subset\mathfrak h_A\Lambda_{\mathfrak
q}$ and later applies Lemma 07FD with $I=\mathfrak h_A$; that only gives $\pi_i^n\in\mathfrak
h_A$, while the map $B\to\Lambda$ of step 8 needs $\pi_i^n\in H_{A/k}\Lambda$. Taking
$I=H_{A/k}\Lambda$ here repairs this. Stacks also writes $H_{A/R}$ for $H_{A/k}$.) Let
$d=\dim\Lambda_{\mathfrak q}$; by (3) $\mathfrak q\Lambda_{\mathfrak q}$ is generated by $d$
elements [def-weil-regular-scheme].

Step 2. (The case $d=0$.) If $d=0$ then $\mathfrak q\Lambda_{\mathfrak q}=0$, so
$\Lambda_{\mathfrak q}=\kappa(\mathfrak q)$ is a field, separable over $k$ by (4)
[def-weil-pbc-separable-field-extension]. Hence $\Lambda_{\mathfrak q}$ is a filtered colimit of
smooth $k$-algebras [corollary-open-direct-image-over-field--2] (in the sense of
[def-weil-pbc-filtered-colimit-smooth-algebras]: the smooth $k$-subalgebras with the inclusions
form such a diagram), and the map $A\to\Lambda\to\Lambda_{\mathfrak q}$ from the finitely
presented $k$-algebra $A$ factors as $A\to B'\to\Lambda_{\mathfrak q}$ with $B'$ a smooth
$k$-algebra [lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit]. As $B'=B'_1$ is
smooth, $1\in H_{B'/k}$ [def-weil-pbc-singular-ideal], so $\mathfrak h_{B'}=\Lambda_{\mathfrak
q}$, which contains the ideal $\mathfrak h_{A}$ formed in $\Lambda_{\mathfrak q}$ and is not
contained in $\mathfrak q\Lambda_{\mathfrak q}$: this is a resolution of $k\to
A\to\Lambda_{\mathfrak q}\supset\mathfrak q\Lambda_{\mathfrak q}$
[def-weil-pbc-popescu-resolution]. Here the inverse image of $\mathfrak q$ in $k$ is $\mathfrak
p=0$, $k_{\mathfrak p}=k$ and $A_{\mathfrak p}=A$. Since $\mathfrak q$ is minimal over $\mathfrak
h_A$ and $\dim\Lambda_{\mathfrak q}=0$, [lem-weil-pbc-popescu-delocalize-height-zero] (with $R=k$)
shows that $k\to A\to\Lambda\supset\mathfrak q$ can be resolved. (Stacks' proof does not treat
$d=0$ separately; there Lemma 07F8, which needs $r\ge1$, is applied with $r=d$.) From now on
$d\ge1$.

Step 3. (The algebra $B$.) Let $R=k[x_1,\dots,x_d]$ and
$B=A[x_1,\dots,x_d,z_{ij}]/(x_i^n-\sum_{j=1}^rz_{ij}a_j)_{i=1,\dots,d}$ with $rd$ variables
$z_{ij}$, an $A$-algebra and an $R$-algebra via $x_i\mapsto x_i$. If $A\cong
k[t_1,\dots,t_N]/(g_1,\dots,g_M)$ and $\tilde a_j\in k[t]$ lift $a_j$, then $B\cong
R[t,z_{ij}]/(g_1,\dots,g_M,x_i^n-\sum_jz_{ij}\tilde a_j)$, so $B$ is an $R$-algebra of finite
presentation.

Step 4. ($B_{a_l}$ and $B_{x_i}$ are smooth over $R$.) Fix $l$. In $B_{a_l}$ the relations can be
solved for $z_{il}=a_l^{-1}(x_i^n-\sum_{j\ne l}z_{ij}a_j)$, so $B_{a_l}\cong
A_{a_l}[x_1,\dots,x_d][z_{ij}:j\ne l]=(A_{a_l}\otimes_kR)[z_{ij}:j\ne l]$ (the inverse maps
$z_{il}$ to that expression). $A_{a_l}$ is smooth over $k$ because $a_l\in H_{A/k}$
[lem-weil-pbc-singular-ideal-localization-smooth]; hence $A_{a_l}\otimes_kR$ is smooth over $R$
(base change), the polynomial ring over it is smooth over it
[lem-weil-pbc-polynomial-ring-smooth], and the composite $R\to B_{a_l}$ is smooth
[lem-weil-pbc-smooth-ring-map-base-change-composition]. Now fix $i$. In $B_{x_i}$ the element
$x_i^n=\sum_jz_{ij}a_j$ is a unit, so $a_1,\dots,a_r$ generate the unit ideal of $B_{x_i}$ (if
$r=0$, $B_{x_i}=0$); each $(B_{x_i})_{a_j}=(B_{a_j})_{x_i}$ is smooth over $R$
[lem-weil-pbc-smooth-ring-map-principal-localization], hence $B_{x_i}$ is smooth over $R$
[lem-weil-pbc-smooth-ring-map-local-on-cover].

Step 5. (The algebra $C$ and the exponent $c$.) Apply [lem-weil-pbc-improve-presentation] to the
finitely presented $R$-algebra $B$: there are a $B$-algebra $C$ of finite type and a $B$-algebra
retraction $\rho:C\to B$ such that $C_b$ is smooth over $R$ with $\Omega_{C_b/R}$ free whenever
$B_b$ is smooth over $R$. $C$ is of finite type over $R$ ($B$ is), so of finite presentation over
the Noetherian ring $R$ [lem-weil-pbc-finite-type-algebra-noetherian,
lem-weil-pbc-finite-type-noetherian-finite-presentation]. By step 4, $C_{x_i}$ ($i=1,\dots,d$) and
$C_{a_j}$ ($j=1,\dots,r$) are smooth over $R$, and $\Omega_{C_{x_i}/R}$ is free. By
[lem-weil-pbc-smooth-free-differentials-strictly-standard-power] there are $e_0(i)$ with $x_i^{c}$
strictly standard in $C$ over $R$ [theorem-finite-etale-covers-proper-henselian--2] for $c\ge
e_0(i)$; take $c=\max_ie_0(i)$, so every $x_i^c$ is strictly standard in $C$ over $R$. Put $e=8c$.

Step 6. (The elements $\pi_i$ and the maps to $\Lambda$.) By step 1 and (1), (3),
[lem-weil-pbc-popescu-find-sequence] applies to $\Lambda$, $I=H_{A/k}\Lambda\subset\mathfrak q$,
$n$ and $e=8c$: there are $\pi_1,\dots,\pi_d\in\Lambda$ with (i)
$(\pi_1,\dots,\pi_d)\Lambda_{\mathfrak q}=\mathfrak q\Lambda_{\mathfrak q}$, (ii) $\pi_i^n\in I$,
(iii) $\mathrm{Ann}_{M_i}(\pi_i)=\mathrm{Ann}_{M_i}(\pi_i^2)$ on
$M_i=\Lambda/(\pi_1^e,\dots,\pi_{i-1}^e)\Lambda$. By (ii) write
$\pi_i^n=\sum_j\lambda_{ij}\alpha(a_j)$ with $\lambda_{ij}\in\Lambda$ (Stacks writes $\pi_{ij}$
once for $\lambda_{ij}$). Make $\Lambda$ an $R$-algebra by the $k$-algebra map $x_i\mapsto\pi_i$;
the $A$-algebra map $\beta:B\to\Lambda$, $x_i\mapsto\pi_i$, $z_{ij}\mapsto\lambda_{ij}$, is well
defined (the relations map to $\pi_i^n-\sum_j\lambda_{ij}\alpha(a_j)=0$) and $R$-linear, and
$\gamma=\beta\circ\rho:C\to\Lambda$ is an $R$-algebra map with $\gamma|_B=\beta$, so $A\to B\to
C\xrightarrow{\gamma}\Lambda$ composes to $\alpha$. By (i) $\pi_i/1\in\mathfrak
q\Lambda_{\mathfrak q}$, so $\pi_i\in\mathfrak q$ ($\mathfrak q$ prime); thus the inverse image
$\mathfrak p$ of $\mathfrak q$ in $R$ contains $x_1,\dots,x_d$, and since $(x_1,\dots,x_d)$ is
maximal ($R/(x)=k$), $\mathfrak p=(x_1,\dots,x_d)$.

Step 7. (Reduction modulo $x^e$ by Lemma 07F8.) Apply [lem-weil-pbc-popescu-lift-solution] to the
Noetherian ring $R$ [lem-weil-pbc-finite-type-algebra-noetherian], $R\to
C\xrightarrow{\gamma}\Lambda\supset\mathfrak q$ and the elements $x_1^c,\dots,x_d^c\in R$
($r=d\ge1$), which map to $\pi_i^c\in\mathfrak q$; note $(x_i^c)^8=x_i^e\mapsto\pi_i^e$.
Hypothesis (2) is step 5. Hypothesis (1) for $R$:
$R/(x_1^e,\dots,x_{i-1}^e)\cong(k[x_1,\dots,x_{i-1}]/(x_1^e,\dots,x_{i-1}^e))[x_i,\dots,x_d]$ is a
polynomial ring in $x_i$ over a ring, on which multiplication by $x_i^c$ and $x_i^{2c}$ is
injective, so both annihilators are $0$. Hypothesis (1) for $\Lambda$: on $M_i$,
$\mathrm{Ann}(\pi_i)=\mathrm{Ann}(\pi_i^2)$ (iii) implies
$\mathrm{Ann}(\pi_i^m)=\mathrm{Ann}(\pi_i)$ for all $m\ge1$ (if $\pi_i^{m+1}y=0$ with $m\ge1$ then
$\pi_i^2(\pi_i^{m-1}y)=0$, so $\pi_i(\pi_i^{m-1}y)=0$; induct), hence
$\mathrm{Ann}(\pi_i^c)=\mathrm{Ann}(\pi_i^{2c})$. Therefore, with $\bar R=R/(x_1^e,\dots,x_d^e)$,
$\bar C=C/(x^e)C$, $\bar\Lambda=\Lambda/(\pi_1^e,\dots,\pi_d^e)\Lambda$, $\bar{\mathfrak
q}=\mathfrak q/(\pi^e)\Lambda$: if $\bar R\to\bar C\to\bar\Lambda\supset\bar{\mathfrak q}$ can be
resolved, then $R\to C\to\Lambda\supset\mathfrak q$ can be resolved.

Step 8. (A resolution over $R$ gives one over $k$.) Stacks passes over this point. Let $C\to
D\to\Lambda$ be a resolution of $R\to C\to\Lambda\supset\mathfrak q$: $D$ of finite presentation
over $R$, $\mathfrak h_C^{R}\subset\mathfrak h_D^{R}\not\subset\mathfrak q$, where $\mathfrak h^R$
is formed with singular ideals over $R$ [def-weil-pbc-popescu-resolution]. $D$ is of finite
presentation over $k$ ($R$ is). If $D_g$ is smooth over $R$ it is smooth over $k$, since $R=k[x]$
is smooth over $k$ [lem-weil-pbc-polynomial-ring-smooth,
lem-weil-pbc-smooth-ring-map-base-change-composition]; so $H_{D/R}\subset H_{D/k}$
[def-weil-pbc-singular-ideal] and $\mathfrak h_D^R\subset\mathfrak h_D^k$, whence $\mathfrak
h_D^k\not\subset\mathfrak q$. By step 5, $C_{a_j}$ is smooth over $R$, so the image of $a_j$ in
$C$ lies in $H_{C/R}$, and $\gamma(a_j)=\alpha(a_j)$; hence $H_{A/k}\Lambda=(\alpha(a_j))_j\subset
H_{C/R}\Lambda$ and $\mathfrak h_A=\mathfrak h_A^k\subset\mathfrak h_C^R\subset\mathfrak
h_D^R\subset\mathfrak h_D^k$. So $A\to B\to C\to D\to\Lambda$ is a resolution of $k\to
A\to\Lambda\supset\mathfrak q$. It therefore suffices to resolve $\bar R\to\bar
C\to\bar\Lambda\supset\bar{\mathfrak q}$ (step 7).

Step 9. (Reduction to the localization by Lemma 07FA.) $\bar R$ is Noetherian
[lem-weil-pbc-finite-type-algebra-noetherian], $\bar C$ is of finite presentation over $\bar R$,
and $\bar\Lambda$ is an $\bar R$-algebra. The inverse image of $\bar{\mathfrak q}$ in $\bar R$ is
$\bar{\mathfrak p}=\mathfrak p/(x^e)$, and $\bar R_{\bar{\mathfrak p}}=R_{\mathfrak
p}/(x^e)R_{\mathfrak p}$, $\bar C_{\bar{\mathfrak p}}=C_{\mathfrak p}/(x^e)C_{\mathfrak p}$,
$\bar\Lambda_{\bar{\mathfrak q}}=\Lambda_{\mathfrak q}/(\pi_1^e,\dots,\pi_d^e)\Lambda_{\mathfrak
q}$ (localization commutes with quotients). A prime of $\Lambda_{\mathfrak q}$ containing all
$\pi_i^e$ contains all $\pi_i$, hence $\mathfrak q\Lambda_{\mathfrak q}$ by (i); so
$\bar\Lambda_{\bar{\mathfrak q}}$ has exactly one prime: $\dim\bar\Lambda_{\bar{\mathfrak q}}=0$.
If $\mathfrak h_{\bar C}\not\subset\bar{\mathfrak q}$, the identity factorization $\bar C\to\bar
C\to\bar\Lambda$ is already a resolution [def-weil-pbc-popescu-resolution]. Otherwise $\mathfrak
h_{\bar C}\subset\bar{\mathfrak q}$, and $\bar{\mathfrak q}$ is minimal over $\mathfrak h_{\bar
C}$: a prime $\mathfrak q'\subset\bar{\mathfrak q}$ of $\bar\Lambda$ gives the prime $\mathfrak
q'\bar\Lambda_{\bar{\mathfrak q}}$ of $\bar\Lambda_{\bar{\mathfrak q}}$, which is the unique one,
so $\mathfrak q'=\bar{\mathfrak q}$. (Stacks does not check hypothesis (1) of 07FA.) By
[lem-weil-pbc-popescu-delocalize-height-zero] it suffices to resolve $\bar R_{\bar{\mathfrak
p}}\to\bar C_{\bar{\mathfrak p}}\to\bar\Lambda_{\bar{\mathfrak q}}\supset\bar{\mathfrak
q}\bar\Lambda_{\bar{\mathfrak q}}$.

Step 10. (Flatness.) $R_{\mathfrak p}$ is a regular local ring of dimension $d$ whose maximal
ideal is generated by $x_1,\dots,x_d$, with residue field $R/\mathfrak p=k$
[lem-weil-pbc-polynomial-ring-origin-regular-local]. $\Lambda_{\mathfrak q}$ is a regular local
ring of dimension $d$ whose maximal ideal is generated by $\pi_1,\dots,\pi_d$ (i), so
$\pi_1,\dots,\pi_d$ is a regular sequence in $\Lambda_{\mathfrak q}$
[lem-weil-pbc-regular-local-generators-regular-sequence, def-weil-pbc-regular-sequence].
$R\setminus\mathfrak p$ maps into $\Lambda\setminus\mathfrak q$, so $R\to\Lambda$ induces a local
homomorphism $R_{\mathfrak p}\to\Lambda_{\mathfrak q}$ of Noetherian local rings
[lem-weil-pbc-localization-noetherian] sending $x_i\mapsto\pi_i$; it is flat
[lem-weil-pbc-flat-over-regular]. Hence $\bar\Lambda_{\bar{\mathfrak q}}=\Lambda_{\mathfrak
q}/(x_1^e,\dots,x_d^e)\Lambda_{\mathfrak q}$ is flat over $\bar R_{\bar{\mathfrak p}}=R_{\mathfrak
p}/(x^e)R_{\mathfrak p}$ [lem-weil-pbc-flat-module-quotient-flat].

Step 11. (Filtered colimit of smooth algebras.) The maximal ideal $\bar{\mathfrak
m}=(x_1,\dots,x_d)$ of $\bar R_{\bar{\mathfrak p}}$ is nilpotent: $\bar{\mathfrak
m}^{d(e-1)+1}=0$, as every monomial of that degree is divisible by some $x_i^e$. $\bar
R_{\bar{\mathfrak p}}/\bar{\mathfrak m}=R_{\mathfrak p}/\mathfrak pR_{\mathfrak p}=k$ and
$\bar\Lambda_{\bar{\mathfrak q}}/\bar{\mathfrak m}\bar\Lambda_{\bar{\mathfrak
q}}=\Lambda_{\mathfrak q}/(\pi_1,\dots,\pi_d)\Lambda_{\mathfrak q}=\kappa(\mathfrak q)$ by (i),
the $k$-algebra structure being the given one ($R\to\Lambda$ is a $k$-algebra map). By (4)
[def-weil-pbc-separable-field-extension] and [corollary-open-direct-image-over-field--2],
$\kappa(\mathfrak q)$ is a filtered colimit of smooth $k$-algebras
[def-weil-pbc-filtered-colimit-smooth-algebras]. With step 10, [lem-weil-pbc-popescu-lift-nilpotent]
applied to $\bar R_{\bar{\mathfrak p}}\to\bar\Lambda_{\bar{\mathfrak q}}$ and $I=\bar{\mathfrak m}$
shows that $\bar\Lambda_{\bar{\mathfrak q}}$ is a filtered colimit of smooth $\bar R_{\bar{\mathfrak
p}}$-algebras.

Step 12. (The resolution.) $\bar C_{\bar{\mathfrak p}}$ is of finite presentation over $\bar
R_{\bar{\mathfrak p}}$, so by step 11 and
[lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit] the map $\bar
C_{\bar{\mathfrak p}}\to\bar\Lambda_{\bar{\mathfrak q}}$ factors through a smooth $\bar
R_{\bar{\mathfrak p}}$-algebra $T$. Then $1\in H_{T/\bar R_{\bar{\mathfrak p}}}$
[def-weil-pbc-singular-ideal], so $\mathfrak h_T=\bar\Lambda_{\bar{\mathfrak q}}$, which contains
$\mathfrak h_{\bar C_{\bar{\mathfrak p}}}$ and is not contained in $\bar{\mathfrak
q}\bar\Lambda_{\bar{\mathfrak q}}$: $T$ resolves $\bar R_{\bar{\mathfrak p}}\to\bar
C_{\bar{\mathfrak p}}\to\bar\Lambda_{\bar{\mathfrak q}}\supset\bar{\mathfrak
q}\bar\Lambda_{\bar{\mathfrak q}}$ [def-weil-pbc-popescu-resolution]. By steps 9, 7 and 8, $k\to
A\to\Lambda\supset\mathfrak q$ can be resolved.
-/
theorem canBePopescuResolved_of_regularLocalRing_separable
    {k : Type u} {A : Type v} {Λ : Type w}
    [Field k] [CommRing A] [CommRing Λ] [Algebra k A] [Algebra k Λ]
    [FinitePresentation k A] [IsNoetherianRing Λ]
    (α : A →ₐ[k] Λ) (q : PrimeSpectrum Λ)
    (hminimal : q.asIdeal ∈ (popescuIdeal α).minimalPrimes)
    [IsRegularLocalRing (Localization.AtPrime q.asIdeal)]
    (hsep : IsSeparableExtension k q.asIdeal.ResidueField) :
    CanBePopescuResolved α q := by
  by_cases hdim : ringKrullDim (Localization.AtPrime q.asIdeal) = 0
  · exact canBePopescuResolved_of_local_height_zero α q hminimal
      (popescu_separable_height_zero_local α q hdim hsep) hdim
  · let d := (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)).spanFinrank
    have hdimension : ringKrullDim (Localization.AtPrime q.asIdeal) =
        (d : WithBot ℕ∞) := IsRegularLocalRing.spanFinrank_maximalIdeal.symm
    have hd : 1 ≤ d := by
      by_contra h
      have hz : d = 0 := by omega
      exact hdim (by simpa [hz] using hdimension)
    let I := Ideal.map α.toRingHom (singularIdeal k A)
    have hIq : I ≤ q.asIdeal := Ideal.le_radical.trans hminimal.le
    have hrad : (I.map (algebraMap Λ (Localization.AtPrime q.asIdeal))).radical =
        q.asIdeal.map (algebraMap Λ (Localization.AtPrime q.asIdeal)) := by
      apply IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
      change q.asIdeal ∈ I.radical.minimalPrimes at hminimal
      rwa [Ideal.radical_minimalPrimes] at hminimal
    obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
      (le_of_eq hrad.symm)
      (IsNoetherian.noetherian
        (q.asIdeal.map (algebraMap Λ (Localization.AtPrime q.asIdeal))))
    have hpow : (q.asIdeal ^ (n + 1)).map
        (algebraMap Λ (Localization.AtPrime q.asIdeal)) ≤
        I.map (algebraMap Λ (Localization.AtPrime q.asIdeal)) := by
      rw [Ideal.map_pow]
      exact (Ideal.pow_le_pow_right (by omega)).trans hn
    obtain ⟨c, φ, C, instC, algkC, algRC, towerC, fpC, β, γ,
      hc, hgen, hcomp, hideal, hπ, hΛ, hstandard⟩ :=
        exists_popescu_separable_preparation α q d (n + 1) hd (by omega)
          hdimension hIq hpow
    let : Algebra (MvPolynomial (Fin d) k) Λ := φ.toRingHom.toAlgebra
    have hquotient := exists_popescu_resolution_parameter_quotient
      d c hc φ γ q hdimension hgen hsep
    have hresolved : CanBePopescuResolved γ q :=
      canBePopescuResolved_of_quotient_eighth_powers d
        (fun i : Fin d ↦ MvPolynomial.X i ^ c) γ q hd hπ (polynomial_annihilator_eq d c)
        (fun i x ↦ power_annihilator_eq (MvPolynomial.X i) c hc (hΛ i) x)
        hstandard hquotient
    have : Smooth k (MvPolynomial (Fin d) k) := Smooth.mk
    exact canBePopescuResolved_of_smooth_base α q β γ hcomp hideal hresolved

end Algebra
