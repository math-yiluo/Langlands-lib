/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.PopescuResolution
public import WeilConjectures.RingTheory.StrictlyStandardElement
public import Mathlib.Algebra.MvPolynomial.Basic
public import WeilConjectures.RingTheory.EssentiallySmooth
public import Mathlib.RingTheory.Localization.AtPrime.Basic

import WeilConjectures.RingTheory.PopescuCharPPreparationGlobal
import WeilConjectures.RingTheory.EssentiallySmoothBaseChange
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Popescu characteristic-p preparation: auxiliary construction

Source: Stacks Project, Smoothing Ring Maps, Lemma 07FJ.
-/

@[expose] public section
universe u v w
open scoped TensorProduct
namespace Algebra

/-- Construct the standardized polynomial-base algebra and a factorization at an auxiliary
thickening, with explicit power and ideal-containment witnesses.
Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07FJ, construction and
quotient steps (with n=N+de).
(blueprint: popescu-char-p-preparation-core).

Proof:
1. (Items item-power, item-generators, item-dimension: the integers $N$, $d$ and generators of
   $H_{A/k}$.) Write $H=H_{A/k}$ [def-weil-pbc-singular-ideal], $\mathfrak h_A=\sqrt{H\Lambda}$
   [def-weil-pbc-popescu-resolution], $S_\Lambda=\Lambda\setminus\mathfrak q$ and
   $\Lambda_{\mathfrak q}=S_\Lambda^{-1}\Lambda$ [def-weil-pbc-localization-at-prime]. The
   primes of $\Lambda_{\mathfrak q}$ are the $\mathfrak q'\Lambda_{\mathfrak q}$ with $\mathfrak
   q'\subset\mathfrak q$ prime; if such a $\mathfrak q'$ contains $H\Lambda$ it contains
   $\mathfrak h_A$, so $\mathfrak q'=\mathfrak q$ because $\mathfrak q$ is minimal over
   $\mathfrak h_A$. Hence $V(H\Lambda_{\mathfrak q})=\{\mathfrak q\Lambda_{\mathfrak
   q}\}=V(\mathfrak q\Lambda_{\mathfrak q})$ and $\sqrt{H\Lambda_{\mathfrak q}}=\sqrt{\mathfrak
   q\Lambda_{\mathfrak q}}=\mathfrak q\Lambda_{\mathfrak q}$ [lem-weil-pbc-zero-locus-eq-iff-
   radical-eq]. $\Lambda_{\mathfrak q}$ is Noetherian [lem-weil-pbc-localization-noetherian], so
   $\mathfrak q\Lambda_{\mathfrak q}$ is finitely generated and there is $N\ge1$ with $\mathfrak
   q^N\Lambda_{\mathfrak q}\subset H\Lambda_{\mathfrak q}$ [lem-weil-pbc-fg-ideal-radical-
   power]. $A$ is of finite type over the field $k$, hence Noetherian [lem-weil-pbc-finite-type-
   algebra-noetherian]; choose generators $a_1,\dots,a_t$ of the ideal $H\subset A$ (Stacks
   writes $H_{A/R}$ here, a misprint for $H_{A/k}$). Put $d=\dim\Lambda_{\mathfrak q}$.

2. (Items item-standardizer, item-elkik, item-strictly-standard, item-set-n: the algebras $B$,
   $C$ and the integers $c$, $e$, $n$.) Let
   $B=A[x_1,\dots,x_d,z_{ij}]/(x_i^{2N}-\sum_{j=1}^tz_{ij}a_j)_{i=1,\dots,d}$ ($i\le d$, $j\le
   t$), a $k[x_1,\dots,x_d]$-algebra of finite presentation (finitely many variables and
   relations over the finitely presented $k$-algebra $A$). (a) For each $j$, $A_{a_j}$ is smooth
   over $k$ [lem-weil-pbc-singular-ideal-localization-smooth]. In $B_{a_j}$ the $i$-th relation
   reads $z_{ij}=a_j^{-1}(x_i^{2N}-\sum_{l\ne j}z_{il}a_l)$, so $B_{a_j}\cong
   A_{a_j}[x_1,\dots,x_d][z_{il}:l\ne j]$ as $k[x]$-algebras (the map sending $z_{il}\mapsto
   z_{il}$ for $l\ne j$ and inverse sending $z_{ij}$ to that expression), i.e. a polynomial
   algebra over $A_{a_j}\otimes_kk[x]$; this is smooth over $k[x]$ by base change of $k\to
   A_{a_j}$ along $k\to k[x]$, the smoothness of polynomial algebras and composition [lem-weil-
   pbc-smooth-ring-map-base-change-composition] [lem-weil-pbc-polynomial-ring-smooth]. (b) In
   $B$, $x_i^{2N}\in(a_1,\dots,a_t)B$, so $a_1,\dots,a_t$ generate the unit ideal of $B_{x_i}$,
   and $(B_{x_i})_{a_j}=(B_{a_j})_{x_i}$ is smooth over $k[x]$ [lem-weil-pbc-smooth-ring-map-
   principal-localization]; hence $B_{x_i}$ is smooth over $k[x]$ [lem-weil-pbc-smooth-ring-map-
   local-on-cover]. (c) Apply [lem-weil-pbc-improve-presentation] to the $k[x]$-algebra $B$: we
   get a $B$-algebra $C$ of finite type with a $B$-algebra retraction $\rho:C\to B$ such that
   $C_{x_i}$ and $C_{a_j}$ (by (b), (a)) are smooth over $k[x]$ with free modules of
   differentials. $C$ is of finite type over the Noetherian ring $k[x]$ [lem-weil-pbc-finite-
   type-algebra-noetherian], hence of finite presentation [lem-weil-pbc-finite-type-noetherian-
   finite-presentation]. By [lem-weil-pbc-smooth-free-differentials-strictly-standard-power]
   there is $c\ge1$ such that $x_1^c,\dots,x_d^c$ are strictly standard in $C$ over $k[x]$ [def-
   weil-pbc-strictly-standard-element] (take $c$ at least each of the $d$ bounds $e_0$). Put
   $e=8c$ and $n=N+de$. (Stacks sets $n=N+dc$; the justification of item (item-sixth-resolve)
   needs $\mathfrak p^nk[y]_{\mathfrak p}\subset(\pi_1^e,\dots,\pi_d^e)$ for a regular system of
   parameters $\pi_1,\dots,\pi_d$, i.e. $n\ge d(e-1)+1$, which $N+dc$ does not give when $e=8c$;
   $n=N+de$ satisfies $n\ge N$ and $n\ge d(e-1)+1$, and nothing else in the proof bounds $n$, so
   this corrects a misprint.) Let $\bar\Lambda=\Lambda_{\mathfrak q}/\mathfrak
   q^n\Lambda_{\mathfrak q}$ and $E\subset\bar\Lambda$ the images of finitely many $k$-algebra
   generators of $A$.

3. (Item item-NP: the solution modulo $\mathfrak q^n$.) By [lem-weil-pbc-popescu-solution-
   modulo] (applicable: $k$ of characteristic $p$, $\Lambda$ Noetherian and geometrically
   regular, $n$ and $E$ as in Step 2) there are $m\ge0$, a $k$-algebra map
   $\varphi:k[y_1,\dots,y_m]\to\Lambda$, with $\mathfrak p=\varphi^{-1}(\mathfrak q)$ and
   $P_0=k[y_1,\dots,y_m]_{\mathfrak p}$, such that $\mathfrak p\Lambda_{\mathfrak q}=\mathfrak
   q\Lambda_{\mathfrak q}$, $P_0\to\Lambda_{\mathfrak q}$ is flat, and a factorization
   $P_0/\mathfrak p^nP_0\to D\to\bar\Lambda$ by local homomorphisms of local Artinian rings with
   the first arrow essentially smooth [def-weil-pbc-essentially-smooth-ring-map], the second
   flat, and $E$ contained in the image of $D$. The flat local map $D\to\bar\Lambda$ is
   faithfully flat [lem-weil-pbc-flat-local-hom-faithfully-flat], hence injective [lem-weil-pbc-
   faithfully-flat-ideal-contraction] (case $I=0$); we identify $D$ with its image, a
   $k$-subalgebra of $\bar\Lambda$. Since $D$ contains the images of generators of $A$, the map
   $A\to\bar\Lambda$ takes values in $D$; in particular $a_1,\dots,a_t\in D$.

4. (Item item-choose-pii: the parameters $\pi_i$.) The field $k$ is a regular ring [lem-weil-
   pbc-field-regular-ring] and $k\to k[y_1,\dots,y_m]$ is smooth [lem-weil-pbc-polynomial-ring-
   smooth], so $k[y]$ is a regular ring [lem-weil-pbc-regular-ring-smooth-ascent] and $P_0$ is a
   regular local ring [def-weil-regular-scheme]. Apply [lem-weil-pbc-flat-height-formula] to the
   flat map $P_0\to\Lambda_{\mathfrak q}$ of Noetherian rings ($k[y]$ is Noetherian [lem-weil-
   pbc-finite-type-algebra-noetherian], localizations of Noetherian rings are Noetherian [lem-
   weil-pbc-localization-noetherian]) and the maximal ideal $\mathfrak q\Lambda_{\mathfrak q}$,
   which lies over $\mathfrak pP_0$ (Step 3: $\mathfrak q\Lambda_{\mathfrak q}=\mathfrak
   p\Lambda_{\mathfrak q}$): the prime $\mathfrak q\Lambda_{\mathfrak q}/\mathfrak
   p\Lambda_{\mathfrak q}$ is the zero ideal of the field $\Lambda_{\mathfrak q}/\mathfrak
   q\Lambda_{\mathfrak q}$, of height $0$, so $d=\dim\Lambda_{\mathfrak q}=\dim P_0$ [def-weil-
   pbc-localization-at-prime]. As $P_0$ is regular of dimension $d$, $\mathfrak pP_0$ is
   generated by $d$ elements; multiplying them by units of $P_0$ we may take them as images of
   $\pi_1,\dots,\pi_d\in\mathfrak p$. Their images generate $\mathfrak pP_0\Lambda_{\mathfrak
   q}=\mathfrak q\Lambda_{\mathfrak q}$, so $\Lambda_{\mathfrak q}$, a Noetherian local ring of
   dimension $d$ whose maximal ideal is generated by $d$ elements, is a regular local ring [def-
   weil-regular-scheme] with regular system of parameters $\pi_1,\dots,\pi_d$. (Stacks writes
   'pi_1,...,pi_d in Lambda which map to a regular system of parameters in Lambda_q'; the
   elements are taken in $k[y]$, as item (item-choose-pii) says.)

5. (Items item-set-R, item-modify-pii: the ring $R$ and the annihilator conditions in $R$.) Let
   $R=k[y_1,\dots,y_m,t_1,\dots,t_d]$ (Stacks writes $t_1,\dots,t_m$ in item (item-set-R), a
   misprint for $t_d$ as in item (item-set-map-R)), $\gamma_i=\pi_it_i$,
   $S_0=k[y]\setminus\mathfrak p$, so $S_0^{-1}R=P_0[t_1,\dots,t_d]$. Each permutation of
   $\pi_1,\dots,\pi_d$ generates $\mathfrak pP_0$ and so is a regular sequence in $P_0$ [lem-
   weil-pbc-regular-local-generators-regular-sequence] [def-weil-pbc-regular-sequence]; the
   $\pi_i$ lie in the maximal ideal, so by [lem-weil-pbc-regular-sequence-polynomial-variables]
   $\gamma_1,\dots,\gamma_d$ is a regular sequence in $S_0^{-1}R$. Both facts persist when the
   $\pi_i$ are multiplied by elements of $S_0$ (units of $P_0$). We modify $\pi_1,\dots,\pi_d$
   one at a time so that for $i=1,\dots,d$:
   $\operatorname{Ann}_{M_i}(\gamma_i)=\operatorname{Ann}_{M_i}(\gamma_i^2)$,
   $M_i=R/(\gamma_1^e,\dots,\gamma_{i-1}^e)R$. Suppose this holds for $i\le t_0$. By [lem-weil-
   pbc-regular-sequence-powers] (exponents $e,\dots,e,1$),
   $\gamma_1^e,\dots,\gamma_{t_0}^e,\gamma_{t_0+1}$ is a regular sequence in $S_0^{-1}R$, so
   $\gamma_{t_0+1}$ is a nonzerodivisor on
   $S_0^{-1}M_{t_0+1}=S_0^{-1}R/(\gamma_1^e,\dots,\gamma_{t_0}^e)$ and
   $\operatorname{Ker}(\gamma_{t_0+1})=0=\operatorname{Ker}(\gamma_{t_0+1}^2)$ there. $R$ is
   Noetherian [lem-weil-pbc-finite-type-algebra-noetherian] and $M_{t_0+1}$ is a finite
   $R$-module, so [lem-weil-pbc-ogoma] gives $s\in S_0$ with
   $\operatorname{Ann}_{M_{t_0+1}}(s\gamma_{t_0+1})=
   \operatorname{Ann}_{M_{t_0+1}}((s\gamma_{t_0+1})^2)$ (its case $n=1$). Replace
   $\pi_{t_0+1}$ by $s\pi_{t_0+1}$ (still in $\mathfrak p$; $\gamma_{t_0+1}$ becomes
   $s\gamma_{t_0+1}$); the conditions for $i\le t_0$ involve only $\gamma_1,\dots,\gamma_{t_0}$
   and are unchanged. Induction on $t_0$ gives the conditions for all $i\le d$; Step 4 still
   holds for the modified $\pi_i$.

6. (Item item-choose-deltai: the units $\delta_i$, the elements $\lambda_{ij}$ and the enlarged
   $D'$.) We show by induction on $t_0\in\{0,\dots,d\}$: there are
   $\delta_1,\dots,\delta_{t_0}\in S_\Lambda$, $\lambda_{ij}\in\Lambda$ ($i\le t_0$) and a
   factorization $D\to D'\to\bar\Lambda$ by local homomorphisms of local Artinian rings, $D\to
   D'$ essentially smooth, $D'\to\bar\Lambda$ flat, such that with $\pi'_i=\delta_i\pi_i$: (a)
   $(\pi'_i)^{2N}=\sum_ja_j\lambda_{ij}$ in $\Lambda$ and the image of $\lambda_{ij}$ in
   $\bar\Lambda$ lies in $D'$; (b) $\operatorname{Ann}_{\Lambda/({\pi'_1}^e,\dots,{\pi'_{i-
   1}}^e)}(\pi'_i)=\operatorname{Ann}_{\Lambda/({\pi'_1}^e,\dots,{\pi'_{i-1}}^e)}({\pi'_i}^2)$;
   (c) the image of $\delta_i$ in $\bar\Lambda$ lies in $D'$. For $t_0=0$ take $D'=D$ ($D\to D$
   is smooth, so essentially smooth). Throughout, $P_0/\mathfrak p^nP_0\to D'$ is essentially
   smooth [lem-weil-pbc-essentially-smooth-composition], so [lem-weil-pbc-popescu-enlarge-
   solution-modulo] applies to $D'$ in place of $D$, and each enlargement $D'\to D''$ is again
   essentially smooth over $D$ [lem-weil-pbc-essentially-smooth-composition], keeps (a)-(c) for
   the earlier indices (the image only grows), and $D''\to\bar\Lambda$ is flat local, hence
   faithfully flat [lem-weil-pbc-flat-local-hom-faithfully-flat] and injective [lem-weil-pbc-
   faithfully-flat-ideal-contraction]; we identify $D''$ with its image. Inductive step,
   $\pi=\pi_{t_0+1}$: $\pi^N\in\mathfrak q^N\Lambda_{\mathfrak q}\subset H\Lambda_{\mathfrak q}$
   (Step 1), so in $\bar\Lambda$, $\pi^N\in(a_1,\dots,a_t)\bar\Lambda$; $\pi$ and the $a_j$ lie
   in $D'$ (Step 3), so $\pi^N\in(a_1,\dots,a_t)\bar\Lambda\cap D'=(a_1,\dots,a_t)D'$ [lem-weil-
   pbc-faithfully-flat-ideal-contraction]: $\pi^N=\sum_ja_jd_j$, $d_j\in D'$. Lift $d_j$ to
   $c_j\in\Lambda_{\mathfrak q}$; then $\varepsilon=\pi^N-\sum c_ja_j\in\mathfrak
   q^n\Lambda_{\mathfrak q}=\mathfrak q^{n-N}\mathfrak q^N\Lambda_{\mathfrak q}\subset\mathfrak
   q^{n-N}H\Lambda_{\mathfrak q}$, so $\varepsilon=\sum a_jc'_j$ with $c'_j\in\mathfrak
   q^{n-N}\Lambda_{\mathfrak q}$, and $\pi^{2N}=\sum_jw_ja_j$ with $w_j=\pi^N(c_j+c'_j)$, where
   $\pi^Nc'_j\in\mathfrak q^n\Lambda_{\mathfrak q}$ maps to $0$ in $\bar\Lambda$ (the 'key
   observation' of Stacks). (The detail Stacks omits:) write $w_j=u_j/s_0$ with $u_j\in\Lambda$,
   $s_0\in S_\Lambda$; then $s_0\pi^{2N}-\sum u_ja_j$ is $0$ in $\Lambda_{\mathfrak q}$, so
   $s_1(s_0\pi^{2N}-\sum u_ja_j)=0$ in $\Lambda$ for some $s_1\in S_\Lambda$; with $s=s_0s_1$
   and $\mu_j=s^{2N-1}s_1u_j$ we get $(s\pi)^{2N}=\sum_j\mu_ja_j$ in $\Lambda$ and
   $\mu_j/s^{2N}=w_j$. Enlarge $D'$ by [lem-weil-pbc-popescu-enlarge-solution-modulo] with
   $\lambda=s$ so that some $s^{q_1}\in D'$, and replace $s$ by $s^{q_1}$ and $\mu_j$ by
   $s^{2N(q_1-1)}\mu_j$ (both equations persist); now $s\in D'$ and the image of $\mu_j$ in
   $\bar\Lambda$ is $s^{2N}\pi^Nd_j\in D'$ (Stacks writes $s^{2N}d_j$). Next,
   $\pi_1,\dots,\pi_d$ is a regular sequence in the regular local ring $\Lambda_{\mathfrak q}$
   (Step 4, [lem-weil-pbc-regular-local-generators-regular-sequence]); multiplying its terms by
   the units $\delta_1,\dots,\delta_{t_0},s$ of $\Lambda_{\mathfrak q}$ keeps it regular (the
   ideals $(f_1,\dots,f_{i-1})$ and the nonzerodivisor conditions are unchanged) [def-weil-pbc-
   regular-sequence], and by [lem-weil-pbc-regular-sequence-powers]
   ${\pi'_1}^e,\dots,{\pi'_{t_0}}^e,s\pi$ is a regular sequence in $S_\Lambda^{-1}\Lambda$. So
   on $M=\Lambda/({\pi'_1}^e,\dots,{\pi'_{t_0}}^e)$, a finite module over the Noetherian ring
   $\Lambda$, multiplication by $s\pi$ is injective on $S_\Lambda^{-1}M$, whence
   $\operatorname{Ker}(s\pi)=\operatorname{Ker}((s\pi)^2)$ on $S_\Lambda^{-1}M$, and [lem-weil-
   pbc-ogoma] gives $s'\in S_\Lambda$ with
   $\operatorname{Ann}_M((s')^qs\pi)=\operatorname{Ann}_M(((s')^qs\pi)^2)$ for every $q>0$. By
   [lem-weil-pbc-popescu-enlarge-solution-modulo] with $\lambda=s'$ choose $q$ and enlarge $D'$
   so that $(s')^q\in D'$. Set $\delta_{t_0+1}=(s')^qs$ and $\lambda_{t_0+1,j}=(s')^{2Nq}\mu_j$:
   then $(\pi'_{t_0+1})^{2N}=(s')^{2Nq}(s\pi)^{2N}=\sum_ja_j\lambda_{t_0+1,j}$ with
   $\lambda_{t_0+1,j}\mapsto(s')^{2Nq}s^{2N}\pi^Nd_j\in D'$, which is (a); (b) is the choice of
   $s'$; (c) holds as $s,(s')^q\in D'$.

7. Distinguish the algebra C_old from step 2 from the final algebra C. Map B to Λ by the
   original map α on A, x_i to δ_iπ_i and z_ij to λ_ij; step 6 verifies its relations. Compose
   with the retraction C_old→B. Map k[x]→R by x_i↦π_it_i and R→Λ by y_j↦φ(y_j), t_i↦δ_i.
   Set C=R⊗_(k[x])C_old, β the map A→B→C_old→C, and γ the tensor lift of these compatible
   maps. On A, γβ=α. The images of all a_j have smooth principal localizations over R by
   base change of the opens from step 2; hence the extended singular ideal of A over k lies
   in the singular ideal of C over R after extension to Λ. Taking radicals gives
   popescuIdeal α≤popescuIdeal γ. Finite presentation follows by base change. Choose the
   lifting parameters (π_it_i)^c. Strict standardness survives base change. If multiplication
   by x and x^2 have the same kernel, induct on j to see that every positive power has this
   kernel; apply this to the annihilator equalities from steps 5 and 6. Thus the displayed
   eighth-power lifting hypotheses hold.

8. Work before taking the final eighth-power quotient. Write Q=R_r and L=Λ_q, r=q∩R. The t_i map
   to units δ_i of L, hence t_i are units in Q. Thus JQ is generated by π_i^e, e=8c. The
   modified π_i still generate the maximal ideal of the original polynomial localization P_0;
   their images generate the maximal ideal of L. The pigeonhole bound gives m_L^(d(e-1)+1)⊆JL
   and p_0^(d(e-1)+1)Q⊆JQ. With n=N+de>0 these containments also hold for n-th powers. Set
   I=p_0^n Q and K=m_L^n. Then I⊆JQ, K⊆JL, and IL⊆K because p_0L=m_L. These are actual power and
   ideal-containment witnesses, not a consequence of the annihilator conditions.

9. The enlarged Artinian solution D′ is essentially smooth over P_0/p_0^n by composition. Form
   D′[t], then base change along (P_0/p_0^n)[t]→Q/I; call the result D. This base map exists
   since elements outside p_0 map to units in Q. The retraction C→B and the map A→D′ give f:Q⊗_R
   C→D: send x_i to π_it_i and z_ij to bar(λ_ij)t_i^(2N)bar(δ_i)^(-2N). The images of δ_i are
   units in D′ since the map D′→L/K is flat local and their images are units. The equation
   (δ_iπ_i)^(2N)=Σ_j a_jλ_ij holds in Λ; faithful-flat injectivity proves the corresponding
   defining relation in D′. It persists after adjoining t and base changing. Send t_i to δ_i and
   use D′→L/K to obtain g:D→L/K. Agreement of the base maps extends g through the tensor base
   change. On A,x_i,z_ij the composite agrees with C→Λ→L/K, and the tensor universal property
   gives the displayed equality. Smoothness survives base change and localization commutes with
   base change; hence D is essentially smooth over Q/I. This is a factorization at the earlier
   thickening K; no algebra E over the eighth-power quotient has yet been constructed.

10. If d=0 pad the parameter list by a zero; otherwise padding by a final zero is harmless. Its
   annihilator equality is tautological, and it is strictly standard by choosing zero minor
   coefficients in any finite presentation. The eighth-power ideal is unchanged, as are Q,L,I,K
   and the auxiliary factorization. In dimension zero m_L=0, so the positive power bound holds
   even when all parameters are zero. The constructed standardized algebra and D have
   representatives in Type(max u v). For the Artinian solutions supplied in a larger universe,
   essential smoothness expresses each as a localization of a smooth algebra over P_0/p_0^n.
   A smooth algebra is finitely presented, so its finite polynomial presentation gives a small
   representative; transport the multiplicative subset to it and localize. Tensor products,
   quotients and localizations of these small representatives remain small. Transport all
   structures and maps along the resulting algebra equivalences.
-/
theorem exists_popescu_char_p_preparation_core
    {k : Type u} {A : Type v} {Λ : Type w}
    [Field k] [CommRing A] [CommRing Λ] [Algebra k A] [Algebra k Λ]
    [FinitePresentation k A] [IsNoetherianRing Λ]
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (α : A →ₐ[k] Λ) (q : PrimeSpectrum Λ)
    (hreg : IsGeometricallyRegular k Λ)
    (hminimal : q.asIdeal ∈ (popescuIdeal α).minimalPrimes) :
    ∃ (m : ℕ) (_ : Algebra (MvPolynomial (Fin m) k) Λ)
      (_ : IsScalarTower k (MvPolynomial (Fin m) k) Λ)
      (C : Type (max u v)) (_ : CommRing C) (_ : Algebra k C)
      (_ : Algebra (MvPolynomial (Fin m) k) C)
      (_ : IsScalarTower k (MvPolynomial (Fin m) k) C)
      (_ : FinitePresentation (MvPolynomial (Fin m) k) C)
      (β : A →ₐ[k] C) (γ : C →ₐ[MvPolynomial (Fin m) k] Λ),
      (γ.restrictScalars k).comp β = α ∧ popescuIdeal α ≤ popescuIdeal γ ∧
      ∃ (r : ℕ) (π : Fin r → MvPolynomial (Fin m) k),
        1 ≤ r ∧
        (∀ i, algebraMap (MvPolynomial (Fin m) k) Λ (π i) ∈ q.asIdeal) ∧
        (∀ (i : Fin r)
          (x : MvPolynomial (Fin m) k ⧸ Ideal.span
            {y | ∃ j : Fin r, j.val < i.val ∧ y = π j ^ 8}),
          π i • x = 0 ↔ π i ^ 2 • x = 0) ∧
        (∀ (i : Fin r)
          (x : Λ ⧸ Ideal.span
            {y | ∃ j : Fin r, j.val < i.val ∧
              y = algebraMap (MvPolynomial (Fin m) k) Λ (π j) ^ 8}),
          π i • x = 0 ↔ π i ^ 2 • x = 0) ∧
        (∀ i, IsStrictlyStandardElement
          (R := MvPolynomial (Fin m) k) (algebraMap (MvPolynomial (Fin m) k) C (π i))) ∧
    let R := MvPolynomial (Fin m) k
    let J := Ideal.span (Set.range (fun i : Fin r ↦ π i ^ 8))
    let Q := Localization.AtPrime (q.asIdeal.under R)
    let L := Localization.AtPrime q.asIdeal
    letI := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
    let JQ := J.map (algebraMap R Q)
    let JL := (J.map (algebraMap R Λ)).map (algebraMap Λ L)
    ∃ (n : ℕ), 0 < n ∧ IsLocalRing.maximalIdeal L ^ n ≤ JL ∧
      ∃ (I : Ideal Q) (K : Ideal L),
        I ≤ JQ ∧ K ≤ JL ∧ I.map (algebraMap Q L) ≤ K ∧
        ∃ (D : Type (max u v)) (_ : CommRing D) (_ : Algebra Q D)
          (_ : Algebra (Q ⧸ I) D) (_ : IsScalarTower Q (Q ⧸ I) D),
          EssentiallySmooth (Q ⧸ I) D ∧
          ∃ (f : Q ⊗[R] C →ₐ[Q] D) (g : D →ₐ[Q] L ⧸ K),
            g.comp f = Algebra.TensorProduct.lift (Algebra.ofId Q (L ⧸ K))
              ((Ideal.Quotient.mkₐ R K).comp
                ((IsScalarTower.toAlgHom R Λ L).comp γ))
              (fun _ _ ↦ Commute.all _ _) := by
  let H := Ideal.map α.toRingHom (singularIdeal k A)
  let L₀ := Localization.AtPrime q.asIdeal
  have hmin : q.asIdeal ∈ H.minimalPrimes := by
    simpa only [popescuIdeal, Ideal.radical_minimalPrimes] using hminimal
  have hrad : (H.map (algebraMap Λ L₀)).radical = IsLocalRing.maximalIdeal L₀ := by
    rw [IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes L₀ q.asIdeal H hmin,
      Localization.AtPrime.map_eq_maximalIdeal]
  obtain ⟨N₀, hN₀⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (le_of_eq hrad.symm) (IsNoetherian.noetherian _)
  have hpower : IsLocalRing.maximalIdeal L₀ ^ (N₀ + 1) ≤ H.map (algebraMap Λ L₀) :=
    (Ideal.pow_le_pow_right (Nat.le_succ N₀)).trans hN₀
  obtain ⟨m, algΛ, towerΛ, C, ringC, algkC, algRC, towerC, fpC, β, γ,
    hcomp, hsing, r, π, hr, hπq, hannR, hannΛ, hstrict, hglobal⟩ :=
    exists_popescu_char_p_preparation_global p hp α q hreg (N₀ + 1) (by omega) hpower
  let := algΛ
  let := towerΛ
  let := ringC
  let := algkC
  let := algRC
  let := towerC
  let := fpC
  refine ⟨m, algΛ, towerΛ, C, ringC, algkC, algRC, towerC, fpC, β, γ,
    hcomp, hsing, r, π, hr, hπq, hannR, hannΛ, hstrict, ?_⟩
  let R := MvPolynomial (Fin m) k
  let Q := Localization.AtPrime (q.asIdeal.under R)
  let L := Localization.AtPrime q.asIdeal
  let := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
  obtain ⟨n, hn, hpow, I₀, K, hI, hK, hIK, t, D', ringD', localD', artD',
    algRE, algIE, towerE, hE, a, b, hab⟩ := hglobal
  let := ringD'
  let := localD'
  let := artD'
  let E := MvPolynomial (Fin t) D' 
  let := algRE
  let := algIE
  let := towerE
  let I := I₀.map (algebraMap R Q)
  let : Algebra (R ⧸ I₀) (Q ⧸ I) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.le_comap_map :
      I₀ ≤ I.comap (algebraMap R Q))
  have : IsScalarTower R (R ⧸ I₀) (Q ⧸ I) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra (Q ⧸ I) (L ⧸ K) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.mp hIK)
  have : IsScalarTower Q (Q ⧸ I) (L ⧸ K) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra (R ⧸ I₀) (L ⧸ K) :=
    ((algebraMap (Q ⧸ I) (L ⧸ K)).comp (algebraMap (R ⧸ I₀) (Q ⧸ I))).toAlgebra
  have : IsScalarTower (R ⧸ I₀) (Q ⧸ I) (L ⧸ K) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R (R ⧸ I₀) (L ⧸ K) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap R (L ⧸ K) r =
        Ideal.Quotient.mk K (algebraMap Q L (algebraMap R Q r))
      rw [← IsScalarTower.algebraMap_apply R Q L]
      rfl
  let D := (Q ⧸ I) ⊗[R ⧸ I₀] E
  let : Algebra Q D := Algebra.TensorProduct.leftAlgebra
    (R := R ⧸ I₀) (S := Q) (A := Q ⧸ I) (B := E)
  let : Algebra R D := Algebra.TensorProduct.leftAlgebra
    (R := R ⧸ I₀) (S := R) (A := Q ⧸ I) (B := E)
  have : IsScalarTower Q (Q ⧸ I) D := inferInstance
  have : IsScalarTower R Q D := inferInstance
  have : IsScalarTower R (R ⧸ I₀) D := inferInstance
  let j : E →ₐ[R] D :=
    (Algebra.TensorProduct.includeRight (R := R ⧸ I₀) (A := Q ⧸ I)).restrictScalars R
  let f : Q ⊗[R] C →ₐ[Q] D :=
    Algebra.TensorProduct.lift (Algebra.ofId Q D) (j.comp a) (fun _ _ ↦ Commute.all _ _)
  let b' : E →ₐ[R ⧸ I₀] L ⧸ K :=
    b.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  let g : D →ₐ[Q] L ⧸ K :=
    (Algebra.TensorProduct.lift (Algebra.ofId (Q ⧸ I) (L ⧸ K)) b'
      (fun _ _ ↦ Commute.all _ _)).restrictScalars Q
  have hD : EssentiallySmooth (Q ⧸ I) D := essentiallySmooth_baseChange hE
  refine ⟨n, hn, hpow, I, K, hI, hK, hIK, D, inferInstance, inferInstance,
    inferInstance, inferInstance, hD, f, g, ?_⟩
  ext y
  change g (f (1 ⊗ₜ[R] y)) = _
  have hf : f (1 ⊗ₜ[R] y) = (1 ⊗ₜ[R ⧸ I₀] a y) := by
    change algebraMap Q D 1 * (1 ⊗ₜ[R ⧸ I₀] a y) = _
    simp
  rw [hf]
  change algebraMap (Q ⧸ I) (L ⧸ K) 1 * b' (a y) = _
  rw [map_one, one_mul]
  change b (a y) = _
  simpa only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.lift_tmul,
    map_one, one_mul] using DFunLike.congr_fun hab y

end Algebra
