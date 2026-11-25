/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.PopescuResolution
import WeilConjectures.RingTheory.PopescuCharPPreparation
import WeilConjectures.RingTheory.PopescuDelocalizeHeightZero
import WeilConjectures.RingTheory.PopescuLiftSolution
import WeilConjectures.RingTheory.FactorsThroughSmooth

/-!
# Resolving Popescu's local problem in positive characteristic

Source: Stacks Project, Smoothing Ring Maps, Lemma 07FJ, in Section 07FF
(blueprint: lem-weil-pbc-popescu-resolve-char-p).
-/

@[expose] public section

universe u v w

namespace Algebra

private theorem singularIdeal_eq_top_of_smooth
    (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]
    [Smooth R B] : singularIdeal R B = ⊤ := by
  apply top_unique
  rw [← Ideal.span_singleton_one]
  apply Ideal.span_le.mpr
  intro x hx
  have hx1 : x = 1 := by simpa using hx
  subst x
  apply Ideal.le_radical
  apply Ideal.subset_span
  change Smooth R (Localization.Away (1 : B))
  let : Smooth B (Localization.Away (1 : B)) := Smooth.of_isLocalization_Away 1
  exact Smooth.comp R B _

private theorem popescuIdeal_eq_top_of_smooth
    {R : Type u} {B : Type v} {Λ : Type w}
    [CommRing R] [CommRing B] [CommRing Λ] [Algebra R B] [Algebra R Λ]
    [Smooth R B] (γ : B →ₐ[R] Λ) : popescuIdeal γ = ⊤ := by
  unfold popescuIdeal
  rw [singularIdeal_eq_top_of_smooth R B, Ideal.map_top, Ideal.radical_top]

private theorem resolved_of_ideal_not_le
    {R : Type u} {C : Type (max u v)} {Λ : Type w}
    [CommRing R] [CommRing C] [CommRing Λ] [Algebra R C] [Algebra R Λ]
    [IsNoetherianRing R] [FinitePresentation R C]
    (γ : C →ₐ[R] Λ) (q : PrimeSpectrum Λ) (h : ¬ popescuIdeal γ ≤ q.asIdeal) :
    CanBePopescuResolved γ q := by
  exact ⟨C, inferInstance, inferInstance, AlgHom.id R C, γ,
    inferInstance, γ.comp_id, le_rfl, h⟩

private theorem resolved_of_essentiallySmooth_factorization
    {R : Type u} {C E : Type (max u v)} {Λ : Type w}
    [CommRing R] [CommRing C] [CommRing E] [CommRing Λ]
    [Algebra R C] [Algebra R E] [Algebra R Λ]
    [IsNoetherianRing R] [FinitePresentation R C]
    (γ : C →ₐ[R] Λ) (q : PrimeSpectrum Λ)
    (hE : EssentiallySmooth R E) (f : C →ₐ[R] E) (g : E →ₐ[R] Λ)
    (hfg : g.comp f = γ) : CanBePopescuResolved γ q := by
  obtain ⟨T, instT, algT, hT, a, b, hab⟩ :=
    essentiallySmooth_factors_through_smooth R C E hE f
  let := instT
  let := algT
  let := hT
  refine ⟨T, inferInstance, inferInstance, a, g.comp b, inferInstance, ?_, ?_, ?_⟩
  · rw [AlgHom.comp_assoc, hab, hfg]
  · rw [popescuIdeal_eq_top_of_smooth (g.comp b)]
    exact le_top
  · rw [popescuIdeal_eq_top_of_smooth]
    exact fun h ↦ q.isPrime.ne_top (top_le_iff.mp h)

private theorem popescuIdeal_restrictScalars_le
    {k : Type u} {R : Type u} {B : Type v} {Λ : Type w}
    [CommRing k] [CommRing R] [CommRing B] [CommRing Λ]
    [Algebra k R] [Algebra k B] [Algebra k Λ] [Algebra R B] [Algebra R Λ]
    [IsScalarTower k R B] [IsScalarTower k R Λ] [Smooth k R]
    (γ : B →ₐ[R] Λ) : popescuIdeal γ ≤ popescuIdeal (γ.restrictScalars k) := by
  apply Ideal.radical_mono
  apply Ideal.map_mono
  apply Ideal.radical_mono
  apply Ideal.span_mono
  intro x hx
  change Smooth k (Localization.Away x)
  let : Smooth R (Localization.Away x) := hx
  exact Smooth.comp k R _

/-- Popescu's local problem over a positive-characteristic field is resolvable when the target
is Noetherian and geometrically regular and the prime is minimal over the extended singular
ideal. Source: Stacks Project, Smoothing Ring Maps, Lemma 07FJ
(blueprint: lem-weil-pbc-popescu-resolve-char-p).

Proof, following the blueprint's expanded version of the source's reduction argument:

1. (Items item-power, item-generators, item-dimension: the integers $N$, $d$ and generators of
$H_{A/k}$.) Write $H=H_{A/k}$ [def-weil-pbc-singular-ideal], $\mathfrak h_A=\sqrt{H\Lambda}$
[def-weil-pbc-popescu-resolution], $S_\Lambda=\Lambda\setminus\mathfrak q$ and $\Lambda_{\mathfrak
q}=S_\Lambda^{-1}\Lambda$ [def-weil-pbc-localization-at-prime]. The primes of $\Lambda_{\mathfrak
q}$ are the $\mathfrak q'\Lambda_{\mathfrak q}$ with $\mathfrak q'\subset\mathfrak q$ prime; if
such a $\mathfrak q'$ contains $H\Lambda$ it contains $\mathfrak h_A$, so $\mathfrak q'=\mathfrak
q$ because $\mathfrak q$ is minimal over $\mathfrak h_A$. Hence $V(H\Lambda_{\mathfrak
q})=\{\mathfrak q\Lambda_{\mathfrak q}\}=V(\mathfrak q\Lambda_{\mathfrak q})$ and
$\sqrt{H\Lambda_{\mathfrak q}}=\sqrt{\mathfrak q\Lambda_{\mathfrak q}}=\mathfrak
q\Lambda_{\mathfrak q}$ [lem-weil-pbc-zero-locus-eq-iff-radical-eq]. $\Lambda_{\mathfrak q}$ is
Noetherian [lem-weil-pbc-localization-noetherian], so $\mathfrak q\Lambda_{\mathfrak q}$ is
finitely generated and there is $N\ge1$ with $\mathfrak q^N\Lambda_{\mathfrak q}\subset
H\Lambda_{\mathfrak q}$ [lem-weil-pbc-fg-ideal-radical-power]. $A$ is of finite type over the
field $k$, hence Noetherian [lem-weil-pbc-finite-type-algebra-noetherian]; choose generators
$a_1,\dots,a_t$ of the ideal $H\subset A$ (Stacks writes $H_{A/R}$ here, a misprint for
$H_{A/k}$). Put $d=\dim\Lambda_{\mathfrak q}$. Uses: def-weil-pbc-singular-ideal,
def-weil-pbc-popescu-resolution, def-weil-pbc-localization-at-prime,
lem-weil-pbc-zero-locus-eq-iff-radical-eq, lem-weil-pbc-localization-noetherian,
lem-weil-pbc-fg-ideal-radical-power, lem-weil-pbc-finite-type-algebra-noetherian.

2. (Items item-standardizer, item-elkik, item-strictly-standard, item-set-n: the algebras $B$, $C$
and the integers $c$, $e$, $n$.) Let
$B=A[x_1,\dots,x_d,z_{ij}]/(x_i^{2N}-\sum_{j=1}^tz_{ij}a_j)_{i=1,\dots,d}$ ($i\le d$, $j\le t$), a
$k[x_1,\dots,x_d]$-algebra of finite presentation (finitely many variables and relations over the
finitely presented $k$-algebra $A$). (a) For each $j$, $A_{a_j}$ is smooth over $k$
[lem-weil-pbc-singular-ideal-localization-smooth]. In $B_{a_j}$ the $i$-th relation reads
$z_{ij}=a_j^{-1}(x_i^{2N}-\sum_{l\ne j}z_{il}a_l)$, so $B_{a_j}\cong
A_{a_j}[x_1,\dots,x_d][z_{il}:l\ne j]$ as $k[x]$-algebras (the map sending $z_{il}\mapsto z_{il}$
for $l\ne j$ and inverse sending $z_{ij}$ to that expression), i.e. a polynomial algebra over
$A_{a_j}\otimes_kk[x]$; this is smooth over $k[x]$ by base change of $k\to A_{a_j}$ along $k\to
k[x]$, the smoothness of polynomial algebras and composition
[lem-weil-pbc-smooth-ring-map-base-change-composition] [lem-weil-pbc-polynomial-ring-smooth]. (b)
In $B$, $x_i^{2N}\in(a_1,\dots,a_t)B$, so $a_1,\dots,a_t$ generate the unit ideal of $B_{x_i}$,
and $(B_{x_i})_{a_j}=(B_{a_j})_{x_i}$ is smooth over $k[x]$
[lem-weil-pbc-smooth-ring-map-principal-localization]; hence $B_{x_i}$ is smooth over $k[x]$
[lem-weil-pbc-smooth-ring-map-local-on-cover]. (c) Apply [lem-weil-pbc-improve-presentation] to
the $k[x]$-algebra $B$: we get a $B$-algebra $C$ of finite type with a $B$-algebra retraction
$\rho:C\to B$ such that $C_{x_i}$ and $C_{a_j}$ (by (b), (a)) are smooth over $k[x]$ with free
modules of differentials. $C$ is of finite type over the Noetherian ring $k[x]$
[lem-weil-pbc-finite-type-algebra-noetherian], hence of finite presentation
[lem-weil-pbc-finite-type-noetherian-finite-presentation]. By
[lem-weil-pbc-smooth-free-differentials-strictly-standard-power] there is $c\ge1$ such that
$x_1^c,\dots,x_d^c$ are strictly standard in $C$ over $k[x]$
[theorem-finite-etale-covers-proper-henselian--2] (take $c$ at least each of the $d$ bounds $e_0$).
Put $e=8c$ and $n=N+de$. (Stacks sets $n=N+dc$; the justification of item (item-sixth-resolve) needs
$\mathfrak p^nk[y]_{\mathfrak p}\subset(\pi_1^e,\dots,\pi_d^e)$ for a regular system of parameters
$\pi_1,\dots,\pi_d$, i.e. $n\ge d(e-1)+1$, which $N+dc$ does not give when $e=8c$; $n=N+de$
satisfies $n\ge N$ and $n\ge d(e-1)+1$, and nothing else in the proof bounds $n$, so this corrects
a misprint.) Let $\bar\Lambda=\Lambda_{\mathfrak q}/\mathfrak q^n\Lambda_{\mathfrak q}$ and
$E\subset\bar\Lambda$ the images of finitely many $k$-algebra generators of $A$. Uses:
lem-weil-pbc-singular-ideal-localization-smooth,
lem-weil-pbc-smooth-ring-map-base-change-composition, lem-weil-pbc-polynomial-ring-smooth,
lem-weil-pbc-smooth-ring-map-principal-localization, lem-weil-pbc-smooth-ring-map-local-on-cover,
lem-weil-pbc-improve-presentation, lem-weil-pbc-finite-type-algebra-noetherian,
lem-weil-pbc-finite-type-noetherian-finite-presentation,
lem-weil-pbc-smooth-free-differentials-strictly-standard-power,
theorem-finite-etale-covers-proper-henselian--2.

3. (Item item-NP: the solution modulo $\mathfrak q^n$.) By [lem-weil-pbc-popescu-solution-modulo]
(applicable: $k$ of characteristic $p$, $\Lambda$ Noetherian and geometrically regular, $n$ and
$E$ as in Step 2) there are $m\ge0$, a $k$-algebra map $\varphi:k[y_1,\dots,y_m]\to\Lambda$, with
$\mathfrak p=\varphi^{-1}(\mathfrak q)$ and $P_0=k[y_1,\dots,y_m]_{\mathfrak p}$, such that
$\mathfrak p\Lambda_{\mathfrak q}=\mathfrak q\Lambda_{\mathfrak q}$, $P_0\to\Lambda_{\mathfrak q}$
is flat, and a factorization $P_0/\mathfrak p^nP_0\to D\to\bar\Lambda$ by local homomorphisms of
local Artinian rings with the first arrow essentially smooth
[def-weil-pbc-essentially-smooth-ring-map], the second flat, and $E$ contained in the image of
$D$. The flat local map $D\to\bar\Lambda$ is faithfully flat
[lem-weil-pbc-flat-local-hom-faithfully-flat], hence injective
[lem-weil-pbc-faithfully-flat-ideal-contraction] (case $I=0$); we identify $D$ with its image, a
$k$-subalgebra of $\bar\Lambda$. Since $D$ contains the images of generators of $A$, the map
$A\to\bar\Lambda$ takes values in $D$; in particular $a_1,\dots,a_t\in D$. Uses:
lem-weil-pbc-popescu-solution-modulo, def-weil-pbc-essentially-smooth-ring-map,
lem-weil-pbc-flat-local-hom-faithfully-flat, lem-weil-pbc-faithfully-flat-ideal-contraction.

4. (Item item-choose-pii: the parameters $\pi_i$.) The field $k$ is a regular ring
[lem-weil-pbc-field-regular-ring] and $k\to k[y_1,\dots,y_m]$ is smooth
[lem-weil-pbc-polynomial-ring-smooth], so $k[y]$ is a regular ring
[lem-weil-pbc-regular-ring-smooth-ascent] and $P_0$ is a regular local ring
[def-weil-regular-scheme]. Apply [lem-weil-pbc-flat-height-formula] to the flat map
$P_0\to\Lambda_{\mathfrak q}$ of Noetherian rings ($k[y]$ is Noetherian
[lem-weil-pbc-finite-type-algebra-noetherian], localizations of Noetherian rings are Noetherian
[lem-weil-pbc-localization-noetherian]) and the maximal ideal $\mathfrak q\Lambda_{\mathfrak q}$,
which lies over $\mathfrak pP_0$ (Step 3: $\mathfrak q\Lambda_{\mathfrak q}=\mathfrak
p\Lambda_{\mathfrak q}$): the prime $\mathfrak q\Lambda_{\mathfrak q}/\mathfrak
p\Lambda_{\mathfrak q}$ is the zero ideal of the field $\Lambda_{\mathfrak q}/\mathfrak
q\Lambda_{\mathfrak q}$, of height $0$, so $d=\dim\Lambda_{\mathfrak q}=\dim P_0$
[def-weil-pbc-localization-at-prime]. As $P_0$ is regular of dimension $d$, $\mathfrak pP_0$ is
generated by $d$ elements; multiplying them by units of $P_0$ we may take them as images of
$\pi_1,\dots,\pi_d\in\mathfrak p$. Their images generate $\mathfrak pP_0\Lambda_{\mathfrak
q}=\mathfrak q\Lambda_{\mathfrak q}$, so $\Lambda_{\mathfrak q}$, a Noetherian local ring of
dimension $d$ whose maximal ideal is generated by $d$ elements, is a regular local ring
[def-weil-regular-scheme] with regular system of parameters $\pi_1,\dots,\pi_d$. (Stacks writes
'pi_1,...,pi_d in Lambda which map to a regular system of parameters in Lambda_q'; the elements
are taken in $k[y]$, as item (item-choose-pii) says.) Uses: lem-weil-pbc-field-regular-ring,
lem-weil-pbc-polynomial-ring-smooth, lem-weil-pbc-regular-ring-smooth-ascent,
def-weil-regular-scheme, lem-weil-pbc-flat-height-formula,
lem-weil-pbc-finite-type-algebra-noetherian, lem-weil-pbc-localization-noetherian,
def-weil-pbc-localization-at-prime.

5. (Items item-set-R, item-modify-pii: the ring $R$ and the annihilator conditions in $R$.) Let
$R=k[y_1,\dots,y_m,t_1,\dots,t_d]$ (Stacks writes $t_1,\dots,t_m$ in item (item-set-R), a misprint
for $t_d$ as in item (item-set-map-R)), $\gamma_i=\pi_it_i$, $S_0=k[y]\setminus\mathfrak p$, so
$S_0^{-1}R=P_0[t_1,\dots,t_d]$. Each permutation of $\pi_1,\dots,\pi_d$ generates $\mathfrak pP_0$
and so is a regular sequence in $P_0$ [lem-weil-pbc-regular-local-generators-regular-sequence]
[def-weil-pbc-regular-sequence]; the $\pi_i$ lie in the maximal ideal, so by
[lem-weil-pbc-regular-sequence-polynomial-variables] $\gamma_1,\dots,\gamma_d$ is a regular
sequence in $S_0^{-1}R$. Both facts persist when the $\pi_i$ are multiplied by elements of $S_0$
(units of $P_0$). We modify $\pi_1,\dots,\pi_d$ one at a time so that for $i=1,\dots,d$:
$\operatorname{Ann}_{M_i}(\gamma_i)=\operatorname{Ann}_{M_i}(\gamma_i^2)$,
$M_i=R/(\gamma_1^e,\dots,\gamma_{i-1}^e)R$. Suppose this holds for $i\le t_0$. By
[lem-weil-pbc-regular-sequence-powers] (exponents $e,\dots,e,1$),
$\gamma_1^e,\dots,\gamma_{t_0}^e,\gamma_{t_0+1}$ is a regular sequence in $S_0^{-1}R$, so
$\gamma_{t_0+1}$ is a nonzerodivisor on
$S_0^{-1}M_{t_0+1}=S_0^{-1}R/(\gamma_1^e,\dots,\gamma_{t_0}^e)$ and
$\operatorname{Ker}(\gamma_{t_0+1})=0=\operatorname{Ker}(\gamma_{t_0+1}^2)$ there. $R$ is
Noetherian [lem-weil-pbc-finite-type-algebra-noetherian] and $M_{t_0+1}$ is a finite $R$-module,
so [lem-weil-pbc-ogoma] gives $s\in S_0$ with
$\operatorname{Ann}_{M_{t_0+1}}(s\gamma_{t_0+1})=
\operatorname{Ann}_{M_{t_0+1}}((s\gamma_{t_0+1})^2)$
(its case $n=1$). Replace $\pi_{t_0+1}$ by $s\pi_{t_0+1}$ (still in $\mathfrak p$;
$\gamma_{t_0+1}$ becomes $s\gamma_{t_0+1}$); the conditions for $i\le t_0$ involve only
$\gamma_1,\dots,\gamma_{t_0}$ and are unchanged. Induction on $t_0$ gives the conditions for all
$i\le d$; Step 4 still holds for the modified $\pi_i$. Uses:
lem-weil-pbc-regular-local-generators-regular-sequence, def-weil-pbc-regular-sequence,
lem-weil-pbc-regular-sequence-polynomial-variables, lem-weil-pbc-regular-sequence-powers,
lem-weil-pbc-finite-type-algebra-noetherian, lem-weil-pbc-ogoma.

6. (Item item-choose-deltai: the units $\delta_i$, the elements $\lambda_{ij}$ and the enlarged
$D'$.) We show by induction on $t_0\in\{0,\dots,d\}$: there are $\delta_1,\dots,\delta_{t_0}\in
S_\Lambda$, $\lambda_{ij}\in\Lambda$ ($i\le t_0$) and a factorization $D\to D'\to\bar\Lambda$ by
local homomorphisms of local Artinian rings, $D\to D'$ essentially smooth, $D'\to\bar\Lambda$
flat, such that with $\pi'_i=\delta_i\pi_i$: (a) $(\pi'_i)^{2N}=\sum_ja_j\lambda_{ij}$ in
$\Lambda$ and the image of $\lambda_{ij}$ in $\bar\Lambda$ lies in $D'$; (b)
$\operatorname{Ann}_{\Lambda/({\pi'_1}^e,\dots,{\pi'_{i-1}}^e)}(\pi'_i)=
\operatorname{Ann}_{\Lambda/({\pi'_1}^e,\dots,{\pi'_{i-1}}^e)}({\pi'_i}^2)$;
(c) the image of $\delta_i$ in $\bar\Lambda$ lies in $D'$. For $t_0=0$ take $D'=D$ ($D\to D$ is
smooth, so essentially smooth). Throughout, $P_0/\mathfrak p^nP_0\to D'$ is essentially smooth
[lem-weil-pbc-essentially-smooth-composition], so [lem-weil-pbc-popescu-enlarge-solution-modulo]
applies to $D'$ in place of $D$, and each enlargement $D'\to D''$ is again essentially smooth over
$D$ [lem-weil-pbc-essentially-smooth-composition], keeps (a)-(c) for the earlier indices (the
image only grows), and $D''\to\bar\Lambda$ is flat local, hence faithfully flat
[lem-weil-pbc-flat-local-hom-faithfully-flat] and injective
[lem-weil-pbc-faithfully-flat-ideal-contraction]; we identify $D''$ with its image. Inductive
step, $\pi=\pi_{t_0+1}$: $\pi^N\in\mathfrak q^N\Lambda_{\mathfrak q}\subset H\Lambda_{\mathfrak
q}$ (Step 1), so in $\bar\Lambda$, $\pi^N\in(a_1,\dots,a_t)\bar\Lambda$; $\pi$ and the $a_j$ lie
in $D'$ (Step 3), so $\pi^N\in(a_1,\dots,a_t)\bar\Lambda\cap D'=(a_1,\dots,a_t)D'$
[lem-weil-pbc-faithfully-flat-ideal-contraction]: $\pi^N=\sum_ja_jd_j$, $d_j\in D'$. Lift $d_j$ to
$c_j\in\Lambda_{\mathfrak q}$; then $\varepsilon=\pi^N-\sum c_ja_j\in\mathfrak
q^n\Lambda_{\mathfrak q}=\mathfrak q^{n-N}\mathfrak q^N\Lambda_{\mathfrak q}\subset\mathfrak
q^{n-N}H\Lambda_{\mathfrak q}$, so $\varepsilon=\sum a_jc'_j$ with $c'_j\in\mathfrak
q^{n-N}\Lambda_{\mathfrak q}$, and $\pi^{2N}=\sum_jw_ja_j$ with $w_j=\pi^N(c_j+c'_j)$, where
$\pi^Nc'_j\in\mathfrak q^n\Lambda_{\mathfrak q}$ maps to $0$ in $\bar\Lambda$ (the 'key
observation' of Stacks). (The detail Stacks omits:) write $w_j=u_j/s_0$ with $u_j\in\Lambda$,
$s_0\in S_\Lambda$; then $s_0\pi^{2N}-\sum u_ja_j$ is $0$ in $\Lambda_{\mathfrak q}$, so
$s_1(s_0\pi^{2N}-\sum u_ja_j)=0$ in $\Lambda$ for some $s_1\in S_\Lambda$; with $s=s_0s_1$ and
$\mu_j=s^{2N-1}s_1u_j$ we get $(s\pi)^{2N}=\sum_j\mu_ja_j$ in $\Lambda$ and $\mu_j/s^{2N}=w_j$.
Enlarge $D'$ by [lem-weil-pbc-popescu-enlarge-solution-modulo] with $\lambda=s$ so that some
$s^{q_1}\in D'$, and replace $s$ by $s^{q_1}$ and $\mu_j$ by $s^{2N(q_1-1)}\mu_j$ (both equations
persist); now $s\in D'$ and the image of $\mu_j$ in $\bar\Lambda$ is $s^{2N}\pi^Nd_j\in D'$
(Stacks writes $s^{2N}d_j$). Next, $\pi_1,\dots,\pi_d$ is a regular sequence in the regular local
ring $\Lambda_{\mathfrak q}$ (Step 4, [lem-weil-pbc-regular-local-generators-regular-sequence]);
multiplying its terms by the units $\delta_1,\dots,\delta_{t_0},s$ of $\Lambda_{\mathfrak q}$
keeps it regular (the ideals $(f_1,\dots,f_{i-1})$ and the nonzerodivisor conditions are
unchanged) [def-weil-pbc-regular-sequence], and by [lem-weil-pbc-regular-sequence-powers]
${\pi'_1}^e,\dots,{\pi'_{t_0}}^e,s\pi$ is a regular sequence in $S_\Lambda^{-1}\Lambda$. So on
$M=\Lambda/({\pi'_1}^e,\dots,{\pi'_{t_0}}^e)$, a finite module over the Noetherian ring $\Lambda$,
multiplication by $s\pi$ is injective on $S_\Lambda^{-1}M$, whence
$\operatorname{Ker}(s\pi)=\operatorname{Ker}((s\pi)^2)$ on $S_\Lambda^{-1}M$, and
[lem-weil-pbc-ogoma] gives $s'\in S_\Lambda$ with
$\operatorname{Ann}_M((s')^qs\pi)=\operatorname{Ann}_M(((s')^qs\pi)^2)$ for every $q>0$. By
[lem-weil-pbc-popescu-enlarge-solution-modulo] with $\lambda=s'$ choose $q$ and enlarge $D'$ so
that $(s')^q\in D'$. Set $\delta_{t_0+1}=(s')^qs$ and $\lambda_{t_0+1,j}=(s')^{2Nq}\mu_j$: then
$(\pi'_{t_0+1})^{2N}=(s')^{2Nq}(s\pi)^{2N}=\sum_ja_j\lambda_{t_0+1,j}$ with
$\lambda_{t_0+1,j}\mapsto(s')^{2Nq}s^{2N}\pi^Nd_j\in D'$, which is (a); (b) is the choice of $s'$;
(c) holds as $s,(s')^q\in D'$. Uses: lem-weil-pbc-essentially-smooth-composition,
lem-weil-pbc-popescu-enlarge-solution-modulo, lem-weil-pbc-flat-local-hom-faithfully-flat,
lem-weil-pbc-faithfully-flat-ideal-contraction,
lem-weil-pbc-regular-local-generators-regular-sequence, def-weil-pbc-regular-sequence,
lem-weil-pbc-regular-sequence-powers, lem-weil-pbc-ogoma,
def-weil-pbc-essentially-smooth-ring-map.

7. (Items item-map-B-Lambda, item-set-map-R, item-first-solve: the maps and the first reduction,
to the base $R$.) Define $B\to\Lambda$ by $\alpha$ on $A$, $x_i\mapsto\pi'_i$,
$z_{ij}\mapsto\lambda_{ij}$; it is well defined by Step 6(a). Let $C\to\Lambda$ be $B\to\Lambda$
composed with $\rho$; since $\rho$ is a $B$-algebra map, $A\to C\to\Lambda$ is $\alpha$. Map
$R\to\Lambda$ by $\varphi$ on $k[y]$ and $t_i\mapsto\delta_i$, and $k[x_1,\dots,x_d]\to R$ by
$x_i\mapsto\gamma_i$. Both composites $k[x]\to\Lambda$ send $x_i$ to $\pi_i\delta_i=\pi'_i$, so we
get an $R$-algebra map $C':=C\otimes_{k[x]}R\to\Lambda$, $C'$ of finite presentation over $R$
(base change of the finitely presented $k[x]$-algebra $C$, Step 2), and $R$ is Noetherian
[lem-weil-pbc-finite-type-algebra-noetherian]: $R\to C'\to\Lambda\supset\mathfrak q$ is a
situation as in [def-weil-pbc-popescu-resolution], and $A\to C\to C'$ makes $C'$ an $A$-algebra
compatibly with $\alpha$. Claim: a resolution of $R\to C'\to\Lambda\supset\mathfrak q$ gives one
of $k\to A\to\Lambda\supset\mathfrak q$. First, $C_{a_j}$ is smooth over $k[x]$ (Step 2(c)), so
$C'_{a_j\otimes1}=C_{a_j}\otimes_{k[x]}R$ is smooth over $R$
[lem-weil-pbc-smooth-ring-map-base-change-composition], i.e. $a_j\otimes1\in H_{C'/R}$
[def-weil-pbc-singular-ideal]; so $H\Lambda=(a_1,\dots,a_t)\Lambda\subset H_{C'/R}\Lambda$ and
$\mathfrak h_A\subset\mathfrak h_{C'}$. Let $C'\to T\to\Lambda$ be a resolution: $T$ of finite
presentation over $R$, $\mathfrak h_{C'}\subset\sqrt{H_{T/R}\Lambda}\not\subset\mathfrak q$. As
$R$ is a polynomial ring over $k$, a finite presentation of $T$ over $R$ is one over $k$. If $T_g$
is smooth over $R$, it is smooth over $k$ because $k\to R$ is smooth
[lem-weil-pbc-polynomial-ring-smooth] [lem-weil-pbc-smooth-ring-map-base-change-composition];
hence $H_{T/R}\subset H_{T/k}$ and $\mathfrak h_A\subset\mathfrak
h_{C'}\subset\sqrt{H_{T/R}\Lambda}\subset\sqrt{H_{T/k}\Lambda}$, while
$\sqrt{H_{T/k}\Lambda}\not\subset\mathfrak q$. So $A\to T\to\Lambda$ is a resolution of $k\to
A\to\Lambda\supset\mathfrak q$ [def-weil-pbc-popescu-resolution]. Uses:
lem-weil-pbc-finite-type-algebra-noetherian, def-weil-pbc-popescu-resolution,
lem-weil-pbc-smooth-ring-map-base-change-composition, def-weil-pbc-singular-ideal,
lem-weil-pbc-polynomial-ring-smooth.

8. (Items item-set-I, item-second-resolve: reduction modulo $I=(\gamma_1^e,\dots,\gamma_d^e)$.)
Apply [lem-weil-pbc-popescu-lift-solution] to $R\to C'\to\Lambda\supset\mathfrak q$ with $r=d$ and
the elements $\gamma_1^c,\dots,\gamma_d^c\in R$, whose images $(\pi'_i)^c$ in $\Lambda$ lie in
$\mathfrak q$; note $(\gamma_i^c)^8=\gamma_i^e$. Hypothesis (1): for a module $M$ and an element
$x$ with $\operatorname{Ann}_M(x)=\operatorname{Ann}_M(x^2)$ one has
$\operatorname{Ann}_M(x^j)=\operatorname{Ann}_M(x)$ for all $j\ge1$ (if $x^{j+1}m=0$ then
$x^2(x^{j-1}m)=0$, so $x(x^{j-1}m)=0$; induct), hence
$\operatorname{Ann}_M(x^c)=\operatorname{Ann}_M(x^{2c})$; applied to $x=\gamma_i$ on
$R/(\gamma_1^e,\dots,\gamma_{i-1}^e)$ (Step 5) and to $x=\pi'_i$ on
$\Lambda/({\pi'_1}^e,\dots,{\pi'_{i-1}}^e)$ (Step 6(b)) this is (1). Hypothesis (2): $x_i^c$ is
strictly standard in $C$ over $k[x]$ (Step 2), so its image $x_i^c\otimes1=1\otimes\gamma_i^c$ is
strictly standard in $C'$ over $R$ [lem-weil-pbc-strictly-standard-base-change]
[theorem-finite-etale-covers-proper-henselian--2]. Hence it suffices to resolve $R/I\to
C\otimes_{k[x]}R/I\to\Lambda/I\Lambda\supset\mathfrak q/I\Lambda$ (note
$C'/IC'=C\otimes_{k[x]}R/I$ and $I\Lambda=({\pi'_1}^e,\dots,{\pi'_d}^e)$). Uses:
lem-weil-pbc-popescu-lift-solution, lem-weil-pbc-strictly-standard-base-change,
theorem-finite-etale-covers-proper-henselian--2.

9. (Items item-set-r, item-third-resolve: localization; the target becomes local Artinian.) Let
$\mathfrak r\subset R$ be the inverse image of $\mathfrak q$. In $\Lambda_{\mathfrak q}$ the
$\delta_i$ are units, so $I\Lambda_{\mathfrak q}=(\pi_1^e,\dots,\pi_d^e)\Lambda_{\mathfrak q}$;
since $\pi_1,\dots,\pi_d$ generate $\mathfrak q\Lambda_{\mathfrak q}$ (Step 4) and every monomial
of degree $d(e-1)+1$ in $d$ letters has an exponent $\ge e$, $\mathfrak
q^{d(e-1)+1}\Lambda_{\mathfrak q}\subset I\Lambda_{\mathfrak q}\subset\mathfrak
q\Lambda_{\mathfrak q}$, so $\Lambda_{\mathfrak q}/I\Lambda_{\mathfrak q}$ has the single prime
$\mathfrak q\Lambda_{\mathfrak q}/I\Lambda_{\mathfrak q}$ and dimension $0$. Apply
[lem-weil-pbc-popescu-delocalize-height-zero] to $R/I\to
C\otimes_{k[x]}R/I\to\Lambda/I\Lambda\supset\mathfrak q/I\Lambda$, whose prime of $R/I$ below
$\mathfrak q/I\Lambda$ is $\mathfrak r/I$ and whose localizations
[def-weil-pbc-localization-at-prime] are $(R/I)_{\mathfrak r}$ and $(\Lambda/I\Lambda)_{\mathfrak
q}=\Lambda_{\mathfrak q}/I\Lambda_{\mathfrak q}$: hypothesis (3) was just shown. For (1): let
$\mathfrak h$ be the ideal $\mathfrak h_{C\otimes R/I}$ of this situation
[def-weil-pbc-popescu-resolution]. If $\mathfrak h\not\subset\mathfrak q/I\Lambda$, the identity
factorization is a resolution and we are done. Otherwise $\mathfrak q/I\Lambda$ is minimal over
$\mathfrak h$, because the primes of $\Lambda/I\Lambda$ contained in it correspond to primes of
$\Lambda_{\mathfrak q}/I\Lambda_{\mathfrak q}$, of which there is one. (Stacks does not check
(1).) So it suffices to resolve $(R/I)_{\mathfrak r}\to C\otimes_{k[x]}(R/I)_{\mathfrak
r}\to\Lambda_{\mathfrak q}/I\Lambda_{\mathfrak q}\supset\mathfrak q\Lambda_{\mathfrak
q}/I\Lambda_{\mathfrak q}$. From now on the target is a local ring with one prime, and for any
base $R'$ and factorization through a smooth $R'$-algebra $T$ [def-weil-pbc-smooth-ring-map] we
have $1\in H_{T/R'}$ (since $T_1=T$ is smooth) [def-weil-pbc-singular-ideal], so $\mathfrak h_T$
is the unit ideal, contains the $\mathfrak h$ of the situation and is not contained in the maximal
ideal: a factorization through a smooth algebra over the base is a resolution
[def-weil-pbc-popescu-resolution]. We find such factorizations below. Uses:
lem-weil-pbc-popescu-delocalize-height-zero, def-weil-pbc-localization-at-prime,
def-weil-pbc-popescu-resolution, def-weil-pbc-smooth-ring-map, def-weil-pbc-singular-ideal.

10. (Items item-fourth-resolve, item-fifth-resolve, item-sixth-resolve, item-seventh-resolve: from
$(R/I)_{\mathfrak r}$ to $(R/\mathfrak p^nR)_{\mathfrak p}$ and from $C$ to $B$.) Let
$J=(\pi_1^e,\dots,\pi_d^e)\subset k[y]$ and, for an $R$-module, $(-)_{\mathfrak p}$ the
localization at $S_0=k[y]\setminus\mathfrak p\subset R\setminus\mathfrak r$. Each
$t_i\notin\mathfrak r$ (it maps to $\delta_i\notin\mathfrak q$), so $t_i$ is a unit in
$R_{\mathfrak r}$ and $IR_{\mathfrak r}=JR_{\mathfrak r}$; thus $(R/I)_{\mathfrak
r}=(R/JR)_{\mathfrak r}$, a localization of $(R/JR)_{\mathfrak p}$, and $I\Lambda_{\mathfrak
q}=J\Lambda_{\mathfrak q}$. Hence a factorization $C\otimes_{k[x]}(R/JR)_{\mathfrak p}\to
T\to\Lambda_{\mathfrak q}/J\Lambda_{\mathfrak q}$ with $T$ smooth over $(R/JR)_{\mathfrak p}$
gives $T_{\mathfrak r}=T\otimes_{(R/JR)_{\mathfrak p}}(R/I)_{\mathfrak r}$, smooth over
$(R/I)_{\mathfrak r}$ [lem-weil-pbc-smooth-ring-map-base-change-composition], with
$C\otimes_{k[x]}(R/I)_{\mathfrak r}\to T_{\mathfrak r}\to\Lambda_{\mathfrak q}/I\Lambda_{\mathfrak
q}$ (the target is a $(R/I)_{\mathfrak r}$-algebra), which resolves the situation of Step 9. Next,
$\mathfrak pP_0$ and $\mathfrak q\Lambda_{\mathfrak q}$ are generated by $\pi_1,\dots,\pi_d$ and
$n=N+de\ge d(e-1)+1$ (Step 2), so $\mathfrak p^nP_0\subset JP_0$ and $\mathfrak
q^n\Lambda_{\mathfrak q}\subset J\Lambda_{\mathfrak q}$ (monomial count as in Step 9); hence
$(R/JR)_{\mathfrak p}$ is a quotient of $(R/\mathfrak p^nR)_{\mathfrak p}$ and $\Lambda_{\mathfrak
q}/J\Lambda_{\mathfrak q}$ a quotient of $\bar\Lambda$, and a factorization
$C\otimes_{k[x]}(R/\mathfrak p^nR)_{\mathfrak p}\to T\to\bar\Lambda$ with $T$ smooth gives $T/JT$,
smooth over $(R/JR)_{\mathfrak p}$ [lem-weil-pbc-smooth-ring-map-base-change-composition], with
$C\otimes(R/JR)_{\mathfrak p}\to T/JT\to\Lambda_{\mathfrak q}/J\Lambda_{\mathfrak q}$ (Stacks' 'Ad
(item-sixth-resolve)' has the two item labels interchanged in its last sentence and uses $n=N+dc$;
see Step 2). Finally $\rho:C\to B$ is a $k[x]$-algebra map with $C\to\Lambda$ factoring through
it, so a factorization $B\otimes_{k[x]}(R/\mathfrak p^nR)_{\mathfrak p}\to T\to\bar\Lambda$
through a smooth $T$, precomposed with $\rho\otimes1$, gives one for $C\otimes_{k[x]}(R/\mathfrak
p^nR)_{\mathfrak p}$. It remains to find a factorization of $B\otimes_{k[x]}(R/\mathfrak
p^nR)_{\mathfrak p}\to\bar\Lambda$ through a smooth $(R/\mathfrak p^nR)_{\mathfrak p}$-algebra.
Uses: lem-weil-pbc-smooth-ring-map-base-change-composition.

11. (Items item-eighth-resolve, item-done: the factorization through $D'[t]$; conclusion.) Let
$R_0=P_0/\mathfrak p^nP_0$, so $(R/\mathfrak p^nR)_{\mathfrak p}=R_0[t_1,\dots,t_d]$. By Step 6,
$R_0\to D'$ is essentially smooth [lem-weil-pbc-essentially-smooth-composition]: $D'\cong S^{-1}Q$
with $Q$ smooth over $R_0$ [def-weil-pbc-essentially-smooth-ring-map]; then
$D'[t]=S^{-1}(Q\otimes_{R_0}R_0[t])$ with $Q\otimes_{R_0}R_0[t]$ smooth over $R_0[t]$
[lem-weil-pbc-smooth-ring-map-base-change-composition], so $R_0[t]\to D'[t]$ is essentially
smooth. The images $\bar\delta_i\in D'$ of $\delta_i$ (Step 6(c)) are units of $D'$: they map to
units of $\bar\Lambda$ and $D'\to\bar\Lambda$ is local. Define $\psi:B\otimes_{k[x]}R_0[t]\to
D'[t]$ by $A\to D\subset D'$ on $A$ (Step 3), $R_0\to D\to D'$ and $t_i\mapsto t_i$ on $R_0[t]$,
$x_i\mapsto\pi_it_i$ and $z_{ij}\mapsto\bar\lambda_{ij}t_i^{2N}\bar\delta_i^{-2N}$
($\bar\lambda_{ij}\in D'$ by Step 6(a)). It respects the relations:
$\sum_ja_j\bar\lambda_{ij}t_i^{2N}\bar\delta_i^{-2N}=
t_i^{2N}\bar\delta_i^{-2N}(\pi'_i)^{2N}=
t_i^{2N}\pi_i^{2N}$,
using Step 6(a) in $\bar\Lambda$ and the injectivity of $D'\to\bar\Lambda$
[lem-weil-pbc-flat-local-hom-faithfully-flat] [lem-weil-pbc-faithfully-flat-ideal-contraction];
and $x_i\mapsto\pi_it_i$ is the image of $\gamma_i$, so $\psi$ is a well-defined $R_0[t]$-algebra
map (Stacks' 'final twist': $z_{ij}\mapsto\lambda_{ij}$ would not be compatible with $k[x]\to
R_0[t]$). The map $D'[t]\to\bar\Lambda$ extending $D'\subset\bar\Lambda$ by $t_i\mapsto\delta_i$
composed with $\psi$ sends $x_i\mapsto\pi_i\delta_i=\pi'_i$, $z_{ij}\mapsto\lambda_{ij}$, and
agrees with the given maps on $A$ and $R_0[t]$: it is the map of Step 7 reduced to $\bar\Lambda$.
As $B\otimes_{k[x]}R_0[t]$ is of finite presentation over $R_0[t]$ (base change of $B$, Step 2),
[lem-weil-pbc-essentially-smooth-factors-through-smooth] factors $\psi$ as
$B\otimes_{k[x]}R_0[t]\to T\to D'[t]$ with $T$ smooth over $R_0[t]$, and $B\otimes R_0[t]\to T\to
D'[t]\to\bar\Lambda$ is the factorization required at the end of Step 10. Going back through Steps
10, 9, 8 and 7 (each turning a resolution of the later situation into one of the earlier) shows
that $k\to A\to\Lambda\supset\mathfrak q$ can be resolved [def-weil-pbc-popescu-resolution]. Uses:
lem-weil-pbc-essentially-smooth-composition, def-weil-pbc-essentially-smooth-ring-map,
lem-weil-pbc-smooth-ring-map-base-change-composition, lem-weil-pbc-flat-local-hom-faithfully-flat,
lem-weil-pbc-faithfully-flat-ideal-contraction,
lem-weil-pbc-essentially-smooth-factors-through-smooth, def-weil-pbc-popescu-resolution.
-/
theorem canBePopescuResolved_of_char_pos
    {k : Type u} {A : Type v} {Λ : Type w}
    [Field k] [CommRing A] [CommRing Λ] [Algebra k A] [Algebra k Λ]
    [FinitePresentation k A] [IsNoetherianRing Λ]
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (α : A →ₐ[k] Λ) (q : PrimeSpectrum Λ)
    (hreg : IsGeometricallyRegular k Λ)
    (hminimal : q.asIdeal ∈ (popescuIdeal α).minimalPrimes) :
    CanBePopescuResolved α q := by
  obtain ⟨m, algΛ, towerΛ, C, ringC, algkC, algRC, towerC, fpC, β, γ,
    hcomp, hdom, r, π, hr, hπ, hR, hΛ, hstandard, fp₀, γ₀, q₀, hγ₀, hq₀, hlocal⟩ :=
    exists_popescu_char_p_preparation p hp α q hreg hminimal
  let R := MvPolynomial (Fin m) k
  let : Smooth k R := ⟨inferInstance, inferInstance⟩
  let := algΛ
  let := towerΛ
  let := ringC
  let := algkC
  let := algRC
  let := towerC
  let := fpC
  let J := Ideal.span (Set.range (fun i : Fin r ↦ π i ^ 8))
  let J_C := J.map (algebraMap R C)
  let J_Λ := J.map (algebraMap R Λ)
  let R₀ := R ⧸ J
  let C₀ := C ⧸ J_C
  let Λ₀ := Λ ⧸ J_Λ
  let := fp₀
  have hresolved₀ : CanBePopescuResolved γ₀ q₀ := by
    rcases hlocal with hout | ⟨hmin₀, hdim₀, hfactor⟩
    · exact resolved_of_ideal_not_le γ₀ q₀ hout
    · apply canBePopescuResolved_of_local_height_zero γ₀ q₀ hmin₀ _ hdim₀
      let P := Localization.AtPrime (q₀.asIdeal.under R₀)
      let L := Localization.AtPrime q₀.asIdeal
      let := Localization.AtPrime.algebraOfLiesOver
        (q₀.asIdeal.under R₀) q₀.asIdeal
      obtain ⟨E, ringE, algE, hE, f, g, hfg⟩ := hfactor
      let := ringE
      let := algE
      exact resolved_of_essentiallySmooth_factorization _ _ hE f g hfg
  have hresolved : CanBePopescuResolved γ q :=
    canBePopescuResolved_of_quotient_eighth_powers r π γ q hr hπ hR hΛ hstandard
      ⟨fp₀, γ₀, q₀, hγ₀, hq₀, hresolved₀⟩
  obtain ⟨B, ringB, algRB, a, b, hfpB, hab, hCB, hout⟩ := hresolved
  let := ringB
  let := algRB
  let : Algebra k B := ((algebraMap R B).comp (algebraMap k R)).toAlgebra
  let : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq' rfl
  let := hfpB
  let : FinitePresentation k B := FinitePresentation.trans k R B
  refine ⟨B, inferInstance, inferInstance, (a.restrictScalars k).comp β,
    b.restrictScalars k, inferInstance, ?_, ?_, ?_⟩
  · ext x
    have h := AlgHom.congr_fun hab (β x)
    have h' := AlgHom.congr_fun hcomp x
    exact h.trans h'
  · exact hdom.trans (hCB.trans (popescuIdeal_restrictScalars_le b))
  · exact fun h ↦ hout ((popescuIdeal_restrictScalars_le b).trans h)

end Algebra
