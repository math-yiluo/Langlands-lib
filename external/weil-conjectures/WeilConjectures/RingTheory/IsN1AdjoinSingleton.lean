/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NagataRing
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AsSubring
import WeilConjectures.RingTheory.IsN1OfFiniteDomainExtension
import WeilConjectures.RingTheory.IsN1OfIsAnalyticallyUnramified
import WeilConjectures.RingTheory.IsN1OfLocalCharacterization
import WeilConjectures.RingTheory.AdjoinSingletonLocalUnramified
import WeilConjectures.RingTheory.AdjoinSingletonMaximalFiniteCover

/-!
# Normalization of a monogenic subalgebra of a normal Nagata domain's fraction field

Source: Stacks Project, Algebra, Proposition 10.162.15 (Tag 0334), statement (***) at the
end of Step 4 and its proof in Step 5 (blueprint: lem-weil-pbc-normal-nagata-monogenic-n1).
-/

@[expose] public section

universe u v

/-- Clearing one denominator identifies a principal open of `R[x]` with one of `R`. -/
private theorem adjoin_singleton_normal_away (R : Type u) (K : Type v)
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] (x : K) :
    ∃ f : Algebra.adjoin R ({x} : Set K), f ≠ 0 ∧
      ∀ (p : Ideal (Localization.Away f)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  classical
  obtain ⟨b, a, hx⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors R) x
  have ha : (a : R) ≠ 0 := nonZeroDivisors.ne_zero a.property
  let S := Algebra.adjoin R ({x} : Set K)
  let M := Submonoid.powers (a : R)
  have hM : M ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors ha
  let T := Localization.subalgebra K M hM
  have hxT : x ∈ T := by
    refine ⟨b, a, Submonoid.mem_powers _, ?_⟩
    exact hx.symm
  have hST : S ≤ T := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hxT)
  let : Algebra S T := (Subalgebra.inclusion hST).toRingHom.toAlgebra
  let : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' (by ext r; rfl)
  let f : S := algebraMap R S a
  have hf : f ≠ 0 := by
    intro h
    apply ha
    apply IsFractionRing.injective R K
    have := congrArg (fun z : S ↦ (z : K)) h
    simpa only [f, Subalgebra.coe_algebraMap, ZeroMemClass.coe_zero, map_zero] using this
  let : IsLocalization.Away f T := by
    refine IsLocalization.Away.mk f ?_ ?_ ?_
    · change IsUnit (algebraMap R T a)
      exact IsLocalization.Away.algebraMap_isUnit (a : R)
    · intro t
      obtain ⟨n, r, hr⟩ := IsLocalization.Away.surj (a : R) t
      exact ⟨n, algebraMap R S r, hr⟩
    · intro c d h
      have hcd : c = d := Subtype.ext (congrArg (fun z : T ↦ (z : K)) h)
      exact ⟨0, by simp [hcd]⟩
  let : IsIntegrallyClosed T := isIntegrallyClosed_of_isLocalization T M hM
  let e : T ≃ₐ[S] Localization.Away f :=
    IsLocalization.algEquiv (Submonoid.powers f) T (Localization.Away f)
  let : IsDomain (Localization.Away f) := IsLocalization.Away.isDomain _ hf
  let : IsIntegrallyClosed (Localization.Away f) := IsIntegrallyClosed.of_equiv e.toRingEquiv
  refine ⟨f, hf, ?_⟩
  intro p hp
  exact ⟨inferInstance, isIntegrallyClosed_of_isLocalization
    (Localization.AtPrime p) p.primeCompl p.primeCompl_le_nonZeroDivisors⟩

/-- For a normal Nagata domain `R` with fraction field `K`, the subring `R[x]` of `K`
is N-1: its integral closure in `K` is finite as an `R[x]`-module.
Source: Stacks Project, Algebra, Proposition 10.162.15 (Tag 0334), (***) and Step 5
(blueprint: lem-weil-pbc-normal-nagata-monogenic-n1).

Proof:

1. If $x=0$, then $S=R$ is normal [def-weil-pbc-normal-ring], hence its integral closure in $K$
is $R$ itself and it is N-1. Assume $x\ne0$ and write $x=b/a$ with $a,b\in R$, $a\ne0$. Since
$R$ is Noetherian by [def-weil-pbc-nagata-ring], its one-generator algebra $S=R[x]$ is
Noetherian by [lem-weil-pbc-finite-type-algebra-noetherian]. Inverting $a$ gives $S_a=R_a$,
because $x=b/a\in R_a$; this ring is normal by [lem-weil-pbc-localization-normal-domain]. Thus
[lem-weil-pbc-n1-local-characterization] reduces the claim to proving $S_{\mathfrak m}$ is N-1
for each maximal ideal $\mathfrak m\subset S$. Dependencies: def-weil-pbc-normal-ring,
def-weil-pbc-nagata-ring, lem-weil-pbc-finite-type-algebra-noetherian,
lem-weil-pbc-localization-normal-domain, lem-weil-pbc-n1-local-characterization.

2. Fix $\mathfrak m$ and set $\mathfrak n=R\cap\mathfrak m$. The field $\kappa(\mathfrak m)$ is
generated as a $\kappa(\mathfrak n)$-algebra by the residue of $x$, because $S=R[x]$; it is
finite over $\kappa(\mathfrak n)$ by [lem-weil-pbc-zariski-lemma]. Let $\bar
f(T)=T^d+\sum_{i=1}^d\bar c_iT^{d-i}\in\kappa(\mathfrak n)[T]$ be the monic minimal polynomial
of the residue of $x$. Lift each $\bar c_i$ to a fraction $c_i/s_i\in R_{\mathfrak n}$ with
$s_i\in R\setminus\mathfrak n$; localize $R$ and $S$ at the product $s=\prod_i s_i$, so all
lifts lie in $R_s$. The resulting monic $f(T)\in R_s[T]$ has $f(x)\in\mathfrak mS_s$, since its
residue in $\kappa(\mathfrak m)$ is $\bar f(\bar x)=0$. The maximal ideal $\mathfrak mS_s$ and
its localization of $S$ still give the original $S_{\mathfrak m}$. Dependencies:
lem-weil-pbc-zariski-lemma.

3. Work over the localized $R_s$ and rename it $R$. Adjoin roots of $f$ successively to $K$; at
most $d$ finite algebraic extensions give a finite splitting field $K''/K$. Let $R'$ be the
integral closure of $R$ in $K''$. The Nagata property of $R$ [lem-weil-pbc-nagata-localization]
makes $R'$ a finite $R$-module by the N-2 clause of [def-weil-pbc-nagata-ring] and
[def-weil-pbc-japanese-domain]; it is a normal domain with fraction field $K''$ by
[lem-weil-pbc-integral-closure-finite-extension-normal], and Nagata by
[lem-weil-pbc-finite-over-nagata-nagata]. Every root of the monic polynomial $f$ is integral
over $R$, so lies in $R'$ [def-weil-pbc-integral-closure]. Put $S'=R'[x]\subset K''$. The same
finitely many $R$-module generators of $R'$ generate $S'$ as an $S$-module, so $S\subseteq S'$
is finite [def-weil-finitely-generated-module], hence integral by
[lem-weil-pbc-finite-algebra-is-integral]. Every maximal ideal $\mathfrak m$ of $S$ has a prime
ideal of $S'$ above it by [lem-weil-pbc-integral-injective-lying-over], and that prime is
maximal by [lem-weil-pbc-integral-prime-over-maximal-maximal]. Dependencies:
lem-weil-pbc-nagata-localization, def-weil-pbc-nagata-ring, def-weil-pbc-japanese-domain,
lem-weil-pbc-integral-closure-finite-extension-normal, lem-weil-pbc-finite-over-nagata-nagata,
def-weil-pbc-integral-closure, def-weil-finitely-generated-module,
lem-weil-pbc-finite-algebra-is-integral, lem-weil-pbc-integral-injective-lying-over,
lem-weil-pbc-integral-prime-over-maximal-maximal.

4. We claim that every local ring $S'_{\mathfrak m'}$ at a maximal ideal over $\mathfrak m$ is
N-1. Since $f(x)\in\mathfrak m'$, the factorization $f(T)=\prod_{i=1}^d(T-r_i)$ with $r_i\in R'$
gives $x-r_i\in\mathfrak m'$ for some $i$. Replace the generator $x$ by $y=x-r_i$; then
$S'=R'[y]$ and $y\in\mathfrak m'$. Rename $(R',S',y,\mathfrak m')$ as $(R,S,x,\mathfrak m)$ for
this local calculation. Thus the local calculation assumes a normal Nagata domain $R$, $0\ne
x\in\operatorname{Frac}(R)$, $S=R[x]$, and a maximal ideal $\mathfrak m$ containing $x$. If the
new $x=0$, then $S=R$ is normal and the local ring is N-1 immediately; otherwise continue.
Dependencies: def-weil-pbc-normal-ring, def-weil-pbc-nagata-ring, def-weil-pbc-japanese-domain.

5. Let $I=\ker(R[T]\to S)$, where $T\mapsto x$. We show by induction on degree that $I$ is
generated by the linear polynomials $cT-d$ with $c,d\in R$ and $cx=d$ in $K$. The degree-zero
case is zero because $R\hookrightarrow K$ is injective. If $g(T)=c_dT^d+\cdots+c_0\in I$ with
$d>0$, [lem-weil-pbc-leading-coefficient-times-root-integral] says $c_dx$ is integral over $R$;
normality [def-weil-pbc-normal-ring] gives $d_0:=c_dx\in R$. Then $c_dT-d_0\in I$, and
$g-(c_dT-d_0)T^{d-1}$ is in $I$ with degree below $d$. Hence $S/xS\cong R[T]/(I,T)\cong R/J$
with $J=\{d_0\in R: d_0=cx\text{ for some }c\in R\}=R\cap xR$. This identifies the quotient map
$R\to S/xS$ and its kernel explicitly. Dependencies:
lem-weil-pbc-leading-coefficient-times-root-integral, def-weil-pbc-normal-ring.

6. Apply [lem-weil-pbc-normal-domain-fractional-principal-quotient-ass] to the nonzero $x$:
$R/J$ has no embedded associated primes, and each associated prime $\mathfrak p$ has height one.
Under the surjection $S\to S/xS\cong R/J$, the annihilator of a class pulls back from its
annihilator in $R/J$; thus the associated primes of $S/xS$ are the inverse images $\mathfrak q$
of those $\mathfrak p$, each minimal over $xS$. Localization at $\mathfrak m$ keeps only
$\mathfrak q\subseteq\mathfrak m$ and preserves this property, so $S_{\mathfrak m}/xS_{\mathfrak
m}$ has no embedded primes. For one such $\mathfrak q$, put $\mathfrak p=R\cap\mathfrak q$. The
Noetherian normal local domain $R_{\mathfrak p}$ has dimension one, hence is a discrete
valuation ring by [lemma-proper-smooth-model--1]. Since $x\in\mathfrak qS_{\mathfrak q}$, $x$ cannot
have negative valuation in $R_{\mathfrak p}$: otherwise $x^{-1}\in\mathfrak pR_{\mathfrak
p}\subseteq\mathfrak qS_{\mathfrak q}$, contradicting $1=xx^{-1}\in\mathfrak qS_{\mathfrak q}$.
Therefore $x\in R_{\mathfrak p}$, so $S\otimes_RR_{\mathfrak p}=R_{\mathfrak p}[x]=R_{\mathfrak
p}$. The prime $\mathfrak q$ extends to a prime of this local ring containing $\mathfrak
pR_{\mathfrak p}$, hence exactly its maximal ideal $\mathfrak pR_{\mathfrak p}$; localizing
gives $S_{\mathfrak q}=R_{\mathfrak p}$, a regular local ring. These are conditions (2) and
(3)(a) of [lem-weil-pbc-analytic-unramified-principal-criterion]. Dependencies:
lem-weil-pbc-normal-domain-fractional-principal-quotient-ass, lemma-proper-smooth-model--1,
lem-weil-pbc-analytic-unramified-principal-criterion.

7. For the same associated prime $\mathfrak q\subseteq\mathfrak m$, the quotient $S/\mathfrak q$
is $R/\mathfrak p$: the map $R\to S/\mathfrak q$ is surjective because $x\in\mathfrak q$, and
its kernel is $\mathfrak p=R\cap\mathfrak q$. Thus $(S/\mathfrak q)_{\mathfrak
m}\cong(R/\mathfrak p)_{\mathfrak n}$, where $\mathfrak n=R\cap\mathfrak m$. The quotient
$R/\mathfrak p$ is Nagata by [lem-weil-pbc-finite-over-nagata-nagata], and its local ring is
Nagata by [lem-weil-pbc-nagata-localization]. It is a Noetherian local domain, so its completion
is reduced by [lem-weil-pbc-local-nagata-domain-analytically-unramified]. This is condition
(3)(b) of [lem-weil-pbc-analytic-unramified-principal-criterion]. That criterion, with $x\ne0$
and $x\in\mathfrak m$, shows $S_{\mathfrak m}$ analytically unramified;
[lem-weil-pbc-analytically-unramified-n1] makes it N-1. This completes the local calculation for
each $S'_{\mathfrak m'}$ above the original $\mathfrak m$. Dependencies:
lem-weil-pbc-finite-over-nagata-nagata, lem-weil-pbc-nagata-localization,
lem-weil-pbc-local-nagata-domain-analytically-unramified,
lem-weil-pbc-analytic-unramified-principal-criterion, lem-weil-pbc-analytically-unramified-n1.

8. Return to the finite extension $S\subseteq S'$ of Step 3 and the original maximal ideal
$\mathfrak m\subset S$. The domain $B=(S\setminus\mathfrak m)^{-1}S'$ is finite over
$S_{\mathfrak m}$, hence Noetherian [lem-weil-pbc-finite-algebra-noetherian] and integral over
$S_{\mathfrak m}$ by [lem-weil-pbc-finite-algebra-is-integral]. Every maximal ideal of $B$
contracts to the sole maximal ideal of $S_{\mathfrak m}$ by
[lem-weil-pbc-integral-maximal-contracts-maximal]; its contraction to $S'$ is a prime over
$\mathfrak m$, hence maximal by [lem-weil-pbc-integral-prime-over-maximal-maximal]. Thus its
localization is one of the $S'_{\mathfrak m'}$, N-1 by Steps 4-7. Also $B_a$ is a localization
of $S'_a=R'_a$, normal by [lem-weil-pbc-localization-normal-domain], because the original
$x=b/a$. Apply [lem-weil-pbc-n1-local-characterization] to $B$: it is N-1. Apply
[lem-weil-pbc-n1-descends-finite-domain-extension] to the finite extension $S_{\mathfrak
m}\subseteq B$: $S_{\mathfrak m}$ is N-1. As the original $\mathfrak m$ was arbitrary, Step 1
and [lem-weil-pbc-n1-local-characterization] show $S$ is N-1. Dependencies:
lem-weil-pbc-finite-algebra-noetherian, lem-weil-pbc-finite-algebra-is-integral,
lem-weil-pbc-integral-maximal-contracts-maximal,
lem-weil-pbc-integral-prime-over-maximal-maximal, lem-weil-pbc-localization-normal-domain,
lem-weil-pbc-n1-local-characterization, lem-weil-pbc-n1-descends-finite-domain-extension. -/
theorem isN1_adjoin_singleton_of_isNagataRing (R : Type u) (K : Type v)
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] (hR : IsNagataRing R) (x : K) :
    IsN1 (Algebra.adjoin R ({x} : Set K)) K := by
  let : IsNoetherianRing R := hR.1
  let S := Algebra.adjoin R ({x} : Set K)
  let : Algebra.FiniteType R S := Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton x)
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  apply isN1_of_local_characterization S K (adjoin_singleton_normal_away R K x)
  intro m hm
  obtain ⟨B, hComm, hDomain, hAlg, hNoeth, hInjective, hFinite, hAway, hMax⟩ :=
    exists_finite_cover_adjoin_singleton_atPrime R K hR x m
      (fun R' K' _ _ _ _ _ _ _ hR' y _ q _ hy ↦
        isAnalyticallyUnramified_adjoin_singleton_atPrime_of_mem R' K' hR' y q hy)
  let := hComm
  let := hDomain
  let := hAlg
  let := hNoeth
  let := hFinite
  have hB : IsN1 B (FractionRing B) :=
    isN1_of_local_characterization B (FractionRing B) hAway
      (fun q _ ↦ isN1_of_isAnalyticallyUnramified
        (Localization.AtPrime q) (FractionRing (Localization.AtPrime q)) (hMax q))
  exact isN1_of_finite_domain_extension (Localization.AtPrime m) B
    (FractionRing (Localization.AtPrime m)) (FractionRing B) hInjective hB
