/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.RingTheory.CohenRing
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic
import WeilConjectures.RingTheory.CompleteLocalDomainResidueParameterMap
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.FiniteOverCompleteRing
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.AdicCompletion.Topology

/-!
# Complete local domains finite over regular subrings

Source: Stacks Project, Algebra, Lemma Tag 032D and Definition Tag 0327
(blueprint: lem-weil-pbc-complete-local-domain-finite-over-regular).
-/

@[expose] public section

universe u

set_option autoImplicit false

namespace IsLocalRing

/-- A Noetherian complete local domain is finite over a regular complete power series subring.
Source: Stacks Project, Algebra, Lemma Tag 032D; Cohen rings are Definition Tag 0327.
(blueprint: lem-weil-pbc-complete-local-domain-finite-over-regular)

Proof outline:

1. (Coefficient ring; the two cases.) By [lem-weil-pbc-cohen-coefficient-ring-exists] (R is
$\mathfrak m$-adically complete [def-weil-pbc-adically-complete-ring]) choose a coefficient ring
$\Lambda\subseteq R$: $\Lambda$ is local with maximal ideal $\Lambda\cap\mathfrak m$ and
$(\Lambda\cap\mathfrak m)$-adically complete, $\Lambda/(\Lambda\cap\mathfrak m)\to R/\mathfrak m$
is an isomorphism, and $\Lambda\cap\mathfrak m=p\Lambda$ with $p\ge0$ the characteristic of
$R/\mathfrak m$. Case I: $p=0$, or $p>0$ and $p\cdot1=0$ in $R$. Then $\Lambda\cap\mathfrak
m=p\Lambda=0$, so the local ring $\Lambda$ has maximal ideal $0$ and is a field $k$, mapping
isomorphically onto $R/\mathfrak m$. Case II: $p>0$ and $p\cdot1\ne0$ in $R$. As $\Lambda\subseteq
R$ and $R$ is a domain, $\Lambda$ is a domain and $p\ne0$ in $\Lambda$; its maximal ideal is
$p\Lambda$, and $\bigcap_np^n\Lambda=0$ because $\Lambda$ is $p\Lambda$-adically complete (the
canonical map to $\varprojlim\Lambda/p^n\Lambda$ is injective). For $0\ne a\in\Lambda$ let $n\ge0$
be largest with $a\in p^n\Lambda$, $a=p^nu$; then $u\notin p\Lambda$, so $u$ is a unit. Hence
every nonzero ideal of $\Lambda$ equals $p^n\Lambda$ for the least $n$ occurring among the orders
of its elements: $\Lambda$ is a local principal ideal domain, not a field ($p$ is a nonzero
non-unit), complete with respect to its maximal ideal $p\Lambda$, i.e. a Cohen ring (Definition
0327), with $\Lambda/p\Lambda\cong R/\mathfrak m$.

2. (Case I: parameters.) Let $\Lambda=k$. By [lem-weil-pbc-noetherian-local-system-of-parameters]
($R$ is a Noetherian local ring [def-weil-pbc-noetherian-ring]) $d=\dim R$ is finite and there are
$x_1,\ldots,x_d\in\mathfrak m$ and $N\ge1$ with $\mathfrak m^N\subseteq
I=(x_1,\ldots,x_d)\subseteq\mathfrak m$. Since $I\subseteq\mathfrak m$ and $\mathfrak m^N\subseteq
I$, [lem-weil-pbc-change-ideal-completion] shows that $R$ is $I$-adically complete. Put
$R_0=k[[X_1,\ldots,X_d]]$ [def-weil-pbc-multivariate-power-series] and $I_0=(X_1,\ldots,X_d)$. By
[lem-weil-pbc-power-series-field-cohen-regular-complete], $R_0$ is a Noetherian local domain with
maximal ideal $\mathfrak m_0=I_0$, $k\to R_0/\mathfrak m_0$ is an isomorphism, $R_0$ is $\mathfrak
m_0$-adically complete, and $R_0$ is a regular local ring of dimension $d=\dim R$.

3. (Case II: parameters.) Let $\Lambda$ be a Cohen ring, $p>0$. Then $p\in
p\Lambda=\Lambda\cap\mathfrak m\subseteq\mathfrak m$ and $p\ne0$ in $R$; as $R$ is a domain, $p$
is a nonzerodivisor of $R$. By [lem-weil-pbc-noetherian-local-system-of-parameters] $\dim R$ is
finite, and by [lem-weil-pbc-dimension-quotient-nonzerodivisor] $\dim(R/pR)+1=\dim R$; put
$d=\dim(R/pR)$, so $\dim R=d+1$. The ring $R/pR$ is a Noetherian [def-weil-pbc-noetherian-ring]
local ring (its ideals are images of ideals of $R$) with maximal ideal $\mathfrak m/pR$, so
[lem-weil-pbc-noetherian-local-system-of-parameters] gives $\bar x_1,\ldots,\bar x_d\in\mathfrak
m/pR$ and $N\ge1$ with $(\mathfrak m/pR)^N\subseteq(\bar x_1,\ldots,\bar x_d)$. Lift them to
$x_1,\ldots,x_d\in\mathfrak m$; then $\mathfrak
m^N\subseteq(x_1,\ldots,x_d)+pR=I:=(p,x_1,\ldots,x_d)\subseteq\mathfrak m$, and by
[lem-weil-pbc-change-ideal-completion] $R$ is $I$-adically complete. Put
$R_0=\Lambda[[X_1,\ldots,X_d]]$ [def-weil-pbc-multivariate-power-series] and
$I_0=(p,X_1,\ldots,X_d)$. By [lem-weil-pbc-power-series-field-cohen-regular-complete], $R_0$ is a
Noetherian local domain with maximal ideal $\mathfrak m_0=I_0$, $\Lambda/p\Lambda\to R_0/\mathfrak
m_0$ is an isomorphism, $R_0$ is $\mathfrak m_0$-adically complete, and $R_0$ is a regular local
ring of dimension $d+1=\dim R$.

4. (The map $R_0\to R$.) In both cases let $f_1,\ldots,f_n$ be the listed generators of $I$
($x_1,\ldots,x_d$ in Case I; $p,x_1,\ldots,x_d$ in Case II). By
[lem-weil-pbc-power-series-onto-completion] there is a ring homomorphism
$\Phi:R[[Y_1,\ldots,Y_n]]\to R^\wedge=\varprojlim_mR/I^m$ [def-weil-pbc-adic-completion] with
$\Phi(Y_j)=(f_j\bmod I^m)_m$ and $\Phi(r)=(r\bmod I^m)_m$ for $r\in R$; the canonical map
$\iota:R\to R^\wedge$ is a ring isomorphism because $R$ is $I$-adically complete
[def-weil-pbc-adically-complete-ring]. Let $\varphi:R_0\to R$ be the composite of the
coefficientwise inclusion $\Lambda[[X_1,\ldots,X_d]]\to R[[X_1,\ldots,X_d]]$ (a ring map, since
sums and Cauchy products of power series [def-weil-pbc-multivariate-power-series] are computed
coefficientwise with the ring operations of $\Lambda\subseteq R$), the ring map
$R[[X_1,\ldots,X_d]]\to R[[Y_1,\ldots,Y_n]]$ renaming $X_i$ to the variable $Y_j$ with $f_j=x_i$,
then $\Phi$ and $\iota^{-1}$. Then $\varphi$ is a ring homomorphism, $\varphi|_\Lambda$ is the
inclusion $\Lambda\subseteq R$ (so $\varphi(p)=p$), and $\varphi(X_i)=x_i$. Hence the ideal of $R$
generated by $\varphi(I_0)$ is $I$, and $I_0^mR=I^m$ for all $m\ge1$ ($R$ viewed as an
$R_0$-module via $\varphi$).

5. ($R/I_0R$ is finite over $R_0/I_0$.) By [lem-weil-pbc-noetherian-local-quotient-artinian-local]
(with $C=R$, $K=I$, $\mathfrak m^N\subseteq I\subseteq\mathfrak m$) the ring $B=R/I$ is an
Artinian local ring with maximal ideal $\mathfrak m/I$, which is therefore its Jacobson radical,
and $B/J(B)=R/\mathfrak m$. Since $\varphi(\mathfrak m_0)\subseteq I\subseteq\mathfrak m$ (step 4,
$\mathfrak m_0=I_0$), the $R_0$-module structure of $R/\mathfrak m$ factors through $R_0/\mathfrak
m_0\to R/\mathfrak m$. This map is an isomorphism: precomposed with the isomorphism
$\Lambda/(\Lambda\cap\mathfrak m)\to R_0/\mathfrak m_0$ of
[lem-weil-pbc-power-series-field-cohen-regular-complete] (clause (2), $\mathfrak
m_\Lambda=\Lambda\cap\mathfrak m$) it is the map $\Lambda/(\Lambda\cap\mathfrak m)\to R/\mathfrak
m$ induced by the inclusion, an isomorphism by [lem-weil-pbc-cohen-coefficient-ring-exists] (2).
So $R/\mathfrak m$ is generated by $1$ as an $R_0$-module, and
[lem-weil-pbc-artinian-finite-over-residue-finite] (with $A=R_0$ acting via $\varphi$, $B=R/I$)
shows that $R/I$ is a finitely generated $R_0$-module. As $R/I_0R=R/I$ (step 4) and $I_0$ acts by
$0$ on it, $R/I_0R$ is a finitely generated $R_0/I_0$-module.

6. ($R$ is finite over $R_0$.) Apply [lem-weil-pbc-finite-over-complete-ring] to $A=R_0$, the
ideal $I_0$ and the $R_0$-module $M=R$ (via $\varphi$): (1) $R_0$ is $I_0$-adically complete
([lem-weil-pbc-power-series-field-cohen-regular-complete] (3), $I_0=\mathfrak m_0$); (2)
$\bigcap_mI_0^mR=\bigcap_mI^m=0$, since $I_0^mR=I^m$ (step 4) and $R$ is $I$-adically complete
[def-weil-pbc-adically-complete-ring], so the kernel $\bigcap_mI^m$ of $R\to\varprojlim R/I^m$ is
$0$; (3) $R/I_0R$ is finitely generated over $R_0/I_0$ (step 5). Hence $R$ is a finitely generated
$R_0$-module via $\varphi$.

7. ($\varphi$ is injective.) Let $P=\ker\varphi$; it is a prime ideal, since
$R_0/P\cong\varphi(R_0)$ is a subring of the domain $R$. Suppose $P\ne0$. By step 6, $R$ is a
finitely generated module over $R_0/P$, hence integral over $R_0/P$
[lem-weil-pbc-finite-algebra-is-integral], so $\dim R\le\dim(R_0/P)$ by
[proposition-proper-direct-image-constructible-complexes]. As $R_0$ is a domain
([lem-weil-pbc-power-series-field-cohen-regular-complete] (1)), $(0)$ is a prime with
$(0)\subsetneq P$; a chain $\mathfrak q_0/P\subsetneq\cdots\subsetneq\mathfrak q_\ell/P$ of primes
of $R_0/P$ gives the chain $(0)\subsetneq\mathfrak q_0\subsetneq\cdots\subsetneq\mathfrak q_\ell$
in $R_0$ (as $P\subseteq\mathfrak q_0$), so $\dim R_0\ge\dim(R_0/P)+1\ge\dim R+1$. But $\dim
R_0=\dim R<\infty$ (steps 2 and 3), a contradiction. Hence $P=0$ and $\varphi$ identifies $R_0$
with the subring $\varphi(R_0)\subseteq R$.

8. (Conclusion.) Identify $R_0$ with $\varphi(R_0)\subseteq R$ (step 7). Then $\mathfrak m\cap
R_0=\mathfrak m_0$: $\mathfrak m_0\subseteq\mathfrak m$ by step 5, and $\mathfrak m\cap R_0$ is a
proper ideal of $R_0$ containing the maximal ideal $\mathfrak m_0$. So (1) $R_0$ is a regular
local ring with maximal ideal $\mathfrak m_0=\mathfrak m\cap R_0$ and is $\mathfrak m_0$-adically
complete ([lem-weil-pbc-power-series-field-cohen-regular-complete] (3), (4)); (2) $R$ is a
finitely generated $R_0$-module (step 6) and $R_0/\mathfrak m_0\to R/\mathfrak m$ is an
isomorphism (step 5); (3) $R_0$ is $k[[X_1,\ldots,X_d]]$ with $k$ a field (Case I) or
$\Lambda[[X_1,\ldots,X_d]]$ with $\Lambda$ a Cohen ring (Case II), by step 1.
-/
theorem complete_local_domain_finite_over_regular
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] :
    ∃ (R₀ : Subring R), ∃ hreg : IsRegularLocalRing R₀,
      let _ := hreg.toIsLocalRing
      IsAdicComplete (IsLocalRing.maximalIdeal R₀) R₀ ∧
      Module.Finite R₀ R ∧
      IsLocalRing.maximalIdeal R₀ =
        Ideal.comap R₀.subtype (IsLocalRing.maximalIdeal R) ∧
    ∃ e : (R₀ ⧸ IsLocalRing.maximalIdeal R₀) ≃+*
          (R ⧸ IsLocalRing.maximalIdeal R),
        (∀ x : R₀,
          e (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R₀) x) =
            Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (R₀.subtype x)) ∧
      ((∃ (k : Type u), ∃ h : Field k, ∃ d : ℕ,
          let _ := h
          Nonempty (R₀ ≃+* MvPowerSeries (Fin d) k)) ∨
      (∃ (Λ : Type u), ∃ h : CommRing Λ, ∃ d : ℕ,
          let _ := h
          ∃ p : ℕ, IsCohenRing p Λ ∧
          Nonempty (R₀ ≃+* MvPowerSeries (Fin d) Λ))) := by
  obtain ⟨n, Λ, hΛring, hlocal, halg, hΛ, hdim, hsep, hquot, hres⟩ :=
    complete_local_domain_residue_parameter_map R
  let := hΛring
  let A := MvPowerSeries (Fin n) Λ
  let : IsLocalRing A := hlocal
  let : Algebra A R := halg
  let : IsHausdorff (maximalIdeal A) R := hsep
  let : Module.Finite (A ⧸ maximalIdeal A)
      (R ⧸ (maximalIdeal A • ⊤ : Submodule A R)) := hquot
  have hproperties := MvPowerSeries.power_series_field_cohen_regular_complete n hΛ
  have hregular : IsRegularLocalRing A := by
    rcases hproperties with ⟨_, _, _, _, _, e, _, _, hreg, _⟩ |
      ⟨_, _, _, _, _, _, e, _, _, hreg, _⟩
    · exact hreg
    · exact hreg
  have hcomplete : IsAdicComplete (maximalIdeal A) A := by
    rcases hproperties with ⟨_, _, _, _, _, e, _, hcomp, _, _⟩ |
      ⟨_, _, _, _, _, _, e, _, hcomp, _, _⟩
    · exact hcomp
    · exact hcomp
  let : IsRegularLocalRing A := hregular
  let : IsAdicComplete (maximalIdeal A) A := hcomplete
  let : Module.Finite A R :=
    (Module.finite_and_span_eq_top_of_adicComplete (maximalIdeal A) R).1
  let f := algebraMap A R
  have hfinite : f.Finite := by
    exact (RingHom.finite_algebraMap).mpr inferInstance
  have hrange : f.range.subtype.Finite :=
    RingHom.Finite.of_comp_finite (f := f.rangeRestrict) (by
      convert hfinite using 1
      ext x
      rfl)
  have hbound : ringKrullDim R ≤ ringKrullDim f.range := by
    let : Module.Finite f.range R := hrange
    let : Algebra.IsIntegral f.range R := inferInstance
    exact Order.krullDim_le_of_strictMono (PrimeSpectrum.comap f.range.subtype)
      (fun p q hpq ↦ Ideal.IsIntegral.under_lt_under hpq)
  have hdomain : IsDomain A := by
    rcases hproperties with ⟨_, _, hdom, _, _⟩ | ⟨_, _, _, hdom, _, _⟩
    · exact hdom
    · exact hdom
  let : IsDomain A := hdomain
  have hinj : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro x hx
    by_contra hne
    have hsucc := ringKrullDim_succ_le_of_surjective f.rangeRestrict
      f.rangeRestrict_surjective (mem_nonZeroDivisors_iff_ne_zero.mpr hne)
      (show f.rangeRestrict x = 0 from Subtype.ext hx)
    have hbad : ringKrullDim R + 1 ≤ ringKrullDim R := by
      calc
        ringKrullDim R + 1 ≤ ringKrullDim f.range + 1 := add_le_add hbound le_rfl
        _ ≤ ringKrullDim A := hsucc
        _ = ringKrullDim R := hdim
    have hnatdim : ∃ d : ℕ, ringKrullDim R = (d : WithBot ℕ∞) := by
      rcases hproperties with ⟨_, _, _, _, _, _, _, _, _, hd⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, hd⟩
      · exact ⟨n, hdim.symm.trans hd⟩
      · exact ⟨n + 1, hdim.symm.trans hd⟩
    obtain ⟨d, hd⟩ := hnatdim
    rw [hd] at hbad
    exact (lt_irrefl (d : WithBot ℕ∞))
      (ENat.WithBot.add_one_le_natCast_iff.mp hbad)
  let e : A ≃+* f.range :=
    RingEquiv.ofBijective f.rangeRestrict
      ⟨fun x y h ↦ hinj (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  let : IsRegularLocalRing f.range := IsRegularLocalRing.of_ringEquiv e
  have hcompRange : IsAdicComplete (maximalIdeal f.range) f.range := by
    have hmap : (maximalIdeal A).map e = maximalIdeal f.range :=
      map_ringEquiv_maximalIdeal e
    rw [← hmap]
    exact (IsAdicComplete.congr_ringEquiv (maximalIdeal A) e).mpr hcomplete
  have hmax : maximalIdeal f.range = (maximalIdeal R).comap f.range.subtype := by
    let : Module.Finite f.range R := hrange
    let : Algebra.IsIntegral f.range R := inferInstance
    exact (eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := f.range)
        (maximalIdeal R))).symm
  let q := Ideal.quotientMap (maximalIdeal R) f.range.subtype hmax.le
  have hq : Function.Bijective q := by
    constructor
    · intro x y hxy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      apply Ideal.Quotient.eq.mpr
      rw [hmax]
      change (a - b : f.range).val ∈ maximalIdeal R
      exact Ideal.Quotient.eq.mp hxy
    · intro y
      obtain ⟨a, ha⟩ := hres y
      exact ⟨Ideal.Quotient.mk _ (f.rangeRestrict a), ha⟩
  let eres := RingEquiv.ofBijective q hq
  refine ⟨f.range, inferInstance, hcompRange, hrange, hmax, eres, ?_, ?_⟩
  · intro x
    rfl
  · rcases hΛ with hfield | ⟨p, hp⟩
    · exact Or.inl ⟨Λ, hfield.toField, n, ⟨e.symm⟩⟩
    · exact Or.inr ⟨Λ, hΛring, n, p, hp, ⟨e.symm⟩⟩


end IsLocalRing
