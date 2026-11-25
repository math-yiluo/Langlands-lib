/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.EssentiallySmooth
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.LocalRing.Defs
import WeilConjectures.RingTheory.PopescuFlatCoordinates
import WeilConjectures.RingTheory.PopescuEtaleQuotientMap
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Solving modulo a prime power through an essentially smooth Artinian algebra

Source: Stacks Project, Smoothing Ring Maps, Lemma 07FH (lemma-solution-modulo)
(blueprint: lem-weil-pbc-popescu-solution-modulo).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

private theorem local_artinian_prime_pow
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (n : ℕ) (hn : 1 ≤ n) :
    IsLocalRing (R ⧸ IsLocalRing.maximalIdeal R ^ n) ∧
      IsArtinianRing (R ⧸ IsLocalRing.maximalIdeal R ^ n) := by
  have hn0 : n ≠ 0 := Nat.ne_zero_of_lt hn
  have hproper : IsLocalRing.maximalIdeal R ^ n ≠ ⊤ := by
    exact ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      (Ideal.pow_le_self hn0)
  have : Nontrivial (R ⧸ IsLocalRing.maximalIdeal R ^ n) :=
    Ideal.Quotient.nontrivial_iff.mpr hproper
  refine ⟨IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective, ?_⟩
  apply IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing
  rw [← Ideal.radical_minimalPrimes, Ideal.radical_pow _ hn0,
    Ideal.IsPrime.radical (IsLocalRing.maximalIdeal.isMaximal R).isPrime,
    Ideal.minimalPrimes_eq_subsingleton_self]
  exact Set.mem_singleton _


/-- A finite subset of a prime-power quotient of a geometrically regular algebra lies in an
Artinian factorization of a polynomial localization, essentially smooth on the first leg
and flat on the second. Source: Stacks Project, Smoothing Ring Maps, Lemma 07FH
(blueprint: lem-weil-pbc-popescu-solution-modulo).

Proof, following the node's split of Stacks 07FH (with its corrected choice of subalgebra):
1. *Setup.* $\Lambda_{\mathfrak q}$ is a local ring with maximal ideal $\mathfrak
q\Lambda_{\mathfrak q}$ and residue field $K=\kappa(\mathfrak q)$
[def-weil-pbc-localization-at-prime], Noetherian as a localization of the Noetherian ring
$\Lambda$ [lem-weil-pbc-localization-noetherian], and $\mathfrak q\Lambda_{\mathfrak
q}\cap\Lambda=\mathfrak q$. It is geometrically regular over $k$
[theorem-finite-etale-covers-proper-henselian--2]: for a finite purely inseparable $k'/k$,
$k'\otimes_k\Lambda_{\mathfrak q}$ is the localization of the regular ring $k'\otimes_k\Lambda$ at
the image of $\Lambda\setminus\mathfrak q$ (tensor products commute with localization), hence
regular [theorem-finite-etale-covers-proper-henselian--2]. Set $\bar\Lambda=\Lambda_{\mathfrak
q}/\mathfrak q^n\Lambda_{\mathfrak q}$ (Stacks' notation); it is an Artinian local $k$-algebra with
maximal ideal $\bar{\mathfrak m}=\mathfrak q\bar\Lambda$, $\bar{\mathfrak m}^n=0$, and residue field
$K$ [lem-weil-pbc-noetherian-local-quotient-artinian-local].

2. *$\dim_KH_1(L_{K/k})<\infty$.* By [lem-weil-pbc-geometrically-regular-h1-injective] applied to
the Noetherian local $k$-algebra $\Lambda_{\mathfrak q}$, geometrically regular over $k$ (step 1),
the canonical map $H_1(L_{K/k})\to\mathfrak q\Lambda_{\mathfrak q}/\mathfrak q^2\Lambda_{\mathfrak
q}$ [def-weil-pbc-smooth-ring-map] is injective. The target is a finite dimensional $K$-vector
space, since the ideal $\mathfrak q\Lambda_{\mathfrak q}$ of the Noetherian ring
$\Lambda_{\mathfrak q}$ is finitely generated. Hence $H_1(L_{K/k})$ is finite dimensional.

3. *A first subring $A_0\supseteq E$.* By [lem-weil-pbc-popescu-artinian-flat-subalgebras] (Stacks
07FG) applied to the Artinian local $k$-algebra $\bar\Lambda$ with residue field $K$ (steps 1, 2),
$\bar\Lambda$ is a filtered colimit of Artinian local $k$-algebras $A_i$, essentially of finite
type over $k$, with flat maps $A_i\to\bar\Lambda$ and $\mathfrak m_{A_i}\bar\Lambda=\bar{\mathfrak
m}$. Each $A_i\to\bar\Lambda$ maps $\mathfrak m_{A_i}$ into $\bar{\mathfrak m}$, so it is a flat
local homomorphism, hence faithfully flat [lem-weil-pbc-flat-local-hom-faithfully-flat] and
injective [lem-weil-pbc-faithfully-flat-ideal-contraction] ($I=0$); identify $A_i$ with its image,
a $k$-subalgebra of $\bar\Lambda$, flat over $A_i$ [def-weil-pbc-flat-ring-map]. Every element of
$\bar\Lambda$ lies in some $A_i$ and the system is filtered, so the finite set $E$ lies in one of
them, $A_0$. In the terminology of [lem-weil-pbc-popescu-solution-modulo-choose], $A_0$ is
admissible.

4. *The subring $A$ and the elements $\lambda$.* By [lem-weil-pbc-popescu-solution-modulo-choose]
applied to $A_0$ there are an admissible $A\subseteq\bar\Lambda$ with $E\subseteq A_0\subseteq A$,
residue field $F=A/\mathfrak m_A$ with $k\subseteq F\subseteq K$, elements
$\lambda_1,\dots,\lambda_t\in\Lambda$ whose images in $\bar\Lambda$ lie in $A$ and whose residues
$\bar\lambda_j\in F$ have differentials $\mathrm d\bar\lambda_1,\dots,\mathrm d\bar\lambda_t$
forming a basis of $\Omega_{F/k}$ [def-weil-pbc-kahler-differentials], and elements
$\lambda'_1,\dots,\lambda'_r\in\mathfrak q$ with images in $A$ which generate $\mathfrak
q\Lambda_{\mathfrak q}$. Since $A$ is essentially of finite type over $k$, so is its quotient
field $F$, which is therefore a finitely generated field extension of $k$ (generated by the images
of finitely many algebra generators). (Stacks picks the $\lambda_j$ for the subring of step 3
directly; as recorded in [lem-weil-pbc-popescu-solution-modulo-choose], that is not possible for
every such subring, which is why $A_0$ is enlarged.)

5. *Flatness of the first part.* Let $\varphi':k[y_1,\dots,y_t]\to\Lambda$
[def-weil-pbc-mv-polynomial-ring] send $y_j\mapsto\lambda_j$ and $\mathfrak
p'=(\varphi')^{-1}(\mathfrak q)$; since $\mathfrak q\Lambda_{\mathfrak q}\cap\Lambda=\mathfrak q$,
$\mathfrak p'$ is also the inverse image of the maximal ideal under
$k[y_1,\dots,y_t]\to\Lambda_{\mathfrak q}$. Apply
[lem-weil-pbc-geometrically-regular-over-field-flat] (Stacks 07E6) to the Noetherian local
$k$-algebra $\Lambda_{\mathfrak q}$, geometrically regular over $k$ (step 1), the finitely
generated subextension $k\subseteq F\subseteq K$ and this map (the image of $y_j$ in $K$ is
$\bar\lambda_j\in F$, and the $\mathrm d\bar\lambda_j$ form a basis of $\Omega_{F/k}$, step 4):
$P'=k[y_1,\dots,y_t]_{\mathfrak p'}\to\Lambda_{\mathfrak q}$ [def-weil-pbc-localization-at-prime]
is flat [def-weil-pbc-flat-ring-map] and $S:=\Lambda_{\mathfrak q}/\mathfrak p'\Lambda_{\mathfrak
q}$ is a regular local ring [def-weil-regular-scheme], with maximal ideal $\mathfrak qS$ and
residue field $K$.

6. *A regular system of parameters of $S$ from the $\lambda'_i$.* The images of
$\lambda'_1,\dots,\lambda'_r$ generate $\mathfrak q\Lambda_{\mathfrak q}$ (step 4), hence the
maximal ideal $\mathfrak qS$ of $S$, hence span the $K$-vector space $\mathfrak qS/\mathfrak
q^2S$. Choose among them $e$ elements whose images form a basis of $\mathfrak qS/\mathfrak q^2S$
and call them $\lambda_{t+1},\dots,\lambda_m$ ($m=t+e$). By Nakayama
[lem-weil-pbc-nakayama-local-generators] their images generate $\mathfrak qS$, and no proper
subset does, so they form a minimal set of generators of the maximal ideal of the regular local
ring $S$, i.e. a regular system of parameters, and $e=\dim S$ [def-weil-regular-scheme]
[lem-weil-pbc-regular-local-generators-regular-sequence]. By
[lem-weil-pbc-regular-local-generators-regular-sequence] their images form a regular sequence in
$S$ [def-weil-pbc-regular-sequence], and $S/(\lambda_{t+1},\dots,\lambda_m)S=S/\mathfrak
qS=K\ne0$. Each $\lambda_{t+i}$ lies in $\mathfrak q$ and its image in $\bar\Lambda$ lies in $A$.

7. *The map $\varphi$ and $\mathfrak p\Lambda_{\mathfrak q}=\mathfrak q\Lambda_{\mathfrak q}$.*
Let $\varphi:k[y_1,\dots,y_m]\to\Lambda$, $y_j\mapsto\lambda_j$, extend $\varphi'$, $\mathfrak
p=\varphi^{-1}(\mathfrak q)$ and $P=k[y_1,\dots,y_m]_{\mathfrak p}$. Then $\mathfrak p\cap
k[y_1,\dots,y_t]=\mathfrak p'$ and $y_{t+1},\dots,y_m\in\mathfrak p$ (as
$\lambda_{t+i}\in\mathfrak q$). Since $\varphi(\mathfrak p)\subseteq\mathfrak q$, $\mathfrak
p\Lambda_{\mathfrak q}\subseteq\mathfrak q\Lambda_{\mathfrak q}$; conversely $\mathfrak
p\Lambda_{\mathfrak q}\supseteq\mathfrak p'\Lambda_{\mathfrak
q}+(\lambda_{t+1},\dots,\lambda_m)\Lambda_{\mathfrak q}$, which is all of $\mathfrak
q\Lambda_{\mathfrak q}$ because the images of $\lambda_{t+1},\dots,\lambda_m$ generate $\mathfrak
qS=\mathfrak q\Lambda_{\mathfrak q}/\mathfrak p'\Lambda_{\mathfrak q}$ (step 6). So $\mathfrak
q\Lambda_{\mathfrak q}=\mathfrak p\Lambda_{\mathfrak q}$, the first half of (1).

8. *The closed fibre $P/\mathfrak p'P$.* Elements of $k[y_1,\dots,y_t]\setminus\mathfrak p'$ are
not in $\mathfrak p$, so they are units of $P$; hence $P/\mathfrak p'P$ is the localization of
$\kappa(\mathfrak p')[y_{t+1},\dots,y_m]$ ($\kappa(\mathfrak p')$ the fraction field of
$k[y_1,\dots,y_t]/\mathfrak p'$) at the image $\bar{\mathfrak p}$ of $\mathfrak p$. As
$\bar{\mathfrak p}$ contains the maximal ideal $(y_{t+1},\dots,y_m)$ (step 7) and is proper, it
equals it. By [lem-weil-pbc-polynomial-ring-origin-regular-local] over the field $\kappa(\mathfrak
p')$, $P/\mathfrak p'P$ is a regular local ring of dimension $e=m-t$ whose maximal ideal is
generated by $y_{t+1},\dots,y_m$. $P'$, $P$ are Noetherian local rings (localizations
[lem-weil-pbc-localization-noetherian] of polynomial rings over a field
[lem-weil-pbc-finite-type-algebra-noetherian]), and $P'\to P$ (localization of the inclusion,
$\mathfrak p\cap k[y_1,\dots,y_t]=\mathfrak p'$) and $P\to\Lambda_{\mathfrak q}$ are local
homomorphisms, with $\mathfrak m_{P'}P=\mathfrak p'P$.

9. *$P\to\Lambda_{\mathfrak q}$ is flat.* The induced local homomorphism $P/\mathfrak p'P\to
S=\Lambda_{\mathfrak q}/\mathfrak p'\Lambda_{\mathfrak q}$ of Noetherian local rings sends the
regular system of parameters $y_{t+1},\dots,y_m$ of the regular local ring $P/\mathfrak p'P$ (step
8) to $\lambda_{t+1},\dots,\lambda_m$, a regular sequence in $S$ with nonzero quotient (step 6);
so it is flat by [lem-weil-pbc-flat-over-regular] (Algebra 07DY). Now apply
[lem-weil-pbc-criterion-flatness-fibre-noetherian] (Algebra 00MP) to $P'\to P\to\Lambda_{\mathfrak
q}$ and $M=\Lambda_{\mathfrak q}$: these are Noetherian local rings and local homomorphisms (steps
1, 8); $M$ is generated by $1$ and nonzero; $M/\mathfrak m_{P'}M=S$ is flat over $P/\mathfrak
m_{P'}P=P/\mathfrak p'P$ (just shown); $M$ is flat over $P'$ (step 5). Hence $\Lambda_{\mathfrak
q}$ is flat over $P$ [def-weil-pbc-flat-ring-map]. With step 7 this proves (1).

10. *The factorization through $A$.* Write $\bar P=P/\mathfrak p^nP$, an Artinian local ring with
maximal ideal $\mathfrak p\bar P$ and residue field $\kappa(\mathfrak p)$
[lem-weil-pbc-noetherian-local-quotient-artinian-local]. The images of $y_1,\dots,y_m$ in
$\bar\Lambda$ lie in $A$ (steps 4, 6), so $k[y_1,\dots,y_m]\to\bar\Lambda$ takes values in $A$. An
element $g\notin\mathfrak p$ maps to an element of $A$ outside $\bar{\mathfrak m}$, i.e. outside
$\mathfrak m_A=A\cap\bar{\mathfrak m}$, hence to a unit of the local ring $A$; by the universal
property of localization [def-weil-pbc-localization-at-prime] $k[y]\to A$ extends to $P\to A$,
which composed with $A\subseteq\bar\Lambda$ is $P\to\Lambda_{\mathfrak q}\to\bar\Lambda$. The
latter kills $\mathfrak p^nP$ (it maps into $\mathfrak q^n\bar\Lambda=0$) and
$A\subseteq\bar\Lambda$ is injective, so we get $\bar P\to A\to\bar\Lambda$, local homomorphisms
of local Artinian rings ($\mathfrak p$ maps into $\mathfrak m_A$). Put $D=A$. Then
$D\to\bar\Lambda$ is flat ($A$ admissible) and $E\subseteq A_0\subseteq D$, which is (3).

11. *$\bar P\to A$ is flat.* Since $\mathfrak q^n\Lambda_{\mathfrak q}=\mathfrak
p^n\Lambda_{\mathfrak q}$ (step 7), $\bar\Lambda=\Lambda_{\mathfrak q}\otimes_P\bar P$, which is
flat over $\bar P$ by base change of the flat $P$-module $\Lambda_{\mathfrak q}$ (step 9)
[lem-weil-pbc-flat-module-base-change]. The flat local homomorphism $A\to\bar\Lambda$ is
faithfully flat [lem-weil-pbc-flat-local-hom-faithfully-flat]. So the $A$-module $\bar\Lambda$ is
flat over $\bar P$ and faithfully flat over $A$, and $\bar P\to A$ is flat by
[lem-weil-pbc-flat-permanence] (Stacks cites Algebra 0584 (2) with $S=A$, $S'=\bar\Lambda$, $M=A$,
which is this instance).

12. *$\mathfrak m_A=\mathfrak pA$.* By step 7, $(\mathfrak pA)\bar\Lambda=\mathfrak
p\bar\Lambda=\mathfrak q\bar\Lambda=\bar{\mathfrak m}=\mathfrak m_A\bar\Lambda$. Since
$A\to\bar\Lambda$ is faithfully flat (step 11), [lem-weil-pbc-faithfully-flat-ideal-contraction]
gives $\mathfrak m_A\subseteq\mathfrak m_A\bar\Lambda\cap A=(\mathfrak pA)\bar\Lambda\cap
A=\mathfrak pA\subseteq\mathfrak m_A$. So the maximal ideal of $\bar P$ generates the maximal
ideal of $A$ (needed for the étaleness criterion below; Stacks leaves it implicit).

13. *$F/\kappa(\mathfrak p)$ is finite separable.* The local map $\bar P\to A$ induces
$\kappa(\mathfrak p)\to F$, and $F$ is finitely generated over $k$ (step 4), hence over
$\kappa(\mathfrak p)$. The universal derivation $F\to\Omega_{F/\kappa(\mathfrak p)}$ is a
$k$-derivation, so by the universal property [def-weil-pbc-kahler-differentials] there is an
$F$-linear map $\Omega_{F/k}\to\Omega_{F/\kappa(\mathfrak p)}$, $\mathrm df\mapsto\mathrm df$,
which is surjective (the $\mathrm df$ generate). It kills $\mathrm d\bar\lambda_j$ for $j\le t$,
since $\bar\lambda_j$ is the image of $y_j\in\kappa(\mathfrak p)$ and $\mathrm d$ vanishes on
$\kappa(\mathfrak p)$; these span $\Omega_{F/k}$ (step 4). Hence $\Omega_{F/\kappa(\mathfrak
p)}=0$, and by [lem-weil-pbc-fg-field-zero-differentials-separable] $F/\kappa(\mathfrak p)$ is
finite and separable algebraic [def-weil-pbc-separable-algebraic-extension].

14. *$\bar P\to A$ is finite and finitely presented.* $A$ is Artinian with Jacobson radical
$\mathfrak m_A$ and $A/\mathfrak m_A=F$ is a finite $\bar P$-module (finite over $\kappa(\mathfrak
p)$, step 13, and $\bar P\to\kappa(\mathfrak p)$ is surjective); so $A$ is a finite $\bar
P$-module [lem-weil-pbc-artinian-finite-over-residue-finite], in particular a $\bar P$-algebra of
finite type. $\bar P$ is Noetherian (a quotient of the Noetherian ring $P$), so $A$ is finitely
presented over $\bar P$ [lem-weil-pbc-finite-type-noetherian-finite-presentation].

15. *$\bar P\to D=A$ is étale, hence essentially smooth.* By
[lem-weil-pbc-local-flat-unramified-etale] (Algebra 00U6, local case) applied to the local
homomorphism $\bar P\to A$: finitely presented (step 14), flat (step 11), $\mathfrak m_{\bar
P}A=\mathfrak m_A$ (step 12), residue extension finite separable (step 13); so $\bar P\to A$ is
étale in the sense of Algebra 00U1, equivalently $\operatorname{Spec}A\to\operatorname{Spec}\bar
P$ is étale [lem-weil-pbc-etale-ring-map-iff-etale-affine]. By remark (a) of
[def-weil-pbc-essentially-smooth-ring-map] an étale ring map is essentially smooth. Together with
step 10 this is (2).
-/
theorem exists_essentiallySmooth_artinian_factorization_mod_prime_pow
    (k : Type u) (Λ : Type v) [Field k] [CommRing Λ] [Algebra k Λ]
    [IsNoetherianRing Λ] (p : ℕ) [CharP k p] (hp : 0 < p)
    (hreg : IsGeometricallyRegular k Λ) (q : Ideal Λ) [q.IsPrime]
    (n : ℕ) (hn : 1 ≤ n)
    (E : Finset (Localization.AtPrime q ⧸
      (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)) :
    ∃ (m : ℕ) (φ : MvPolynomial (Fin m) k →ₐ[k] Λ)
      (ψ : Localization.AtPrime (q.comap φ.toRingHom) →+* Localization.AtPrime q),
      ψ.comp (algebraMap (MvPolynomial (Fin m) k)
          (Localization.AtPrime (q.comap φ.toRingHom))) =
        (algebraMap Λ (Localization.AtPrime q)).comp φ.toRingHom ∧
      q.map (algebraMap Λ (Localization.AtPrime q)) =
        (q.comap φ.toRingHom).map
          ((algebraMap Λ (Localization.AtPrime q)).comp φ.toRingHom) ∧
      ψ.Flat ∧
      IsLocalRing (Localization.AtPrime (q.comap φ.toRingHom) ⧸
        ((q.comap φ.toRingHom).map (algebraMap (MvPolynomial (Fin m) k)
          (Localization.AtPrime (q.comap φ.toRingHom)))) ^ n) ∧
      IsArtinianRing (Localization.AtPrime (q.comap φ.toRingHom) ⧸
        ((q.comap φ.toRingHom).map (algebraMap (MvPolynomial (Fin m) k)
          (Localization.AtPrime (q.comap φ.toRingHom)))) ^ n) ∧
      IsLocalRing (Localization.AtPrime q ⧸
        (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) ∧
      IsArtinianRing (Localization.AtPrime q ⧸
        (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) ∧
      ∃ (D : Type (max u v)) (_ : CommRing D)
        (_ : Algebra (Localization.AtPrime (q.comap φ.toRingHom) ⧸
          ((q.comap φ.toRingHom).map (algebraMap (MvPolynomial (Fin m) k)
            (Localization.AtPrime (q.comap φ.toRingHom)))) ^ n) D)
        (g : D →+* Localization.AtPrime q ⧸
          (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n),
        IsLocalRing D ∧ IsArtinianRing D ∧
        IsLocalHom (algebraMap (Localization.AtPrime (q.comap φ.toRingHom) ⧸
          ((q.comap φ.toRingHom).map (algebraMap (MvPolynomial (Fin m) k)
            (Localization.AtPrime (q.comap φ.toRingHom)))) ^ n) D) ∧
        IsLocalHom g ∧
        EssentiallySmooth (Localization.AtPrime (q.comap φ.toRingHom) ⧸
          ((q.comap φ.toRingHom).map (algebraMap (MvPolynomial (Fin m) k)
            (Localization.AtPrime (q.comap φ.toRingHom)))) ^ n) D ∧
        g.Flat ∧
        (g.comp (algebraMap (Localization.AtPrime (q.comap φ.toRingHom) ⧸
          ((q.comap φ.toRingHom).map (algebraMap (MvPolynomial (Fin m) k)
            (Localization.AtPrime (q.comap φ.toRingHom)))) ^ n) D)).comp
          (Ideal.Quotient.mk ((q.comap φ.toRingHom).map (algebraMap (MvPolynomial (Fin m) k)
            (Localization.AtPrime (q.comap φ.toRingHom))) ^ n)) =
          (Ideal.Quotient.mk
            ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)).comp ψ ∧
        ∀ e ∈ E, e ∈ Set.range g := by
  obtain ⟨A, hlocal, hA, hAm, hE, m, φ, ψ, hψ, hideal, hflat, a, ha, hspan⟩ :=
    exists_popescu_flat_coordinates k Λ p hp hreg q n hn E
  let : IsLocalRing A := hlocal
  let P := Localization.AtPrime (q.comap φ.toRingHom)
  let I : Ideal P := (q.comap φ.toRingHom).map (algebraMap (MvPolynomial (Fin m) k) P)
  let B := Localization.AtPrime q ⧸ (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n
  let Q := P ⧸ I ^ n
  have hP : I = IsLocalRing.maximalIdeal P := Localization.AtPrime.map_eq_maximalIdeal
  have hQ : IsLocalRing Q ∧ IsArtinianRing Q := by
    dsimp [Q]
    rw [hP]
    exact local_artinian_prime_pow P n hn
  have hB : IsLocalRing B ∧ IsArtinianRing B := by
    dsimp [B]
    rw [Localization.AtPrime.map_eq_maximalIdeal]
    exact local_artinian_prime_pow (Localization.AtPrime q) n hn
  have : IsLocalRing Q := hQ.1
  have : IsArtinianRing Q := hQ.2
  have : IsLocalRing B := hB.1
  obtain ⟨f, hfLocal, hfEtale, hfcomm⟩ :=
    exists_etale_popescu_quotient_map k Λ q n hn A hA hAm m φ ψ hψ hideal hflat a ha hspan
  let : Algebra Q A := f.toAlgebra
  have : Etale Q A := hfEtale
  have : IsLocalHom f := hfLocal
  have : IsArtinianRing A := hA.1
  let D := ULift.{u} A
  let e : D ≃ₐ[Q] A := ULift.algEquiv
  have : IsLocalRing D := e.toRingEquiv.symm.isLocalRing
  have : IsArtinianRing D := e.toRingEquiv.symm.isArtinianRing
  have : Etale Q D := Etale.of_equiv e.symm
  let g : D →+* B := A.val.toRingHom.comp e.toRingHom
  have hvalLocal : IsLocalHom A.val.toRingHom := by
    apply (IsLocalRing.local_hom_TFAE A.val.toRingHom).out 5 1 |>.mp
    change (IsLocalRing.maximalIdeal B).comap A.val.toRingHom = _
    rw [← IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))
      Ideal.Quotient.mk_surjective, ← Localization.AtPrime.map_eq_maximalIdeal]
    exact hAm.symm
  have : IsLocalHom A.val.toRingHom := hvalLocal
  have : IsLocalHom e.toRingHom := IsLocalHom.of_surjective _ e.surjective
  have hgLocal : IsLocalHom g := RingHom.isLocalHom_comp _ _
  have hgFlat : g.Flat :=
    (RingHom.Flat.of_bijective e.bijective).comp hA.2.2.choose_spec.1
  have hsmooth : EssentiallySmooth Q D := by
    refine ⟨D, inferInstance, inferInstance, inferInstance, ⊥, ?_⟩
    exact ⟨(IsLocalization.atUnits D (⊥ : Submonoid D)
      (S := Localization (⊥ : Submonoid D)) bot_le).restrictScalars Q⟩
  refine ⟨m, φ, ψ, hψ, hideal, hflat, hQ.1, hQ.2, hB.1, hB.2,
    D, inferInstance, inferInstance, g, inferInstance, inferInstance,
    ?_, hgLocal, hsmooth, hgFlat, ?_, ?_⟩
  · change IsLocalHom (e.symm.toRingHom.comp f)
    have : IsLocalHom e.symm.toRingHom := IsLocalHom.of_surjective _ e.symm.surjective
    exact RingHom.isLocalHom_comp _ _
  · change (g.comp (algebraMap Q D)).comp (Ideal.Quotient.mk (I ^ n)) = _
    have hgf : g.comp (algebraMap Q D) = A.val.toRingHom.comp f := by
      ext x
      rfl
    rw [hgf]
    exact hfcomm
  · intro x hx
    refine ⟨e.symm ⟨x, hE x hx⟩, ?_⟩
    exact congrArg (fun y : A ↦ (y : B)) (e.apply_symm_apply _)

end Algebra
