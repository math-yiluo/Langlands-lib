/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.TensorProduct.Basis
import WeilConjectures.RingTheory.ConormalChartUnramifiedLocalization
import WeilConjectures.RingTheory.UnramifiedSmoothConormalChartFlat
import Mathlib.RingTheory.Smooth.Fiber
/-!
# An étale polynomial chart along the zero section

Source: Stacks Project, proof of Lemma 07CH, the construction of `B'_g`.
(blueprint: lem-weil-pbc-smooth-conormal-basis-etale-polynomial-chart).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Algebra

private theorem exists_conormal_matrix
    (R : Type u) [CommRing R] (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R)
    [Smooth R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))]
    (b : Module.Basis (Fin c)
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
      (Ideal.span (Set.range f)).Cotangent)
    (hb : ∀ j : Fin c,
      b j = (Ideal.span (Set.range f)).toCotangent
        ⟨f j, Ideal.subset_span (Set.mem_range_self j)⟩) :
    ∃ a : Fin n → Fin c → MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f),
      ∀ j k, ∑ i, Ideal.Quotient.mk (Ideal.span (Set.range f))
        (MvPolynomial.pderiv i (f j)) * a i k = if j = k then 1 else 0 := by
  classical
  let J := Ideal.span (Set.range f)
  let C := MvPolynomial (Fin n) R ⧸ J
  have hsurj : Function.Surjective (algebraMap (MvPolynomial (Fin n) R) C) :=
    Ideal.Quotient.mk_surjective
  obtain ⟨l₀, hl⟩ := (FormallySmooth.iff_split_injection (R := R) hsurj).mp
    (inferInstance : FormallySmooth R C)
  let K := RingHom.ker (algebraMap (MvPolynomial (Fin n) R) C)
  have hK : K = J := Ideal.mk_ker
  let q := Ideal.Cotangent.equivOfEq K J hK
  let l : (_root_.TensorProduct (MvPolynomial (Fin n) R) C
      (KaehlerDifferential R (MvPolynomial (Fin n) R)))
      →ₗ[C] J.Cotangent := (q.toLinearMap.comp l₀).extendScalarsOfSurjective hsurj
  let d := (KaehlerDifferential.mvPolynomialBasis R (Fin n)).baseChange C
  let a : Fin n → Fin c → C := fun i k ↦ b.repr (l (d i)) k
  refine ⟨a, ?_⟩
  intro j k
  let x : K := ⟨f j, by rw [hK]; exact Ideal.subset_span (Set.mem_range_self j)⟩
  have hq : q (K.toCotangent x) = b j := by
    rw [Ideal.Cotangent.equivOfEq_toCotangent, hb]
    congr 1
  have hd : _root_.TensorProduct.tmul (MvPolynomial (Fin n) R) (1 : C)
      (KaehlerDifferential.D R (MvPolynomial (Fin n) R) (f j)) =
      ∑ i, Ideal.Quotient.mk J (MvPolynomial.pderiv i (f j)) • d i := by
    apply d.repr.injective
    ext i
    rw [Module.Basis.baseChange_repr_tmul]
    simp only [KaehlerDifferential.mvPolynomialBasis_repr_apply, Algebra.smul_def,
      mul_one]
    simp only [map_sum, map_smul, Module.Basis.repr_self]
    simp [Finsupp.single_apply, eq_comm]
    rfl
  have he := congrArg (fun z ↦ b.repr (q z) k)
    (DFunLike.congr_fun hl (K.toCotangent x))
  change b.repr (l (_root_.TensorProduct.tmul (MvPolynomial (Fin n) R) (1 : C)
    (KaehlerDifferential.D R (MvPolynomial (Fin n) R) (f j)))) k =
    b.repr (q (K.toCotangent x)) k at he
  rw [hd, hq] at he
  simpa [a, map_sum, map_smul, Finsupp.smul_apply, smul_eq_mul,
    Module.Basis.repr_self, Finsupp.single_apply] using he

/-- For a smooth polynomial quotient with equation classes a conormal basis, adjoining one
variable per equation admits a localization that is étale over a polynomial ring over `R`.
The localizing element has constant coefficient one, so the zero section survives.
This statement concerns an explicit localization, not a choice of an algebra retract.

Source: Stacks Project, proof of Lemma 07CH, steps constructing `B'`, `theta`, and `g`
and proving `R[z] → B'_g` étale (smoothing.tex, lines 606--671).
(blueprint: lem-weil-pbc-smooth-conormal-basis-etale-polynomial-chart).

Proof. Write `J = span (range f)` and `C = R[x]/J`, and use the given smoothness
and the given conormal basis. The following steps use those data (the reference to step 1
means precisely these hypotheses). At the end `g - 1 ∈ (y)` implies
`constantCoeff g = 1`; the map `theta` followed by localization supplies the asserted
`R`-algebra homomorphism and its étale algebra structure.

2. (The split conormal sequence and the matrix $(c_{ij})$.) Apply
[lem-weil-pbc-smooth-localization-conormal-split] to $P=R[x_1,\dots,x_n]$, $I=J$, $C=P/J$ and
$a=1$ (so $C_a=C$, smooth over $R$ by step 1): the map $\mathrm
d:J/J^2\to\bigoplus_{i=1}^nC\,\mathrm dx_i$, $\mathrm d(h\bmod J^2)=\sum_i\overline{\partial
h/\partial x_i}\,\mathrm dx_i$ [def-weil-pbc-polynomial-partial-derivative], has a $C$-linear left
inverse $t$, and $0\to J/J^2\to\bigoplus_iC\,\mathrm dx_i\to\Omega_{C/R}\to0$ is split exact, so
$\Omega_{C/R}\oplus J/J^2\cong C^{\oplus n}$. Since $\bar f_1,\dots,\bar f_c$ is a basis of
$J/J^2$ (step 1), $J/J^2\cong C^{\oplus c}$, and write $t(\mathrm dx_i)=\sum_{j=1}^cc_{ij}\bar
f_j$ with $c_{ij}\in C$. Then for each $\ell$, $\bar f_\ell=t(\mathrm d\bar
f_\ell)=\sum_i\overline{\partial f_\ell/\partial x_i}\,t(\mathrm
dx_i)=\sum_j\bigl(\sum_i\overline{\partial f_\ell/\partial x_i}\,c_{ij}\bigr)\bar f_j$, and
comparing coefficients in the basis gives $\sum_{i=1}^n\overline{\partial f_\ell/\partial
x_i}\,c_{ij}=\delta_{\ell j}$ in $C$ (Kronecker delta). Moreover, tensoring $\Omega_{C/R}\oplus
C^{\oplus c}\cong C^{\oplus n}$ with the residue field $\kappa(Q)$ of any prime $Q\subset C$ gives
$\dim_{\kappa(Q)}\Omega_{C/R}\otimes_C\kappa(Q)=n-c$. Uses:
lem-weil-pbc-smooth-localization-conormal-split, def-weil-pbc-polynomial-partial-derivative.

3. (The algebra $B'$, its retraction and the map $\theta$.) Let $B'=C[y_1,\dots,y_c]$
[def-weil-pbc-mv-polynomial-ring]; by the universal properties of polynomial rings and quotients
$B'=R[x_1,\dots,x_n,y_1,\dots,y_c]/(f_1,\dots,f_c)$. The inclusion $C\to B'$ is smooth
[lem-weil-pbc-polynomial-ring-smooth], so $R\to B'$ is smooth
[lem-weil-pbc-smooth-ring-map-base-change-composition](2). The $C$-algebra map $\varepsilon:B'\to
C$, $y_j\mapsto0$, is a retraction of $C\to B'$. Choose $\tilde c_{ij}\in R[x_1,\dots,x_n]$
mapping to $c_{ij}$ and let $\theta:R[z_1,\dots,z_n]\to B'$ be the $R$-algebra map with
$\theta(z_i)=\bar x_i-\sum_jc_{ij}y_j$; regard $B'$ as an $R[z_1,\dots,z_n]$-algebra via $\theta$.
Uses: def-weil-pbc-mv-polynomial-ring, lem-weil-pbc-polynomial-ring-smooth,
lem-weil-pbc-smooth-ring-map-base-change-composition.

4. ($\Omega_{B'/R[z]}=(y_1,\dots,y_c)\Omega_{B'/R[z]}$.) Write
$\Omega'=\Omega_{B'/R[z_1,\dots,z_n]}$ with derivation $\mathrm d$
[def-weil-pbc-kahler-differentials] and $I_y=(y_1,\dots,y_c)B'$. (a) Since $B'$ is generated as an
$R$-algebra by the $\bar x_i,y_j$ and $\mathrm d$ is additive, satisfies the Leibniz rule and
kills the image of $R$, $\Omega'$ is generated as a $B'$-module by $\mathrm d\bar
x_1,\dots,\mathrm d\bar x_n,\mathrm dy_1,\dots,\mathrm dy_c$; in particular it is a finitely
generated $B'$-module. (b) The map $R[x_1,\dots,x_n]\to\Omega'$, $h\mapsto\mathrm d\bar h$, is an
$R$-derivation, so by the universal property and the basis $\mathrm dx_i$ of $\Omega_{R[x]/R}$
with $\mathrm dh=\sum_i\frac{\partial h}{\partial x_i}\mathrm dx_i$
[lem-weil-pbc-polynomial-ring-kahler-basis] we get $\mathrm d\bar h=\sum_i\overline{\partial
h/\partial x_i}\,\mathrm d\bar x_i$. (c) As $\bar f_j=0$ in $B'$: $0=\mathrm d\bar
f_j=\sum_i\overline{\partial f_j/\partial x_i}\,\mathrm d\bar x_i$. As $\theta(z_i)$ comes from
$R[z]$: $0=\mathrm d\theta(z_i)=\mathrm d\bar x_i-\sum_\ell(c_{i\ell}\,\mathrm
dy_\ell+y_\ell\,\mathrm dc_{i\ell})$, so $\mathrm d\bar x_i\equiv\sum_\ell c_{i\ell}\,\mathrm
dy_\ell\bmod I_y\Omega'$. Substituting and using the identity of step 2 (which holds in $C$, hence
in $B'$): $0\equiv\sum_\ell\bigl(\sum_i\overline{\partial f_j/\partial
x_i}\,c_{i\ell}\bigr)\mathrm dy_\ell=\mathrm dy_j\bmod I_y\Omega'$. Hence every $\mathrm dy_j$ and
then every $\mathrm d\bar x_i$ lies in $I_y\Omega'$, and by (a) $\Omega'=I_y\Omega'$. Uses:
def-weil-pbc-kahler-differentials, lem-weil-pbc-polynomial-ring-kahler-basis.

5. (Localizing: $R[z]\to B'_g$ is of finite presentation with $\Omega=0$.) By step 4 and
[lem-weil-pbc-nakayama-one-plus-ideal-annihilator] (Stacks 00DV, applied to the finitely generated
$B'$-module $\Omega'$ and the ideal $I_y$) there is $g\in B'$ with $g-1\in I_y$ and $g\Omega'=0$.
Put $B=B'_g$ [def-weil-ring-localization-away]. By
[lem-weil-pbc-kahler-differentials-localization], $\Omega_{B/R[z]}\cong(\Omega')_g=0$. Choose
$\tilde g\in R[x,y]$ mapping to $g$; by [lem-weil-pbc-localization-away-polynomial-quotient],
$B\cong R[x_1,\dots,x_n,y_1,\dots,y_c,w]/(f_1,\dots,f_c,\tilde gw-1)$ as $R$-algebras, and
therefore, as $R[z]$-algebras, $B\cong R[z_1,\dots,z_n][x,y,w]/(f_1,\dots,f_c,\tilde gw-1,\
z_1-x_1+\sum_j\tilde c_{1j}y_j,\dots,z_n-x_n+\sum_j\tilde c_{nj}y_j)$ (the last $n$ relations
eliminate the $z_i$). So $B$ is a finitely presented $R$-algebra and a finitely presented
$R[z]$-algebra [def-weil-pbc-finitely-presented-algebra], with $\Omega_{B/R[z]}=0$; that is,
$R[z]\to B$ is unramified (even G-unramified) in the sense of Stacks, Algebra, Definition 00UT.
Uses: lem-weil-pbc-nakayama-one-plus-ideal-annihilator, def-weil-ring-localization-away,
lem-weil-pbc-kahler-differentials-localization,
lem-weil-pbc-localization-away-polynomial-quotient, def-weil-pbc-finitely-presented-algebra.

6. (Smoothness of $B$ and the rank of $\Omega_{B/R}$.) $R\to B$ is smooth by
[lem-weil-pbc-smooth-ring-map-principal-localization] (applied to the smooth $R\to B'$ of step 3),
and $C\to B$ is smooth by the same node applied to the smooth $C\to B'$. Composition and
localization establish the required smoothness over $R$
[lem-weil-pbc-smooth-ring-map-base-change-composition](2). Finally
$\Omega_{B'/R}\cong(B'\otimes_C\Omega_{C/R})\oplus B'^{\oplus c}$
[theorem-finite-etale-covers-proper-henselian--2] and $\Omega_{B/R}\cong(\Omega_{B'/R})_g$
[lem-weil-pbc-kahler-differentials-localization]; with step 2 this gives $\dim_{\kappa(\mathfrak
Q)}\Omega_{B/R}\otimes_B\kappa(\mathfrak Q)=(n-c)+c=n$ for every prime $\mathfrak Q\subset B$ (if
$Q$ is the inverse image of $\mathfrak Q$ in $C$, then
$(B\otimes_C\Omega_{C/R})\otimes_B\kappa(\mathfrak
Q)=(\Omega_{C/R}\otimes_C\kappa(Q))\otimes_{\kappa(Q)}\kappa(\mathfrak Q)$). Uses:
lem-weil-pbc-smooth-ring-map-principal-localization,
lem-weil-pbc-smooth-ring-map-base-change-composition,
theorem-finite-etale-covers-proper-henselian--2,
lem-weil-pbc-kahler-differentials-localization.

7. (The fibre over a prime of $R$.) Fix a prime $\mathfrak p\subset R$, let $k=\kappa(\mathfrak
p)$ [def-weil-pbc-localization-at-prime], $T=B\otimes_Rk$ and $P_k=R[z_1,\dots,z_n]\otimes_Rk\cong
k[z_1,\dots,z_n]$ [lem-weil-pbc-polynomial-scalar-extension]; $T\cong B\otimes_{R[z]}P_k$ is a
$P_k$-algebra, finitely generated as a $k$-algebra (step 5). (i) $k\to T$ is smooth
[lem-weil-pbc-smooth-ring-map-base-change-composition](1). (ii) $\Omega_{T/P_k}\cong
T\otimes_B\Omega_{B/R[z]}=0$ and (iii) $\Omega_{T/k}\cong T\otimes_B\Omega_{B/R}$
[lem-weil-pbc-kahler-differentials-base-change], so by step 6 $\dim_{\kappa(\mathfrak
n)}\Omega_{T/k}\otimes_T\kappa(\mathfrak n)=n$ for every prime $\mathfrak n\subset T$. (iv) $k\to
P_k$ is smooth [lem-weil-pbc-polynomial-ring-smooth] and $\Omega_{P_k/k}$ is free with basis
$\mathrm dz_1,\dots,\mathrm dz_n$ [lem-weil-pbc-polynomial-ring-kahler-basis]. Uses:
def-weil-pbc-localization-at-prime, lem-weil-pbc-polynomial-scalar-extension,
lem-weil-pbc-smooth-ring-map-base-change-composition,
lem-weil-pbc-kahler-differentials-base-change, lem-weil-pbc-polynomial-ring-smooth,
lem-weil-pbc-polynomial-ring-kahler-basis.

8. (Local rings at maximal ideals: regular of dimension $n$.) Let $\mathfrak m\subset T$ be a
maximal ideal and $\mathfrak p'\subset P_k$ its inverse image. (a) $T/\mathfrak m$ is a field
finitely generated as a $k$-algebra, hence finite over $k$ [lem-weil-pbc-zariski-lemma];
$P_k/\mathfrak p'\subseteq T/\mathfrak m$ is a domain of finite $k$-dimension, hence a field
(multiplication by a nonzero element is an injective $k$-linear endomorphism, hence surjective),
so $\mathfrak p'$ is maximal. (b) $T_{\mathfrak m}$ is a regular local ring
[def-weil-regular-scheme] by [lem-weil-pbc-smooth-fibre-regular-local] applied to the smooth $k\to
T$ and the prime $(0)$ of $k$ ($T\otimes_kk=T$). $k\to T$ is smooth at $\mathfrak m$ ($g=1$ in
[def-weil-pbc-singular-ideal]), so by [lem-weil-pbc-smooth-over-field-dimension-differentials] and
step 7(iii) the dimension of $\operatorname{Spec}T$ at $\mathfrak m$ is $n$, and by
[lem-weil-pbc-closed-point-dimension-local-ring] $\dim T_{\mathfrak m}=n$
[def-weil-pbc-krull-dimension-ring]. (c) The same argument for $k\to P_k$ and the maximal ideal
$\mathfrak p'$, using step 7(iv), shows that $(P_k)_{\mathfrak p'}$ is a regular local ring of
dimension $n$. Uses: lem-weil-pbc-zariski-lemma, def-weil-regular-scheme,
lem-weil-pbc-smooth-fibre-regular-local, def-weil-pbc-singular-ideal,
lem-weil-pbc-smooth-over-field-dimension-differentials,
lem-weil-pbc-closed-point-dimension-local-ring, def-weil-pbc-krull-dimension-ring.

9. (The fibres of $P_k\to T$ are zero-dimensional.) With $\mathfrak m,\mathfrak p'$ as in step 8,
let $F=T\otimes_{P_k}\kappa(\mathfrak p')$. It is a finitely generated $\kappa(\mathfrak
p')$-algebra with $\Omega_{F/\kappa(\mathfrak p')}\cong F\otimes_T\Omega_{T/P_k}=0$
([lem-weil-pbc-kahler-differentials-base-change], step 7(ii)), so by
[lem-weil-pbc-unramified-ring-map-iff-unramified-affine]
$\operatorname{Spec}F\to\operatorname{Spec}\kappa(\mathfrak p')$ is unramified and by
[lem-weil-pbc-unramified-algebra-over-field-product] $F\cong L_1\times\dots\times L_r$ with fields
$L_i$. By [lem-weil-pbc-fibre-ring-localization-quotient], $F\cong T_{\mathfrak p'}/\mathfrak
p'T_{\mathfrak p'}$, so $T_{\mathfrak m}/\mathfrak p'T_{\mathfrak m}$ is the localization of $F$
at the prime given by $\mathfrak m$; the localization of a finite product of fields at a prime is
one of the factors, a field. Hence $\dim(T_{\mathfrak m}/\mathfrak p'T_{\mathfrak m})=0$
[def-weil-pbc-krull-dimension-ring]. Uses: lem-weil-pbc-kahler-differentials-base-change,
lem-weil-pbc-unramified-ring-map-iff-unramified-affine,
lem-weil-pbc-unramified-algebra-over-field-product, lem-weil-pbc-fibre-ring-localization-quotient,
def-weil-pbc-krull-dimension-ring.

10. ($T$ is flat over $P_k$, by miracle flatness.) For a maximal ideal $\mathfrak m\subset T$ and
$\mathfrak p'$ as in step 8, $(P_k)_{\mathfrak p'}\to T_{\mathfrak m}$ is a local homomorphism of
Noetherian local rings; $(P_k)_{\mathfrak p'}$ is regular (step 8(c)); $T_{\mathfrak m}$ is
regular of dimension $n$, so its maximal ideal is generated by $n$ elements, which form a regular
sequence by [lem-weil-pbc-regular-local-generators-regular-sequence], so
$\operatorname{depth}T_{\mathfrak m}\ge n=\dim T_{\mathfrak m}$ [def-weil-pbc-depth]; and $\dim
T_{\mathfrak m}=n=n+0=\dim(P_k)_{\mathfrak p'}+\dim(T_{\mathfrak m}/\mathfrak p'T_{\mathfrak m})$
(steps 8, 9). By [lem-weil-pbc-miracle-flatness] (Stacks 00R4), $(P_k)_{\mathfrak p'}\to
T_{\mathfrak m}$ is flat. Now let $\mathfrak n\subset T$ be any prime, $\mathfrak
m\supseteq\mathfrak n$ a maximal ideal, and $\mathfrak p''$ the inverse image of $\mathfrak n$ in
$P_k$. $T_{\mathfrak n}$ is a localization of $T_{\mathfrak m}$, hence flat over it
[lem-weil-pbc-localization-flat]; with the flat maps $P_k\to(P_k)_{\mathfrak p'}\to T_{\mathfrak
m}$ we get $P_k\to T_{\mathfrak n}$ flat [lem-weil-pbc-flat-ring-map-comp], and since this map
factors through the localization $(P_k)_{\mathfrak p''}$, $T_{\mathfrak n}$ is flat over
$(P_k)_{\mathfrak p''}$ [lem-weil-pbc-flat-over-localization]. By
[lem-weil-pbc-flat-map-local-criterion], $P_k\to T$ is flat (trivially so if $T=0$). Uses:
lem-weil-pbc-regular-local-generators-regular-sequence, def-weil-pbc-depth,
lem-weil-pbc-miracle-flatness, lem-weil-pbc-localization-flat, lem-weil-pbc-flat-ring-map-comp,
lem-weil-pbc-flat-over-localization, lem-weil-pbc-flat-map-local-criterion.

11. ($R[z]\to B$ is flat, by the critère de platitude par fibres.) Let $\mathfrak Q\subset B$ be a
prime, $\mathfrak p'\subset R[z]$ and $\mathfrak p\subset R$ its inverse images. Apply
[lem-weil-pbc-criterion-flatness-fibre] (Stacks 00R7) to $R_{\mathfrak p}\to R[z]_{\mathfrak
p'}\to B_{\mathfrak Q}$ (local homomorphisms) and $M=B_{\mathfrak Q}$: (1) $R[z]_{\mathfrak p'}$
and $B_{\mathfrak Q}$ are localizations of the finitely presented $R$-algebras $R[z]$ and $B$
(step 5), hence also of $R_{\mathfrak p}\otimes_RR[z]$ and $R_{\mathfrak p}\otimes_RB$, finitely
presented over $R_{\mathfrak p}$; (2), (3) $M$ is free of rank one over $B_{\mathfrak Q}$,
nonzero; (4) by [lem-weil-pbc-fibre-ring-localization-quotient], $M/\mathfrak pM$ and
$R[z]_{\mathfrak p'}/\mathfrak pR[z]_{\mathfrak p'}$ are the localizations of
$T=B\otimes_R\kappa(\mathfrak p)$ and $P_k$ at the primes given by $\mathfrak Q$ and $\mathfrak
p'$, and the map between them is the localization of $P_k\to T$, which is flat by step 10 and
[lem-weil-pbc-flat-local-ring-maps]; (5) $B$ is flat over $R$ [lem-weil-pbc-smooth-ring-map-flat]
(step 6), so $B_{\mathfrak Q}$ is flat over $R_{\mathfrak p}$ [lem-weil-pbc-flat-local-ring-maps].
Hence $B_{\mathfrak Q}$ is flat over $R[z]_{\mathfrak p'}$ for every prime $\mathfrak Q$, and
$R[z]\to B$ is flat [lem-weil-pbc-flat-map-local-criterion]. Uses:
lem-weil-pbc-criterion-flatness-fibre, lem-weil-pbc-fibre-ring-localization-quotient,
lem-weil-pbc-flat-local-ring-maps, lem-weil-pbc-smooth-ring-map-flat,
lem-weil-pbc-flat-map-local-criterion.

12. ($R[z]\to B$ is étale.) The morphism $\operatorname{Spec}B\to\operatorname{Spec}R[z]$
[def-weil-affine-spectrum] is locally of finite presentation [def-sbc-locally-finite-presentation]
since $B$ is a finitely presented $R[z]$-algebra (step 5); it is flat [def-weil-flat-morphism]
since its local rings are the maps $R[z]_{\mathfrak p'}\to B_{\mathfrak Q}$, flat by step 11 and
[lem-weil-pbc-flat-local-ring-maps]; and it is unramified [def-weil-unramified-morphism] by
[lem-weil-pbc-unramified-ring-map-iff-unramified-affine], since $B$ is a finitely generated
$R[z]$-algebra with $\Omega_{B/R[z]}=0$ (step 5). So
$\operatorname{Spec}B\to\operatorname{Spec}R[z]$ is étale [def-weil-etale-morphism]. (Stacks
concludes with Algebra Lemma 00U6, lemma-characterize-etale, that $R[z]\to B$ is étale in the
sense of Algebra Definition 00U1; with the definition of étale used in this DAG the three
properties give it directly, and the agreement with 00U1 is
[lem-weil-pbc-etale-ring-map-iff-etale-affine].) Uses: def-weil-affine-spectrum,
def-sbc-locally-finite-presentation, def-weil-flat-morphism, lem-weil-pbc-flat-local-ring-maps,
def-weil-unramified-morphism, lem-weil-pbc-unramified-ring-map-iff-unramified-affine,
def-weil-etale-morphism, lem-weil-pbc-etale-ring-map-iff-etale-affine. -/
/- Core construction of the chart, retaining the canonical map on constants.

The additional constant-map equation records the retraction part of the construction and is
used to extract the statement below.
(blueprint: lem-weil-pbc-smooth-conormal-basis-etale-polynomial-chart-core).
-/
theorem exists_etale_polynomial_chart_core
    (R : Type u) [CommRing R] (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R)
    [Smooth R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))]
    (b : Module.Basis (Fin c)
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
      (Ideal.span (Set.range f)).Cotangent)
    (hb : ∀ j : Fin c,
      b j = (Ideal.span (Set.range f)).toCotangent
        ⟨f j, Ideal.subset_span (Set.mem_range_self j)⟩) :
    ∃ g : MvPolynomial (Fin c) (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)),
      MvPolynomial.constantCoeff g = 1 ∧
      ∃ θ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g,
        @Etale (MvPolynomial (Fin n) R) (Localization.Away g) _ _
            θ.toRingHom.toAlgebra ∧
          θ.toRingHom.comp MvPolynomial.C = Algebra.ofId R (Localization.Away g) := by
  classical
  obtain ⟨a, ha⟩ := exists_conormal_matrix R n c f b hb
  obtain ⟨g, hg, hu⟩ := exists_unramified_conormal_polynomial_chart R n c f a ha
  let C := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)
  let D := MvPolynomial (Fin c) C
  let θ₀ : MvPolynomial (Fin n) R →ₐ[R] D := MvPolynomial.aeval
    (fun i ↦ MvPolynomial.C (Ideal.Quotient.mk (Ideal.span (Set.range f))
      (MvPolynomial.X i)) - ∑ j, MvPolynomial.C (a i j) * MvPolynomial.X j)
  let θ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g :=
    (IsScalarTower.toAlgHom R D (Localization.Away g)).comp θ₀
  let : Algebra (MvPolynomial (Fin n) R) (Localization.Away g) :=
    θ.toRingHom.toAlgebra
  let : SMul (MvPolynomial (Fin n) R) (Localization.Away g) :=
    θ.toRingHom.toAlgebra.toSMul
  let : Module (MvPolynomial (Fin n) R) (Localization.Away g) :=
    θ.toRingHom.toAlgebra.toModule
  have : IsScalarTower R (MvPolynomial (Fin n) R) (Localization.Away g) :=
    IsScalarTower.of_algebraMap_eq' θ.comp_algebraMap.symm
  have : FormallyUnramified (MvPolynomial (Fin n) R) (Localization.Away g) := hu
  have : Module.Flat (MvPolynomial (Fin n) R) (Localization.Away g) :=
    flat_of_unramified_smooth_conormal_chart R n c f b g θ hu
  have : FinitePresentation D (Localization.Away g) :=
    IsLocalization.Away.finitePresentation g
  have : FinitePresentation R (Localization.Away g) :=
    FinitePresentation.trans R D (Localization.Away g)
  have : FinitePresentation (MvPolynomial (Fin n) R) (Localization.Away g) :=
    FinitePresentation.of_restrict_scalars_finitePresentation R
      (MvPolynomial (Fin n) R) (Localization.Away g)
  refine ⟨g, hg, θ, Etale.of_formallyUnramified_of_flat, ?_⟩
  exact θ.comp_algebraMap

/-- (blueprint: lem-weil-pbc-smooth-conormal-basis-etale-polynomial-chart) -/
theorem exists_etale_polynomial_chart_of_conormal_basis
    (R : Type u) [CommRing R] (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R)
    [Smooth R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))]
    (b : Module.Basis (Fin c)
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
      (Ideal.span (Set.range f)).Cotangent)
    (hb : ∀ j : Fin c,
      b j = (Ideal.span (Set.range f)).toCotangent
        ⟨f j, Ideal.subset_span (Set.mem_range_self j)⟩) :
    ∃ g : MvPolynomial (Fin c) (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)),
      MvPolynomial.constantCoeff g = 1 ∧
      ∃ θ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g,
        @Etale (MvPolynomial (Fin n) R) (Localization.Away g) _ _
          θ.toRingHom.toAlgebra := by
  obtain ⟨g, hg, θ, hθ, _⟩ :=
    exists_etale_polynomial_chart_core R n c f b hb
  exact ⟨g, hg, θ, hθ⟩

end Algebra
