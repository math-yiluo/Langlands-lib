/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedFiniteExceptionalAt
public import WeilConjectures.AlgebraicGeometry.SixFunctors.SpecifiedExceptionalClassHom
public import WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteCompactSupportScalarTransport
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleExceptionalConstantTensor
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.ExceptionalFiniteScalarMatesData
import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.ExceptionalFiniteScalarOperation
import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.ExceptionalFiniteScalar
import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.ExceptionalFiniteScalarMaps

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures.ExceptionalFiniteScalar

/-- Finite scalar extension preserves the actual constructible finite-Tor categories
and their Tor intervals, with literal restrictions and the canonical scalar mates.
Quotient, ramified, identity and composite unital maps are all quantified directly.

Source: Zheng, Propositions 2.23, 2.29 and 3.16, Construction 2.26; Stacks 0GL6,
09AL, 09B1 and 07A4 (blueprint: lem-sf-exceptional-finite-scalar-mates).

Proof plan (the eight steps of the DAG node):

1. First work on the ordinary etale categories. For $K\in\mathcal C_{T,A}$, constructible origin
and Tor comparison give an etale object $K^e$ with the same Tor interval $[u,v]$. The
constructible variant of the flat-model lemma applies because $T$ is finite type over $k$: choose
a flat constructible model $P$ supported in $[u,v]$. A bounded complex of flat sheaves is K-flat,
so derived change of rings computes $K^e\otimes_A^LB$ by $P\otimes_AB$, canonically on morphisms
and independently of this model. Each term is flat over $B$: for an injection $M\hookrightarrow N$
of $B$-module sheaves, $(P^i\otimes_AB)\otimes_BM=P^i\otimes_A\operatorname{Res}M$, and flatness
of $P^i$ preserves this injection. On any stratum trivializing $P^i$, its tensor with the finite
ring $B$ is finite locally constant. Take a common finite refinement for the finitely many terms.
The constructible Serre theorem gives constructible kernels, images and cohomology. The same flat
complex supported in $[u,v]$ therefore has Tor interval $[u,v]$ over $B$, including for nonflat
$A\to B$. Uses: theorem-comparison-constructible-sheaves, lem-sf-comparison-tor-amplitude,
lemma-flat-models-generators--1, lem-pur-derived-change-of-rings, thm-constructible-serre,
lem-weil-pbc-independent-bounded-flat-kflat.

2. Exact comparison inverse image and the canonical derived pullback/tensor identification
identify $\nu_T^*(P\otimes_AB)$ with $S_{a,T}(\nu_T^*P)$. The constructible-origin and
Tor-comparison theorems carry the conclusion of step 1 back to the actual pro-etale category, with
the unchanged interval. Define $T_{a,T}$ on objects by the ambient $S_{a,T}$ with this membership
proof and on morphisms by $S_{a,T}$ itself. The subcategory is full, so identities and composition
are literally those of the ambient functor: $I_{T,B}T_{a,T}=S_{a,T}I_{T,A}$, with equality
realization. Exactness and its canonical shifts are inherited from derived change of rings. This
construction applies separately to every actual finite ring map, including an identity or a
composite. Uses: lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
theorem-comparison-constructible-sheaves, lem-sf-comparison-tor-amplitude,
lem-pur-derived-change-of-rings.

3. Write $F^e_R=Rp_{c,\mathrm{et},R,*}j^e_{!,R}$ and $G^e_R=f^\times_{c,R}$ on the entire etale
derived categories. Use their ambient adjunctions, with counits $\epsilon^e_R$. Let $q^e_a$ be
exactly the proper coefficient comparison at $j^e_{!,A}(-)$ followed by $Rp_{c,B,*}$ of the open
scalar tensor map. The proper comparison theorem specifies its transpose as scalar extension of
the proper counit after the canonical pullback/tensor identification; the open map is scalar
balancing on the open and zero off it. The compact scalar coherence theorem proves this specified
composite invertible for any finite $A\to B$, with no flatness assumption. Thus
$q^e_a:S_YF^e_A\cong F^e_BS_X$ is the required left map rather than an independently chosen
isomorphism. Uses: theorem-existence-exceptional-inverse-image--1,
lem-asd-proper-finite-coefficient-extension, lem-pur-etale-compact-scalar-coherence.

4. Put $U_T=\operatorname{Res}_{a,T}$. Derived ringed direct-image composition applied to the two
factorizations of the same ringed-topos map gives $U_YRp_{c,B,*}\cong Rp_{c,A,*}U_{\overline X}$.
Open extension by zero commutes with $U$ termwise: it changes only the ring action on the open and
both sides are zero off the open. Consequently $h:U_YF^e_B\cong F^e_AU_X$ is the canonical
restriction comparison. For any $N\in D(Y_{\mathrm{et}},B)$ and $K\in D(X_{\mathrm{et}},A)$ the
scalar adjunction, the two exceptional adjunctions and $q^e_a$ give natural bijections
$$\operatorname{Hom}_A(K,U_XG^e_BN)\cong\operatorname{Hom}_B(S_XK,G^e_BN)\cong\operatorname{Hom}_B
(F^e_BS_XK,N)\cong\operatorname{Hom}_B(S_YF^e_AK,N)\cong\operatorname{Hom}_A(K,G^e_AU_YN).$$
Yoneda gives a canonical isomorphism $d_N:U_XG^e_BN\cong G^e_AU_YN$. Explicitly $d_N$ is the
transpose of
$F^e_AU_XG^e_BN\xrightarrow{h^{-1}}U_YF^e_BG^e_BN\xrightarrow{U_Y\epsilon^e_{B,N}}U_YN$. Indeed,
following $\mathrm{id}$ through the chain, its image is
$U_Y(\epsilon^e_{B,N}F^e_B(c)\,q^e)\circ\eta$, with $\eta:x\mapsto x\otimes1$ the scalar unit and
$c:x\otimes b\mapsto b\,x$ the scalar counit. By the proper coefficient theorem and the open
balancing map, $h\circ U_Yq^e_K$ is the projection map $P_K:B_Y\otimes^L_AF^e_AK\to
F^e_A(B_X\otimes^L_AK)$. Naturality of $h$ then rewrites the image as
$U_Y\epsilon^e_{B,N}\,h^{-1}\,F^e_A(U_Xc)\,P\,\eta$. Since $P$ is natural in the constant factor
and is the identity for the unit $A$, $F^e_A(U_Xc)\,P\,\eta=\mathrm{id}$. Uses:
lem-weil-pbc-ringed-topoi-derived-pushforward-composition,
lem-pur-sheaf-ring-derived-coefficient-adjunction, theorem-existence-exceptional-inverse-image--1,
lem-galois-yoneda-hom-bijection, lem-pur-etale-compact-scalar-coherence,
lem-asd-proper-finite-coefficient-extension, lem-weil-pbc-ringed-projection-mate-exact.

5. For $L\in D(Y_{\mathrm{et}},A)$ define $b^e_{a,L}$ to be the $F^e_B\dashv G^e_B$ transpose of
$$F^e_BS_XG^e_AL\xrightarrow{(q^e_{a,G^e_AL})^{-1}}S_YF^e_AG^e_AL\xrightarrow{S_Y\epsilon^e_{A,L}}
S_YL.$$
The adjunction bijection gives naturality in $L$ and exactly
$$\epsilon^e_{B,S_YL}\,F^e_B(b^e_{a,L})\,q^e_{a,G^e_AL}=S_Y\epsilon^e_{A,L}.$$ Under $d_{S_YL}$
and $U_TS_T(-)=B_T\otimes_A^L(-)$, its restriction has $F^e_A$-transpose
$$F^e_A(B_X\otimes_A^LG^e_AL)\xrightarrow{P^{-1}}B_Y\otimes_A^LF^e_AG^e_AL\xrightarrow{1\otimes\ep
silon^e_{A,L}}B_Y\otimes_A^LL.$$
Indeed substitute the transpose formula for $d$ from step 4 into the preceding counit equation;
$U_Yq^e$ is $P$, since its proper factor is precisely the ordered projection by the proper
coefficient theorem and its open factor is the balancing map. Naturality of $h$ and the counit
equation replace $U_Y\epsilon^e_B\,U_YF^e_B(b^e)$ by $U_YS_Y\epsilon^e_A\,(U_Yq^e)^{-1}$. This is
the displayed formula. It is the defining transpose of the exceptional constant-$B$ tensor map.
The constant-tensor theorem applies to $B\in D(A\text{-}\mathrm{Mod})$ without requiring
perfection or bounded projective dimension, so this restricted map is invertible. Restriction
detects quasi-isomorphisms: the cohomology of a cone is unchanged as an abelian sheaf. Hence the
$B$-linear map $b^e_a$ is invertible. Uses: theorem-existence-exceptional-inverse-image--1,
lem-pur-sheaf-ring-derived-coefficient-adjunction, lem-asd-proper-finite-coefficient-extension,
lem-pur-etale-compact-scalar-coherence, lem-pur-etale-exceptional-constant-tensor.

6. The finite-operations theorem supplies the actual constructible restrictions of $F_R,G_R$,
their adjunction and their adjoint shift structures, without absolute separatedness. Steps 1–2
apply both to its inputs and to $F_RK,G_RL$, so every endpoint of $q,b$ lies in the stated full
categories. Use constructible origin and the invertible bounded-below site-comparison unit to
transport $q^e,b^e$ through $\nu^*$ and $R\nu_*$. The compact-support comparison identifies
$\nu_Y^*F^e_R$ with $F_R\nu_X^*$; the exceptional realization is $G_R=\nu_X^*G^e_RR\nu_{Y,*}$. Its
unit and counit are precisely those of the transported adjunction. Applying the equivalence to the
equation in step 5 therefore gives
$$\epsilon_{B,T_{a,Y}L}F_B(b_{a,L})q_{a,G_AL}=T_{a,Y}(\epsilon_{A,L}).$$ Fullness identifies the
transported arrows with natural transformations on the actual full subcategories, and full
faithfulness makes this the unique transpose there. Uses: lem-sf-exceptional-finite-operations,
theorem-comparison-constructible-sheaves, theorem-bounded-below-cohomology-comparison,
proposition-comparison-immersions--4.

7. For the realization of $q$, expand the compact-support site comparison into its two factors.
The proper factor is the counit-normalized direct-image mate, not an unspecified site isomorphism.
The open factor is the termwise comparison $\nu_{\overline X}^*j^e_!\cong j^p_!\nu_X^*$.
Substitute their defining counit and open-unit transposes into step 3. The adjacent site units
cancel with the site counits, and the remaining proper transpose is the scalar extension of the
same proper counit followed by the same open balancing map. The tensor/pullback comparison
identifies the intervening tensors on K-flat models. Thus this transport is exactly the pro-etale
proper scalar-adjunction mate followed by the open tensor map. The counit equation of step 6 then
identifies $b$ with its required normalized transpose; no second choice of Hom bijections is
introduced. The restriction description in step 5 transports to etale-origin objects using these
same identifications and site units. Uses: lem-weil-pbc-comparison-direct-image-canonical-mate,
proposition-comparison-immersions--1, lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
lem-asd-proper-finite-coefficient-extension, lem-pur-sheaf-ring-derived-coefficient-adjunction.

8. All shift equations use the chosen derived shifts. Derived change of rings is exact. The
pullback/tensor comparison commutes with integer shifts; the proper projection map commutes with
shifts in the direct-image input by the first-variable projection theorem (and in the tensor input
by the ringed projection theorem). For the proper scalar map, transpose its proposed shift
equation: its counit formula and the pullback/tensor shift equation give identical transposes,
hence equal maps. This uses the scalar map itself and does not infer equality from restriction of
scalars. The open map is induced by the degreewise balancing identity. On the total tensor
complexes both paths shift the same summand and have the same tensor sign, so it commutes with
shifts in either input. The site comparison is termwise on inverse images and its direct-image
comparison is the mate using the adjoint shifts. Composition and whiskering preserve shift
equations. Consequently $q$ has the required shift equation. Transpose the two sides of the
proposed shift equation for $b$: by shift compatibility of the fixed counits, each transpose is
$T_Y\epsilon_A\,(q_{G_A})^{-1}$ with the same shift identifications. Injectivity of the adjunction
bijection makes the two arrows equal. This also proves compatibility for every integer, with the
unique adjoint shift structure. Uses: lem-pur-derived-change-of-rings,
lem-weil-pbc-ringed-projection-mate-exact, lem-sfb-ringed-projection-first-shift,
lem-pur-etale-open-derived-tensor, lem-weil-pbc-adjunction-shift-compatibility-unique,
lem-weil-pbc-commshift-nattrans-comp-whisker, theorem-existence-exceptional-inverse-image--1.
-/
theorem exceptionalFiniteScalarMates
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m : ℕ)
    (a : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1))
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) : Nonempty (Construction l E L n m a c) := by
  classical
  obtain ⟨source⟩ := finiteScalarOperation_exists D l _hl E n f c
  obtain ⟨target⟩ := finiteScalarOperation_exists D l _hl L m f c
  obtain ⟨scalarX⟩ := finiteScalar_exists D l _hl E L n m a X
  obtain ⟨scalarY⟩ := finiteScalar_exists D l _hl E L n m a Y
  obtain ⟨maps⟩ :=
    finiteScalarMaps_exists D l _hl E L n m a f c scalarX scalarY source target
  exact ⟨{
    scalarX := scalarX
    scalarY := scalarY
    source := source
    target := target
    q := maps.q
    b := maps.b
    q_normalized := maps.q_normalized
    counit := maps.counit
    qShift := maps.qShift
    bShift := maps.bShift
    etale := maps.etale
  }⟩

end WeilConjectures.ExceptionalFiniteScalar
