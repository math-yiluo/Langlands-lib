/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
import WeilConjectures.RingTheory.NoetherianFlatClosedFiberModel
import WeilConjectures.RingTheory.Flat.LocalizationPreservesFlatness
import WeilConjectures.RingTheory.FlatAndFlatOfFlatFibreNoetherian

/-!
# Flatness from flatness over the base and on the closed fibre

Source: Stacks Project, Algebra, Tag 00R7, lemma-criterion-flatness-fibre
(blueprint: lem-weil-pbc-criterion-flatness-fibre).
-/

@[expose] public section

universe u v w t p q

open scoped TensorProduct

namespace Module

/-- The fibre criterion for flatness, Stacks Project, Algebra, Tag 00R7
(blueprint: lem-weil-pbc-criterion-flatness-fibre).

`P`, `Q`, `W`, and `V` exhibit the two essentially finitely presented algebras:
`S` is a localization of the finitely presented `R`-algebra `P`, and `S'` of `Q`.
All scalar towers express restriction along the given local homomorphisms.
The closed fibre module is written as `(S / m_R S) ⊗[S] M`, canonically `M / m_R M`.

Proof from the node, following Tag 00R7 (including its localization corrections):
1. (Claim L: a localization of a module flat over the base is flat over the base.) Let $A\to C$
be a ring map, $W\subseteq C$ a multiplicative subset and $P$ a $C$-module which is flat as an
$A$-module [def-weil-pbc-flat-ring-map]; let $W^{-1}P$ be its localization
[def-weil-pbc-module-localization], an $A$-module through $A\to C$. Then $W^{-1}P$ is a flat
$A$-module. Indeed, let $u:X_1\to X_2$ be an injective $A$-linear map. Since $P$ is flat over
$A$, $1_P\otimes u:P\otimes_AX_1\to P\otimes_AX_2$ is injective, and it is $C$-linear for the
$C$-module structures through $P$. By [lem-weil-pbc-localization-module-exact] applied to the
exact sequence $0\to P\otimes_AX_1\to P\otimes_AX_2$, the map $W^{-1}(1_P\otimes u)$ is
injective. By [lem-weil-pbc-localization-tensor-over-base] (with the ring map $A\to C$, $T=W$,
the $C$-module $P$ and the $A$-modules $X_1$, $X_2$) there are isomorphisms
$W^{-1}(P\otimes_AX_i)\cong W^{-1}P\otimes_AX_i$, natural in $X_i$, so $W^{-1}(1_P\otimes u)$
corresponds to $1_{W^{-1}P}\otimes u$, which is therefore injective. Hence $W^{-1}P$ is flat
over $A$.

2. (Claim P: flatness passes along a base change followed by a localization.) Let $A\to A'$ and
$A\to B$ be ring maps, $B'$ a ring with ring maps $B\to B'$ and $A'\to B'$ agreeing on $A$, such
that the induced map $C:=B\otimes_AA'\to B'$, $b\otimes a'\mapsto\bar b\,\bar a'$, is a
localization of $C$ at a multiplicative subset $W\subseteq C$. Let $N$ be a $B$-module which is
flat as an $A$-module and $N'$ a $B'$-module ($A'$ acting through $A'\to B'$) with a $B$-linear
map $N\to N'$ such that $N\otimes_BB'\to N'$, $x\otimes y\mapsto y\bar x$, is an isomorphism.
Then $N'$ is a flat $A'$-module. Proof: $P:=N\otimes_AA'$ is a $C$-module ($(b\otimes
a')(x\otimes a'')=bx\otimes a'a''$) and a flat $A'$-module by
[lem-weil-pbc-flat-module-base-change]. By associativity of the tensor product,
$N\otimes_BC\cong P$ ($x\otimes(b\otimes a')\mapsto bx\otimes a'$) and
$N\otimes_BB'\cong(N\otimes_BC)\otimes_CB'\cong P\otimes_CB'$, $C$-linearly. Since $C\to B'$ is
a localization at $W$, $B'\cong W^{-1}C$ as $C$-algebras
[lem-weil-pbc-localization-of-localization] (its first sentence), and
[lem-weil-pbc-localization-tensor-over-base] (with the identity ring map of $C$, $T=W$, the
$C$-module $C$ and the $C$-module $P$) gives $W^{-1}C\otimes_CP\cong W^{-1}P$. Hence $N'\cong
W^{-1}P$ as $C$-modules, so as $A'$-modules, since $A'\to C\to B'$ is the given map $A'\to B'$.
By Claim L (step 1, with $A'\to C$, $W$ and $P$), $W^{-1}P$, hence $N'$, is flat over $A'$.

3. (The limit system.) Apply [lem-weil-pbc-limit-tower-essentially-finite-presentation] to $R\to
S\to S'$ and $M$, which is allowed by hypotheses (1), (2)
[def-weil-pbc-finitely-presented-algebra]. We obtain a nonempty directed set $\Lambda$, local
rings $(R_\lambda,\mathfrak p_\lambda)$, $S_\lambda$, $S'_\lambda$ with local homomorphisms
$R_\lambda\to S_\lambda\to S'_\lambda$, local transition maps, $S'_\lambda$-modules $M_\lambda$
and maps to $R,S,S',M$ with properties (1)-(5) of that node. Since $R_\lambda\to R$ is a local
homomorphism of local rings, $\mathfrak p_\lambda$ is the inverse image of $\mathfrak
m=\mathfrak m_R$ (the inverse image is a proper ideal containing the maximal ideal $\mathfrak
p_\lambda$); likewise $\mathfrak p_\lambda$ is the inverse image of $\mathfrak p_\mu$ under
$R_\lambda\to R_\mu$ for $\lambda\le\mu$.

4. (Noetherian local stages.) The ring $\mathbf Z$ is Noetherian [def-weil-pbc-noetherian-ring]
(every ideal is $n\mathbf Z$). If $T_0$ is a Noetherian ring and $T_1$ is essentially of finite
type over $T_0$ [def-weil-pbc-essentially-finite-type-algebra], i.e. $T_1\cong W^{-1}B$ with $B$
of finite type over $T_0$, then $B$ is Noetherian by
[lem-weil-pbc-finite-type-algebra-noetherian] and $W^{-1}B$ by
[lem-weil-pbc-localization-noetherian]. Applying this three times with property (2) of step 3:
$R_\lambda$, $S_\lambda$ and $S'_\lambda$ are Noetherian local rings. Put $\hat
S_\lambda=S_\lambda/\mathfrak p_\lambda S_\lambda$, $\hat S'_\lambda=S'_\lambda/\mathfrak
p_\lambda S'_\lambda$ and $\hat M_\lambda=M_\lambda/\mathfrak p_\lambda M_\lambda$. They are
Noetherian by [lem-weil-pbc-surjective-image-noetherian]; they are local, because $\mathfrak
p_\lambda S_\lambda$ lies in the maximal ideal $\mathfrak m_{S_\lambda}$ ($R_\lambda\to
S_\lambda$ is local), so $\hat S_\lambda\ne0$ and its ideals not containing $1$ lie in
$\mathfrak m_{S_\lambda}/\mathfrak p_\lambda S_\lambda$ (same for $S'_\lambda$). The maps
$S_\lambda\to S'_\lambda$, $S_\lambda\to S_\mu$, $S'_\lambda\to S'_\mu$, $M_\lambda\to M_\mu$
($\lambda\le\mu$) pass to the quotients, since $\mathfrak p_\lambda$ maps into $\mathfrak p_\mu$
(step 3), and the induced ring maps $\hat S_\lambda\to\hat S'_\lambda$, $\hat S_\lambda\to\hat
S_\mu$, $\hat S'_\lambda\to\hat S'_\mu$ are local homomorphisms; $\hat M_\lambda$ is a finitely
generated $\hat S'_\lambda$-module [def-weil-finitely-generated-module] (images of generators of
$M_\lambda$, property (3)).

5. ($S'_\lambda\otimes_{R_\lambda}R_\mu\to S'_\mu$ is a localization.) Let $\lambda\le\mu$ and
$E=S_\lambda\otimes_{R_\lambda}R_\mu$. By associativity of the tensor product,
$S'_\lambda\otimes_{R_\lambda}R_\mu\cong S'_\lambda\otimes_{S_\lambda}E$. By property (4) of
step 3, $E\to S_\mu$ is a localization at some $W\subseteq E$; by
[lem-weil-pbc-localization-base-change] (with the ring map $E\to
D:=S'_\lambda\otimes_{S_\lambda}E$), $D\to D\otimes_ES_\mu\cong
S'_\lambda\otimes_{S_\lambda}S_\mu$ is a localization at the image of $W$; and
$S'_\lambda\otimes_{S_\lambda}S_\mu\to S'_\mu$ is a localization by property (4). By
[lem-weil-pbc-localization-of-localization] (1) the composite
$S'_\lambda\otimes_{R_\lambda}R_\mu\to S'_\mu$, which is $x\otimes a\mapsto\bar x\,\bar a$, is a
localization at a multiplicative subset.

6. ($M_\lambda$ is flat over $R_\lambda$ for $\lambda$ large.) Apply
[lem-weil-pbc-colimit-eventually-flat] to the system $A_\lambda=R_\lambda$,
$B_\lambda=S'_\lambda$ (with the local homomorphism $R_\lambda\to S_\lambda\to S'_\lambda$),
$N_\lambda=M_\lambda$: the rings are Noetherian local (step 4), the transition maps local (step
3), $M_\lambda$ is finitely generated (property (3)), hypothesis (a) holds by step 5 and (b) by
property (4); by property (1) the colimits are $A=R$, $B=S'$ with the map $\beta\circ\alpha$,
and $N=M$ with its $S'$-module structure. Since $M$ is flat over $R$ (hypothesis (5)), there is
$\lambda_0$ with $M_{\lambda_0}$ flat over $R_{\lambda_0}$. For $\mu\ge\lambda_0$, step 2 (Claim
P) with $A=R_{\lambda_0}$, $A'=R_\mu$, $B=S'_{\lambda_0}$, $B'=S'_\mu$, $N=M_{\lambda_0}$,
$N'=M_\mu$ (hypotheses by step 5 and property (4)) shows that $M_\mu$ is flat over $R_\mu$.

7. (The fibre system.) (i) For $\lambda\le\mu$ the map $\hat S'_\lambda\otimes_{\hat
S_\lambda}\hat S_\mu\to\hat S'_\mu$ is a localization and $\hat M_\lambda\otimes_{\hat
S'_\lambda}\hat S'_\mu\to\hat M_\mu$ is an isomorphism (notation of step 4). Let
$C=S'_\lambda\otimes_{S_\lambda}S_\mu$. By [lem-weil-pbc-tensor-over-quotient-ring] (2) (ring
$S_\lambda$, ideal $\mathfrak p_\lambda S_\lambda$, module $S'_\lambda$, and the $\hat
S_\lambda$-module $\hat S_\mu$), $\hat S'_\lambda\otimes_{\hat S_\lambda}\hat S_\mu\cong
S'_\lambda\otimes_{S_\lambda}\hat S_\mu\cong C\otimes_{S_\mu}\hat S_\mu$, which is $C/\mathfrak
p_\mu C$ by part (1) of the same node. By property (4) of step 3, $C\to S'_\mu$ is a
localization at some $W$; by [lem-weil-pbc-localization-base-change] (ring map $C\to C/\mathfrak
p_\mu C$), $C/\mathfrak p_\mu C\to(C/\mathfrak p_\mu C)\otimes_CS'_\mu$ is a localization at the
image of $W$, and $(C/\mathfrak p_\mu C)\otimes_CS'_\mu\cong S'_\mu/\mathfrak p_\mu S'_\mu=\hat
S'_\mu$ by [lem-weil-pbc-tensor-over-quotient-ring] (1). These identifications are compatible
with the maps, so $\hat S'_\lambda\otimes_{\hat S_\lambda}\hat S_\mu\to\hat S'_\mu$ is a
localization. Likewise $\hat M_\lambda\otimes_{\hat S'_\lambda}\hat S'_\mu\cong
M_\lambda\otimes_{S'_\lambda}\hat S'_\mu\cong(M_\lambda\otimes_{S'_\lambda}S'_\mu)/\mathfrak
p_\mu(M_\lambda\otimes_{S'_\lambda}S'_\mu)\cong M_\mu/\mathfrak p_\mu M_\mu$ by the same node
(2), (1) and property (4). (ii) The maps $S_\lambda\to S\to S/\mathfrak mS$ kill $\mathfrak
p_\lambda S_\lambda$ (as $\mathfrak p_\lambda$ maps into $\mathfrak m$), giving a cocone $\hat
S_\lambda\to S/\mathfrak mS$; a colimit $L$ of the rings $\hat S_\lambda$ exists
[lem-weil-pbc-commutative-algebras-colimits-exist] and we show the induced map $\theta:L\to
S/\mathfrak mS$ is bijective, hence an isomorphism of rings. Surjective: every $s\in S$ is the
image of some $s_\lambda\in S_\lambda$ [lem-weil-pbc-filtered-colimit-algebras-elementwise] (2)
(over the base $\mathbf Z$). Injective: every element of $L$ is the image of some $s_\lambda\in
S_\lambda$ [lem-weil-pbc-filtered-colimit-algebras-elementwise]; if its image in $S$ is
$\sum_ia_it_i$ with $a_i\in\mathfrak m$, $t_i\in S$, choose $\mu\ge\lambda$ and $a_{i,\mu}\in
R_\mu$, $t_{i,\mu}\in S_\mu$ mapping to $a_i$, $t_i$; then $a_{i,\mu}\in\mathfrak p_\mu$ (step
3), and the image of $s_\lambda$ in $S_\mu$ and $\sum_ia_{i,\mu}t_{i,\mu}$ have the same image
in $S$, so by [lem-weil-pbc-filtered-colimit-rings-zero] they agree in some $S_\nu$,
$\nu\ge\mu$; thus $s_\lambda$ maps into $\mathfrak p_\nu S_\nu$, its image in $\hat S_\nu$ is
$0$, and so is its image in $L$. Hence $S/\mathfrak mS=\varinjlim\hat S_\lambda$. The same
argument gives $S'/\mathfrak mS'=\varinjlim\hat S'_\lambda$ and, with the colimit of abelian
groups [def-weil-directed-colimit-abelian-groups] and
[lem-weil-pbc-filtered-colimit-modules-elementwise] (over $\mathbf Z$) in place of the ring
statements, $M/\mathfrak mM=\varinjlim\hat M_\lambda$; the induced map $S/\mathfrak mS\to
S'/\mathfrak mS'$ and the module structure of $M/\mathfrak mM$ are the colimit ones, since they
are induced by the maps of the stages.

8. ($\hat M_\lambda$ is flat over $\hat S_\lambda$ for $\lambda$ large.) Apply
[lem-weil-pbc-colimit-eventually-flat] to the system $A_\lambda=\hat S_\lambda$, $B_\lambda=\hat
S'_\lambda$, $N_\lambda=\hat M_\lambda$: Noetherian local rings, local maps and finitely
generated modules by step 4; hypotheses (a), (b) by step 7 (i); colimits $A=S/\mathfrak mS$,
$B=S'/\mathfrak mS'$, $N=M/\mathfrak mM$ by step 7 (ii). Since $M/\mathfrak mM$ is flat over
$S/\mathfrak mS$ (hypothesis (4)), there is $\lambda_1$ with $\hat M_{\lambda_1}$ flat over
$\hat S_{\lambda_1}$. For $\mu\ge\lambda_1$, step 2 (Claim P) with $A=\hat S_{\lambda_1}$,
$A'=\hat S_\mu$, $B=\hat S'_{\lambda_1}$, $B'=\hat S'_\mu$, $N=\hat M_{\lambda_1}$, $N'=\hat
M_\mu$ (hypotheses by step 7 (i)) shows that $\hat M_\mu$ is flat over $\hat S_\mu$.

9. (The Noetherian case at one stage.) As $\Lambda$ is directed, choose
$\lambda\ge\lambda_0,\lambda_1$. Apply [lem-weil-pbc-criterion-flatness-fibre-noetherian]
(Stacks 00MP) to the local homomorphisms of Noetherian local rings $R_\lambda\to S_\lambda\to
S'_\lambda$ (step 4) and the $S'_\lambda$-module $M_\lambda$, with maximal ideal $\mathfrak
p_\lambda$ of $R_\lambda$: (1) $M_\lambda$ is finitely generated (property (3)); (2)
$M_\lambda\ne0$, for otherwise $M\cong M_\lambda\otimes_{S'_\lambda}S'=0$ (property (5)),
contradicting hypothesis (3); (3) $M_\lambda/\mathfrak p_\lambda M_\lambda=\hat M_\lambda$ is
flat over $S_\lambda/\mathfrak p_\lambda S_\lambda=\hat S_\lambda$ (step 8); (4) $M_\lambda$ is
flat over $R_\lambda$ (step 6). Hence $S_\lambda$ is flat over $R_\lambda$ and $M_\lambda$ is a
flat $S_\lambda$-module.

10. ($S$ is flat over $R$.) Apply step 2 (Claim P) with $A=R_\lambda$, $A'=R$, $B=S_\lambda$,
$B'=S$ (the maps $S_\lambda\to S$ and $\alpha:R\to S$ agree on $R_\lambda$), $N=S_\lambda$, flat
over $R_\lambda$ by step 9, and $N'=S$ with the map $S_\lambda\to S$
($S_\lambda\otimes_{S_\lambda}S\to S$ is the canonical isomorphism). Its hypothesis that
$S_\lambda\otimes_{R_\lambda}R\to S$ is a localization is property (5) of step 3
[lem-weil-pbc-limit-tower-essentially-finite-presentation]. Hence $S$ is a flat $R$-module, i.e.
$\alpha$ is flat [def-weil-pbc-flat-ring-map].

11. ($M$ is flat over $S$.) Apply step 2 (Claim P) with $A=S_\lambda$, $A'=S$, $B=S'_\lambda$,
$B'=S'$ (the maps $S'_\lambda\to S'$ and $\beta$ agree on $S_\lambda$), $N=M_\lambda$, flat over
$S_\lambda$ by step 9, and $N'=M$ with the map $M_\lambda\to M$; its hypotheses, that
$S'_\lambda\otimes_{S_\lambda}S\to S'$ is a localization and $M_\lambda\otimes_{S'_\lambda}S'\to
M$ an isomorphism, are property (5) of step 3
[lem-weil-pbc-limit-tower-essentially-finite-presentation]. Hence $M$, an $S$-module through
$\beta$, is a flat $S$-module [def-weil-pbc-flat-ring-map].
-/
theorem flat_of_flat_closedFiber
    (R : Type u) (S : Type v) (S' : Type w) (M : Type t)
    [CommRing R] [CommRing S] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S S')]
    [AddCommGroup M] [Module S' M] [Module S M] [Module R M]
    [IsScalarTower S S' M] [IsScalarTower R S M]
    (P : Type p) (Q : Type q) [CommRing P] [CommRing Q]
    [Algebra R P] [Algebra P S] [IsScalarTower R P S]
    [Algebra R Q] [Algebra Q S'] [IsScalarTower R Q S']
    [Algebra.FinitePresentation R P] [Algebra.FinitePresentation R Q]
    (W : Submonoid P) (V : Submonoid Q) [IsLocalization W S] [IsLocalization V S']
    [Module.FinitePresentation S' M] [Nontrivial M]
    (h_fibre : Module.Flat
      (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
      ((S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) ⊗[S] M))
    [Module.Flat R M] : Module.Flat R S ∧ Module.Flat S M := by
  obtain ⟨R₀, S₀, T₀, N₀,
    instR₀, instS₀, instT₀, locR₀, locS₀, locT₀, noethR₀, noethS₀, noethT₀,
    algRS₀, algST₀, algRT₀, towerRST₀, localRS₀, localST₀,
    groupN₀, modTN₀, modSN₀, modRN₀, towerSTN₀, towerRSN₀, algR₀R, algS₀S,
    hfinite, hbase, hfibre, ⟨U, ⟨eS⟩⟩, hM⟩ :=
    exists_noetherian_flat_closedFiber_model R S S' M P Q W V h_fibre
  have : Module.Finite T₀ N₀ := hfinite
  obtain ⟨modCN₀, towerSCN₀, V₀, ⟨eM⟩⟩ := hM
  have : Nontrivial N₀ := by
    by_contra h
    have : Subsingleton N₀ := not_nontrivial_iff_subsingleton.mp h
    have : Subsingleton (LocalizedModule V₀ (S ⊗[S₀] N₀)) := inferInstance
    exact not_subsingleton M (eM.symm.injective.subsingleton)
  have : Module.Flat R₀ N₀ := hbase
  obtain ⟨hS₀, hN₀⟩ := flat_and_flat_of_flat_fibre_noetherian R₀ S₀ T₀ N₀ hfibre
  have : Module.Flat R₀ S₀ := hS₀
  have : Module.Flat S₀ N₀ := hN₀
  have hRS : Module.Flat R (R ⊗[R₀] S₀) := inferInstance
  have hlocS : Module.Flat R (LocalizedModule U (R ⊗[R₀] S₀)) :=
    Flat.localizedModule_of_algebra U hRS
  have hS : Module.Flat R S := (Flat.equiv_iff eS).mp hlocS
  have hSN : Module.Flat S (S ⊗[S₀] N₀) := inferInstance
  have hlocM : Module.Flat S (LocalizedModule V₀ (S ⊗[S₀] N₀)) :=
    Flat.localizedModule_of_algebra V₀ hSN
  exact ⟨hS, (Flat.equiv_iff eM).mp hlocM⟩

end Module
