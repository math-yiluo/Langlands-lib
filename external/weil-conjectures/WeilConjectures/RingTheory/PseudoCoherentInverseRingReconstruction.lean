/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRings
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.RingTheory.RingPseudoCoherent
import WeilConjectures.RingTheory.PseudoCoherentInverseRingReconstructionModels

/-!
# Pseudo-coherent reconstruction over a tower of nilpotent quotients

Source: Stacks Project, More on Algebra, Tag 0CQF,
lemma-Rlim-pseudo-coherent-gives-pseudo-coherent
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- Reconstruction of a compatible pseudo-coherent tower, including its finite-free models.
The index `0` denotes the paper's index `1`. The ring-limit universal property in `hlim`
is the compatible-tuple construction, invariant under its unique ring isomorphism.
The left adjoints `L` and `M` of derived restriction of scalars denote derived tensor.
The normalization `hχ` specifies the canonical composition of restrictions. The maps
`η` and the equation for `γ` identify ordinary and derived tensor on the free model,
so the last equality identifies the actual projection-induced comparison maps.

Source: Stacks Project, More on Algebra, Tag 0CQF
(auxiliary; not a blueprint node).

Proof, following the node's six steps:

1. Induct on $n$ to show that every $E_n$ is pseudo-coherent. The base $n=1$ is assumed. At the
induction step apply nilpotent invariance to $A_{n+1}\twoheadrightarrow A_n$ and $E_{n+1}$: its
derived reduction is isomorphic to $E_n$ by the specified transition. Thus the pseudo-coherence of
$E_n$ implies that of $E_{n+1}$. Choose a bounded-above finite-free representative $P_1^\bullet$
of $E_1$, an isomorphism $\beta_1:Q(P_1^\bullet)\xrightarrow{\sim}E_1$, and an integer $b$ above
which it is zero.

2. Suppose $P_n$, $\beta_n$, and the transitions through level $n$ have been chosen, with
$P_n^i=0$ for $i>b$. Set $I=\ker(A_{n+1}\to A_n)$. If $I^N=0$, each $1+x$ with $x\in I$ has
inverse $\sum_{j=0}^{N-1}(-x)^j$. Apply marked free-complex lifting to $R=A_{n+1}$, $R/I=A_n$,
$K=E_{n+1}$, $F=P_n$, and the specified isomorphism $\alpha=\beta_n^{-1}\circ\overline
t_n:E_{n+1}\otimes^L_{A_{n+1}}A_n\xrightarrow{\sim}Q(P_n)$, where $\overline t_n$ is induced by
$t_n$. This gives $P_{n+1}$ zero above the same $b$, $\beta_{n+1}$, and
$\theta_n:P_{n+1}\otimes_{A_{n+1}}A_n\xrightarrow{\sim}P_n$, with
$Q(\theta_n)=\beta_n^{-1}\overline t_n(\beta_{n+1}\otimes^L A_n)$. Define $u_n:P_{n+1}\to P_n$ as
the quotient map followed by $\theta_n$. It is a chain map, degreewise surjective, and the marking
equation says that it represents the given transition $t_n$ under the $\beta$'s. Repeating this
induction constructs the entire strictly compatible complex tower.

3. Construct compatible finite bases separately in each degree $i$. Choose a basis of $P_1^i$ of
size $r_i$. Given the basis at level $n$, lift its vectors through the surjection $u_n^i$ to
$P_{n+1}^i$. They form a basis: put $R=A_{n+1}$ and let $f:R^{r_i}\to P_{n+1}^i$ send the standard
vectors to these lifts. Its reduction modulo $I$ is an isomorphism. Since $P_{n+1}^i$ is finite
free, lift the matrix of the inverse reduced map to an $R$-linear $g:P_{n+1}^i\to R^{r_i}$. Both
$gf-1$ and $fg-1$ have matrices in $I$; their $N$th powers vanish, so geometric sums invert $gf$
and $fg$. Consequently $f$ has a left inverse $(gf)^{-1}g$ and a right inverse $g(fg)^{-1}$; these
coincide, and $f$ is an isomorphism. This also covers $r_i=0$. The bases so constructed make
$u_n^i$ the coordinatewise ring reduction $A_{n+1}^{r_i}\to A_n^{r_i}$.

4. Let $P^i=\varprojlim_n P_n^i$, with differential $(x_n)\mapsto(d_nx_n)$; compatibility follows
from $u_nd_{n+1}=d_nu_n$, and $d^2=0$ holds coordinatewise. In the compatible bases of step 3, a
compatible vector tuple is exactly $r_i$ compatible scalar tuples, so $P^i\cong(\varprojlim_n
A_n)^{r_i}=A^{r_i}$. All $P^i$ vanish for $i>b$. Projection is coordinatewise $A^{r_i}\to
A_n^{r_i}$. Therefore $P^i\otimes_A A_n\to P_n^i$, $(x_m)_m\otimes a\mapsto ax_n$, is an
isomorphism. Its inverse in these bases sends the $j$th standard vector to the compatible $j$th
basis tuple tensor $1$. The projections commute with differentials, so these degreewise maps
assemble into chain isomorphisms $P^\bullet\otimes_A A_n\xrightarrow{\sim}P_n^\bullet$.

5. Restrict all $P_n$ to $A$. The maps $u_n$ are degreewise surjective, so the surjective module-
complex tower lemma identifies $Q(P)$, with its literal projections, as a derived limit of
$(Q(P_n),Q(u_n))$ in $D(A)$. The compatible isomorphisms $\beta_n$ identify this system with
$(E_n,t_n)$; the induced isomorphism of products is obtained componentwise, with inverse the
product of the $\beta_n^{-1}$. It conjugates $1-s$ to $1-s$ because
$\beta_nQ(u_n)=t_n\beta_{n+1}$. Write $B_P=\prod_nQ(P_n)$, $B_E=\prod_nE_n$,
$v=\prod_n\beta_n:B_P\xrightarrow{\sim}B_E$, and let $j:Q(P)\to B_P$ and $\delta_P:B_P\to Q(P)[1]$
be the arrows of its Roos triangle. The triangle
$Q(P)\xrightarrow{vj}B_E\xrightarrow{1-s}B_E\xrightarrow{\delta_Pv^{-1}}Q(P)[1]$ is isomorphic to
that triangle by $(1,v,v)$: the first square is $vj=vj$, the second is $v(1-s)=(1-s)v$, and the
last is $(\delta_Pv^{-1})v=\delta_P$. Thus TR1 makes it distinguished, with projections
$\beta_nQ(P\to P_n)$. Compare with the chosen Roos triangle defining $E$: rotate both triangles so
$1-s$ is their first arrow, use TR3 with identities on the two product objects, and rotate back.
The triangle isomorphism lemma makes the resulting map $Q(P)\to E$ an isomorphism. The first
square says it respects every projection. No canonical choice of this isomorphism is asserted.

6. A finite free module is flat: its tensor functor is a finite direct sum of the identity
functor, hence preserves exact sequences componentwise. Thus the bounded-above complexes $P$ over
$A$ and $P_n$ over $A_n$ are K-flat by the bounded-flat K-flat criterion. On the category with one
object and only its identity morphism, a presheaf is its value at that object and the identity-
cover sheaf condition imposes no restriction. Ring sheaves, module sheaves, their complexes and
tensor products are therefore ordinary rings, modules, complexes and tensor products. Derived
change of rings on this site computes $Q(P)\otimes_A^L A_n$ by the ordinary tensor complex
$P\otimes_A A_n$. Under the projection-respecting isomorphism in step 5, the projection-induced
comparison is represented by the chain map $P\otimes_A A_n\to P_n$, $x\otimes a\mapsto
a\,\mathrm{pr}_n(x)$, followed by $\beta_n$. To justify that this is the specified derived map,
use the scalar-extension Hom bijection degreewise: $f:P\to P_n$ corresponds to $\widetilde
f:P\otimes_A A_n\to P_n$, $\widetilde f(x\otimes a)=af(x)$. The chain-map equations correspond
under this bijection by evaluating on $x\otimes1$, and a homotopy $h$ corresponds to $\widetilde
h(x\otimes a)=ah(x)$, since $d\widetilde h+\widetilde h d$ is the transpose of $dh+hd$. Hence it
is a bijection on homotopy classes. Every finite free module is projective: lift a map through a
surjection by choosing a preimage for each basis vector. Both $P$ over $A$ and $P\otimes_A A_n$
over $A_n$ are bounded above projective. The derived-map-representative lemma identifies both
homotopy Hom sets with their derived Hom sets. We therefore obtain a bijection
$\operatorname{Hom}_{D(A_n)}(Q(P\otimes_A
A_n),Q(P_n))\cong\operatorname{Hom}_{D(A)}(Q(P),Q(P_n))$, computed by composition with $x\mapsto
x\otimes1$. In particular the transpose of the projection is exactly the displayed chain map.
Composing with the markings and the projection-respecting isomorphism of step 5 gives precisely
the projection-induced derived comparison. This calculation also justifies the transition-map
representation from the marking equation in step 2, with $A_{n+1}\to A_n$ in place of $A\to A_n$.
Step 4 proves this chain map is an isomorphism, so the derived comparison is an isomorphism.
Finally $P$ is bounded above finite free by step 4 and represents $E$ by step 5, which proves
pseudo-coherence by its definition and all the more precise clauses.
-/
theorem isPseudoCoherent_inverse_ring_reconstruction
    (R : ℕ → Type u) [∀ n, CommRing (R n)]
    (φ : ∀ n, R (n + 1) →+* R n)
    (hsurj : ∀ n, Function.Surjective (φ n))
    (hnil : ∀ n, IsNilpotent (RingHom.ker (φ n)))
    (A : Type u) [CommRing A] (q : ∀ n, A →+* R n)
    (hq : ∀ n, q n = (φ n).comp (q (n + 1)))
    (hlim : ∀ x : ∀ n, R n, (∀ n, φ n (x (n + 1)) = x n) →
      ∃! a : A, ∀ n, q n a = x n)
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    [∀ n, HasDerivedCategory.{w} (ModuleCat.{max u v} (R n))]
    (L : ∀ n, DerivedCategory (ModuleCat.{max u v} (R (n + 1))) ⥤
      DerivedCategory (ModuleCat.{max u v} (R n)))
    (adjφ : ∀ n, L n ⊣ (ModuleCat.restrictScalars (φ n)).mapDerivedCategory)
    (M : ∀ n, DerivedCategory (ModuleCat.{max u v} A) ⥤
      DerivedCategory (ModuleCat.{max u v} (R n)))
    (adjq : ∀ n, M n ⊣ (ModuleCat.restrictScalars (q n)).mapDerivedCategory)
    (χ : ∀ n, (ModuleCat.restrictScalars (q n)).mapDerivedCategory ≅
      (ModuleCat.restrictScalars (φ n)).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory)
    (hχ : ∀ n (C : CochainComplex (ModuleCat.{max u v} (R n)) ℤ),
      (χ n).hom.app (Q.obj C) ≫
        (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory.map
          ((ModuleCat.restrictScalars (φ n)).mapDerivedCategoryFactors.hom.app C) ≫
        (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.restrictScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj C) =
      (ModuleCat.restrictScalars (q n)).mapDerivedCategoryFactors.hom.app C ≫
        Q.map ((NatIso.mapHomologicalComplex
          (ModuleCat.restrictScalarsComp' (q (n + 1)) (φ n) (q n) (hq n))
          (.up ℤ)).hom.app C))
    (Eₙ : ∀ n, DerivedCategory (ModuleCat.{max u v} (R n)))
    (t : ∀ n, Eₙ (n + 1) ⟶
      (ModuleCat.restrictScalars (φ n)).mapDerivedCategory.obj (Eₙ n))
    (hred : ∀ n, IsIso (((adjφ n).homEquiv (Eₙ (n + 1)) (Eₙ n)).symm (t n)))
    (hpc : IsPseudoCoherent (Eₙ 0))
    [HasProduct (fun n ↦ (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (Eₙ n))]
    (E : DerivedCategory (ModuleCat.{max u v} A))
    (pE : E ⟶ ∏ᶜ fun n ↦
      (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (Eₙ n))
    (δ : (∏ᶜ fun n ↦ (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (Eₙ n)) ⟶
      E⟦(1 : ℤ)⟧)
    (hE : IsDerivedLimitTriangle
      (fun n ↦ (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory.map (t n) ≫
        (χ n).inv.app (Eₙ n)) E pE δ) :
    IsPseudoCoherent E ∧
    (∀ n, IsIso (((adjq n).homEquiv E (Eₙ n)).symm (pE ≫ Pi.π _ n))) ∧
    ∃ (Pₙ : ∀ n, CochainComplex (ModuleCat.{max u v} (R n)) ℤ)
      (b : ℤ) (βₙ : ∀ n, Q.obj (Pₙ n) ≅ Eₙ n)
      (uₙ : ∀ n, Pₙ (n + 1) ⟶
        ((ModuleCat.restrictScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj (Pₙ n))
      (θₙ : ∀ n, ((ModuleCat.extendScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj
        (Pₙ (n + 1)) ≅ Pₙ n)
      (P : CochainComplex (ModuleCat.{max u v} A) ℤ) (β : Q.obj P ≅ E)
      (p : ∀ n, P ⟶
        ((ModuleCat.restrictScalars (q n)).mapHomologicalComplex (.up ℤ)).obj (Pₙ n))
      (θ : ∀ n, ((ModuleCat.extendScalars (q n)).mapHomologicalComplex (.up ℤ)).obj P ≅ Pₙ n)
      (η : ∀ n, P ⟶ ((ModuleCat.restrictScalars (q n)).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars (q n)).mapHomologicalComplex (.up ℤ)).obj P))
      (γ : ∀ n, (M n).obj (Q.obj P) ≅
        Q.obj (((ModuleCat.extendScalars (q n)).mapHomologicalComplex (.up ℤ)).obj P)),
      (∀ n, (Pₙ n).IsStrictlyLE b) ∧
      (∀ n i, Module.Free (R n) ((Pₙ n).X i) ∧ Module.Finite (R n) ((Pₙ n).X i)) ∧
      (∀ n i, Function.Surjective ((uₙ n).f i)) ∧
      (∀ n i, ((ModuleCat.extendRestrictScalarsAdj (φ n)).homEquiv
        ((Pₙ (n + 1)).X i) ((Pₙ n).X i) ((θₙ n).hom.f i)) = (uₙ n).f i) ∧
      (∀ n, Q.map (uₙ n) = (βₙ (n + 1)).hom ≫ t n ≫
        (ModuleCat.restrictScalars (φ n)).mapDerivedCategory.map (βₙ n).inv ≫
        (ModuleCat.restrictScalars (φ n)).mapDerivedCategoryFactors.hom.app (Pₙ n)) ∧
      P.IsStrictlyLE b ∧
      (∀ i, Module.Free A (P.X i) ∧ Module.Finite A (P.X i)) ∧
      (∀ n i (y : P.X i), (uₙ n).f i ((p (n + 1)).f i y) = (p n).f i y) ∧
      (∀ i (x : ∀ n, (Pₙ n).X i), (∀ n, (uₙ n).f i (x (n + 1)) = x n) →
        ∃! y : P.X i, ∀ n, (p n).f i y = x n) ∧
      (∀ n, Q.map (p n) ≫
        (ModuleCat.restrictScalars (q n)).mapDerivedCategoryFactors.inv.app (Pₙ n) ≫
        (ModuleCat.restrictScalars (q n)).mapDerivedCategory.map (βₙ n).hom =
        β.hom ≫ pE ≫ Pi.π _ n) ∧
      (∀ n i, ((ModuleCat.extendRestrictScalarsAdj (q n)).homEquiv
        (P.X i) ((Pₙ n).X i) ((θ n).hom.f i)) = (p n).f i) ∧
      (∀ n i, (η n).f i = (ModuleCat.extendRestrictScalarsAdj (q n)).unit.app (P.X i)) ∧
      (∀ n, (adjq n).unit.app (Q.obj P) ≫
        (ModuleCat.restrictScalars (q n)).mapDerivedCategory.map (γ n).hom ≫
        (ModuleCat.restrictScalars (q n)).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars (q n)).mapHomologicalComplex (.up ℤ)).obj P) =
        Q.map (η n)) ∧
      (∀ n, (γ n).hom ≫ Q.map (θ n).hom ≫ (βₙ n).hom =
        (M n).map β.hom ≫ ((adjq n).homEquiv E (Eₙ n)).symm (pE ≫ Pi.π _ n)) := by
  have hm := reconstruction_models (R := R) (φ := φ) (hsurj := hsurj) (hnil := hnil)
    (A := A) (q := q) (hq := hq) (hlim := hlim) (L := L) (adjφ := adjφ) (M := M)
    (adjq := adjq) (χ := χ) (hχ := hχ) (Eₙ := Eₙ) (t := t) (hred := hred)
    (hpc := hpc) (E := E) (pE := pE) (δ := δ) (hE := hE)
  obtain ⟨Pₙ, b, βₙ, uₙ, θₙ, P, β, p, θ, η, γ, hdata⟩ := hm
  rcases hdata with ⟨hboundₙ, hfreeₙ, hsurjₙ, hθₙ, huₙ, hPbound, hPfree,
    hproj, hlimP, hcomparison, hθ, hη, hγ, hfinal⟩
  have hpcE : IsPseudoCoherent E := ⟨P, b, hPbound, hPfree, ⟨β⟩⟩
  have hIso (n : ℕ) : IsIso (((adjq n).homEquiv E (Eₙ n)).symm (pE ≫ Pi.π _ n)) := by
    let f := ((adjq n).homEquiv E (Eₙ n)).symm (pE ≫ Pi.π _ n)
    have hi : IsIso ((M n).map β.hom ≫ f) := by
      rw [← hfinal n]
      infer_instance
    set_option linter.style.haveILetI false in
      letI : IsIso ((M n).map β.hom ≫ f) := hi
    exact IsIso.of_isIso_comp_left ((M n).map β.hom) f
  exact ⟨hpcE, hIso, ⟨Pₙ, b, βₙ, uₙ, θₙ, P, β, p, θ, η, γ,
    ⟨hboundₙ, hfreeₙ, hsurjₙ, hθₙ, huₙ, hPbound, hPfree, hproj, hlimP,
      hcomparison, hθ, hη, hγ, hfinal⟩⟩⟩

end DerivedCategory
