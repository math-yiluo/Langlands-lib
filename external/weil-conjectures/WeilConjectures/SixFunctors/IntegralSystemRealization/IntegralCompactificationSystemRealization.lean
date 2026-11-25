/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationRealizationData
import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralCanonicalAmbientModels
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralComparisonRecursionLaws
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralExpressionCoefficientSquares
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionReductionModel

/-! # Coherent integral realization of compactification expressions

Source: Stacks 0941; blueprint fix-prop-coherence, all seven realization-proof steps
(blueprint: lem-sf-integral-compactification-system-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
namespace IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField
  WeilConjectures.integralDerivedPullback WeilConjectures.integralCompletedTensor
  WeilConjectures.pullbackTensorCalculus

private theorem good_counit_isIso (W : Scheme.{u}) (M : System l E W)
    (h : Good l E W M) : IsIso ((calculus l E W).adjunction.counit.app M) := by
  exact normalizedSequence_counit_isIso l E W (calculus l E W)
    M h.1

private theorem reduction_normalization
    {C N A : Type*} [Category C] [Category N] [Category A]
    {R : C ⥤ N} {L : N ⥤ C} (adj : R ⊣ L)
    (F : A ⥤ N) (G : A ⥤ C) (c : F ⋙ L ≅ G)
    (he : ∀ X : A, IsIso (adj.counit.app (F.obj X))) :
    ∃ r : F ≅ G ⋙ R, ∀ X : A,
      R.map (c.hom.app X) ≫ r.inv.app X = adj.counit.app (F.obj X) := by
  let e : (F ⋙ L) ⋙ R ≅ F :=
    NatIso.ofComponents (fun X ↦ @asIso _ _ _ _ (adj.counit.app (F.obj X)) (he X))
      (fun f ↦ adj.counit.naturality (F.map f))
  refine ⟨e.symm ≪≫ Functor.isoWhiskerRight c R, ?_⟩
  intro X
  change R.map (c.hom.app X) ≫ (R.map (c.inv.app X) ≫ _) = _
  rw [← Category.assoc, ← R.map_comp, c.hom_inv_id_app, R.map_id, Category.id_comp]
  rfl

private theorem coefficient_intertwining
    {C N : Type*} [Category C] [Category N]
    {R : C ⥤ N} {L : N ⥤ C} (adj : R ⊣ L)
    {M N₀ : N} {X Y : C} (c : L.obj M ≅ X) (d : L.obj N₀ ≅ Y)
    (s : M ⟶ N₀) (t : X ⟶ Y)
    (h : R.map c.inv ≫ adj.counit.app M ≫ s =
      R.map t ≫ R.map d.inv ≫ adj.counit.app N₀) :
    L.map s ≫ d.hom = c.hom ≫ t := by
  apply (cancel_epi c.inv).mp
  apply (cancel_mono d.inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.inv_hom_id_assoc]
  apply (adj.homEquiv X N₀).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hn := adj.counit.naturality s
  change R.map (L.map s) ≫ adj.counit.app N₀ = adj.counit.app M ≫ s at hn
  rw [hn]
  exact h

/-- Coherent integral realization of compactification expressions and their maps.
Source: Stacks 0941; blueprint fix-prop-coherence
(blueprint: lem-sf-integral-compactification-system-realization).

Proof:

1. Use the simultaneous semilinear-section models of [lem-coef-semilinear-derived-sections] for
the operations in the statement. In particular pullback, tensor, open extension, direct image,
their adjunctions and coefficient comparisons are constructions on one derived system category,
including their morphisms. The evaluated adjunctions are those of
[lem-pur-coefficient-system-derived-comparison]. Write $u:1\to\mathcal L\mathcal R$ and
$e:\mathcal R\mathcal L\to1$ for the actual unit and counit of
[lem-coef-derived-system-evaluation-calculus]. If $N$ is normalized,
[lemma-sp-tower-adjunction-foundation--2] identifies each $e_{N,n}$ with an isomorphism, the
scalar-extension adjoint of the total-limit projection. Since derived evaluations detect
isomorphisms, $e_N$ itself is an isomorphism of semilinear systems. This uses detection of
isomorphisms only. The limit $\mathcal L N$ is derived complete, and its reductions have precisely
the constructibility and common bounds of $N$, by the same counit isomorphisms and
[def-weil-derived-complete-integral-detailed].  For a derived-complete input $K$,
[def-weil-derived-complete] gives an isomorphism $K\cong\mathcal L\mathcal R K$: its Roos triangle
and the canonical total-limit Roos triangle are triangles of the same reduction tower. This
existence statement alone does not identify that isomorphism with $u_K$. Instead, the adjunction
identity $\mathcal L(e_N)\circ u_{\mathcal L N}=1$, with $e_N$ invertible, proves that
$u_{\mathcal L N}$ is invertible. Take $N=\mathcal R K$, which is normalized by derived tensor
reassociation, and use naturality of $u$ along the preceding isomorphism to conclude that the
specified $u_K$ is invertible. Thus on the complete/normalized domains we have the specific
inverse equivalence with unit $u$ and counit $e$. No arbitrary choice of a morphism between Roos
triangles defines a comparison.

2. Apply [lem-sf-semilinear-proper-open-mate-pasting] to the inverse ring sequence $C_n=A_n$. Its
intrinsic clopen projection gives $\alpha_Q$, its proper mate $\Gamma_Q$, and the specific
open-restriction isomorphism $\lambda_Q$; thus $\lambda_QP_i\Gamma_Q=1$. The geometry, properness
and quasi-compact open hypotheses are exactly those of the square under consideration. Its
scalar-restriction clause, with $B=R$ and the quotient maps $R\to A_n$, identifies this mate with
the normalized constant-$R$ tower map of [lem-cbc-strict-tower-proper-open-calculus]. The bounded
constructible etale-origin levels satisfy that node's finite evaluation hypothesis. All quotient
transitions are retained by these constructions.  The same new lemma gives horizontal, vertical,
base-change, identity and refinement pasting as identities inside $D(\mathscr S)$. In particular
its assertion is stronger than merely observing these equations after scalar restriction. These
are the proper/open generators and equations required below; the remaining projection and exchange
maps are their specified composites with tensor comparisons, units and counits
[def-exchange-projection].

3. For a basic operation $A$, first specify $d_A(K):\mathcal L A\mathcal R
K\xrightarrow{\sim}A_{\mathrm{int}}K$ (with two inputs for tensor). For $P_v$ and tensor these are
the identifications with the strict reduction-tower formulas of
[def-pur-integral-derived-operations, lem-pur-integral-operations-well-defined]: the total limit
$\mathcal L_W$ of a strict tower and the cone model $\operatorname{Cone}(1-s)[-1]$ on termwise
products are identified by the natural Roos triangle of
[lem-weil-pbc-ringed-strict-tower-homotopy-limit], the termwise products representing the derived
products; the simultaneous models ensure agreement on morphisms and transitions, not merely on
evaluated objects. For $S_p$ use the proper direct-image reduction-tower formula of
[prose-03-02]. For $S_pJ_j$, [lem-sf-compact-support-restriction-of-scalars]
gives the transition from $m$ to $n$: apply $Rp_{*,m}j_!$ to $K_m\to\operatorname{Res}_{m,n}K_n$,
then its coefficient-restriction isomorphism. These are exactly the transitions in
[def-weil-integral-rational-qbar-compact-support]. The simultaneous system construction and its
total limit therefore give $d_{S_pJ_j}$ to precisely that functor, including its maps.  For
standalone open extension apply [lem-sf-integral-open-reduction-comparison]. It supplies the
actual strict map $r_j$, completeness, and $d_{J_j}=u_{j_!K}^{-1}\mathcal L(r_j)^{-1}$ with the
localized ringed-site open adjunction. Its quasi-compactness hypothesis holds for these opens. The
common bounds remain the expressly assumed bounds of every intermediate system.

4. Define the comparisons by a genuine induction on expression trees. For a variable $K_i$ put
$c_{K_i}=u_{K_i}^{-1}$. For a normalized system $M$ at the source of a unary operation $A$, set
$$a_A(M)=d_A(\mathcal L M)\circ\bigl(\mathcal L A(e_M)\bigr)^{-1}:\mathcal L A M\longrightarrow
A_{\mathrm{int}}\mathcal L M.$$ For tensor use $$a_\otimes(M,N)=d_\otimes(\mathcal L M,\mathcal L
N)\circ\bigl(\mathcal L(e_M\otimes^L e_N)\bigr)^{-1}.$$ The inverses exist by step 1. If
$M=V(\mathcal R K_1,\ldots,\mathcal R K_s)$, define $c_{AV}=A_{\mathrm{int}}(c_V)\circ a_A(M)$. If
$M=V(\mathcal R K_i)$ and $N=T(\mathcal R K_i)$, define $c_{V\otimes
T}=(c_V\widehat\otimes^Lc_T)\circ a_\otimes(M,N)$. These formulas cover every unary and binary
node and decrease tree size at every invocation. Their sources and targets are the stated ones,
and each factor is natural and invertible. The induction is legitimate because every intermediate
system is assumed normalized, with compatible etale-origin witnesses and common finite
cohomological and Tor intervals.  The direct identification $d_{S_pJ_j}$ of step 3 agrees with the
recursive composite for $S_p(J_j(-))$. Indeed $r_j$ identifies $\mathcal R(j_!K)$ with
$J_j\mathcal R K$ on the very same quotient tower, and the recursion inserts $e_{J_j\mathcal R
K}^{-1}$. In the composite the adjacent $\mathcal R\mathcal L$ insertion cancels by $e_{\mathcal R
K}\circ\mathcal R(u_K)=1$ and naturality of $e$; the remaining tower is $S_pJ_j\mathcal R K$ with
the transitions specified in step 3. The total-limit and resolution comparisons of
[lem-coef-derived-system-evaluation-calculus, lem-coef-semilinear-derived-sections] make this an
equality of the prescribed comparisons. In particular the recursion does not replace the
compact-support definition by an unrelated isomorphic functor.

5. For each basic operation the actual coefficient map is $$r_A=e_{A\mathcal R K_i}\circ\mathcal
R(d_A^{-1})$$ by [lem-sf-generator-reduction-coherence]; the two-input formula holds for tensor.
Its hypotheses hold because all inputs and intermediate systems are normalized and satisfy the
stated origin and common bounds. Substitute these basic maps along a finite expression tree to
define $r_V$. Induction on tree size using step 4, naturality of $e$ and $e_{\mathcal R K}\mathcal
R(u_K)=1$ gives $$r_V=e_{V(\mathcal R K_i)}\circ\mathcal R(c_V^{-1}).$$ The base case is
$r_{K_i}=1$ by that triangle identity; for a unary node naturality moves the inner comparison past
$e$, and for a tensor node the same substitution applies in both slots.  For every basic generator
$\tau:V\to T$, the same lemma supplies the system square $$\tau_{\mathcal R K_i}r_V=r_T\mathcal
R(\tau_{\rm int}).$$ It covers the normalized open maps and proper/open interchange as well as
tensor, pullback and adjunction generators, before evaluation. Projection and exchange are the
composites prescribed by [def-exchange-projection]; paste the squares for their factors. The
tensor/square identifications in these composites are those of
[lem-weil-pbc-ringed-exchange-tensor-coherence].  Apply $\mathcal L$ to this square and substitute
the displayed expression for $r_V,r_T$. Naturality of $u$ and $\mathcal L(e_N)u_{\mathcal LN}=1$
cancel the outer unit/counit factors, giving $$c_T\circ\mathcal L(\tau_{\mathcal R K_i})=\tau_{\rm
int}\circ c_V.$$ This establishes the generator intertwining equation. Extension to arbitrary
outer expression contexts is the separate induction in step 6.

6. The generator equation remains true under every allowed expression context. For a unary outer
operation $A$, insert the two equations defining $c_{AV}$ and $c_{AT}$ from step 4 and use
naturality of $a_A$ at $\tau:V\to T$; the middle square is precisely $A_{\mathrm{int}}$ of the
equation in step 5. For tensor with a second expression use naturality of $a_\otimes$ in the
chosen slot; if both slots change, factor the map into the two slot maps and use bifunctoriality.
Induction on the number of outer nodes proves all the required whiskering equations. Composites of
generators are covered because the intervening $c_V^{-1}c_V$ cancel.  Apply this result to the
proper/open equations proved inside the semilinear category in step 2. The total-limit functor
preserves each equality of transformations. Conjugating by the $c_V$ of step 4 gives its integral
identity, with the canonical compositors checked in step 5. In particular the comparison of two
nested compactifications is the composite of their direct-image/open compositors and the
intervening proper/open generator, so the same calculation proves its compatibility. When
compatible composition towers are refined, [lem-cbc-compactifiable-compatible-tower] gives the
commuting proper maps on the ambient and intermediate schemes; the corresponding proper/open
squares need not be cartesian. Step 2 applies to precisely these general commutative squares, so
its vertical and horizontal laws identify the two refined composites. Their common-refinement
equalities then survive total limit with the comparisons just proved. This proves the required
refinement and nested-composition compatibility; it does not infer an equality from finite
evaluations or assert a canonical lift of unrelated finite-level arrows.

7. Naturality follows from the displayed recursion, since $u,e,d_A$ and all the adjunction
transposes are natural. For the zero input each additive unary operation and tensor with zero is
zero, and the maps into and out of the resulting zero object are its unique maps. For the identity
open, its open unit is identity, so the formulas for $\beta,\gamma$ and $\Gamma$ give identity
comparisons. For the empty open, $J_j=0$, so those formulas give the unique zero maps. For an
identity square the clopen projection is identity and the mate triangle identities give the
identity direct-image or open transformation. For an equal-index quotient $A_n\to A_n$, reduction
is the identity coefficient map and its comparison is the tensor unit identification. A single
compactification is exactly the $d_{S_pJ_j}$ checked in steps 3 and 4. For
$W=\operatorname{Spec}k$ and a degree-zero free coefficient module the recursion is ordinary
tensor reassociation and the inverse of its reduction-limit unit; rank zero is the preceding zero
case. All indices are $n\geq1$; no use of an undefined $n=0$ level occurs. These checks impose no
extra geometric or boundedness hypotheses.
-/
theorem integralCompactificationSystemRealization
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p) :
    ∃ o : Operations l E, Nonempty (Realizations l E D o) := by
  obtain ⟨o, ⟨a⟩⟩ := integralCanonicalAmbientModels l E
  obtain ⟨c, ⟨hc⟩⟩ := integralComparisonRecursionLaws l E D _hl o a
  have reductions {I : Type u} [Finite I]
      {X : I → Over (Spec (CommRingCat.of D.k))}
      {W : Over (Spec (CommRingCat.of D.k))}
      (e : Expression _ I X W) (g : e.geometric) :
      ∃ r : (e.domain l E o).ι ⋙ inputReduction l E X ⋙
          e.evaluate (systemInterpretation l E o) ≅
          e.realizationTarget l E o ⋙ (calculus l E W.left).reduction,
        ∀ K : (e.domain l E o).FullSubcategory,
          (calculus l E W.left).reduction.map ((c e g).hom.app K) ≫ r.inv.app K =
            (calculus l E W.left).adjunction.counit.app
              ((e.evaluate (systemInterpretation l E o)).obj
                ((inputReduction l E X).obj K.obj)) := by
    let F := (e.domain l E o).ι ⋙ inputReduction l E X ⋙
      e.evaluate (systemInterpretation l E o)
    let G := e.realizationTarget l E o
    let ce : F ⋙ coefficientSequenceLimit l E W.left ≅ G :=
      NatIso.ofComponents (fun K ↦ (c e g).app K)
        (fun f ↦ (c e g).hom.naturality f)
    obtain ⟨r, hr⟩ := reduction_normalization (calculus l E W.left).adjunction F G ce
      (fun K ↦ good_counit_isIso l E W.left _
        (e.admissibleGood l E o _ K.property.2))
    exact ⟨r, hr⟩
  classical
  let r := fun {I : Type u} [Finite I]
      {X : I → Over (Spec (CommRingCat.of D.k))}
      {W : Over (Spec (CommRingCat.of D.k))}
      (e : Expression _ I X W) (g : e.geometric) ↦ (reductions e g).choose
  have hn := fun {I : Type u} [Finite I]
      {X : I → Over (Spec (CommRingCat.of D.k))}
      {W : Over (Spec (CommRingCat.of D.k))}
      (e : Expression _ I X W) (g : e.geometric) ↦ (reductions e g).choose_spec
  obtain ⟨hcomplete, hsquare, hsupport⟩ :=
    integralExpressionCoefficientSquares l E D _hl o a c hc r hn
  refine ⟨o, ⟨{
    compositors := a.compositors
    openComparisons := a.openComparisons
    canonicalBridge := a.canonicalBridge
    properOpen := a.properOpen
    ringedTensorCoherence := a.ringedTensorCoherence
    comparison := c
    realizationModel := a.realizationModel
    openRealization := a.openRealization
    openNormalization := a.openNormalization
    inputNormalization := hc.inputNormalization
    push := hc.push
    pull := hc.pull
    shriek := hc.shriek
    tensor := hc.tensor
    supportRecursion := hc.supportRecursion
    reduction := r
    normalization := hn
    ringedModels := a.ringedModels
    ringedOpenComparisons := a.ringedOpenComparisons
    ringedProperOpen := a.ringedProperOpen
    completionIso := hcomplete
    coherence := ?_
    compactSupport := hsupport }⟩⟩
  intro I _ X W e t ge gt K ht s v hpair
  exact coefficient_intertwining (calculus l E W.left).adjunction
    ((c e ge).app K) ((c t gt).app ⟨K.obj, ht⟩) s v
    (hsquare e t ge gt K ht s v hpair)

end IntegralSystemRealization
end WeilConjectures
