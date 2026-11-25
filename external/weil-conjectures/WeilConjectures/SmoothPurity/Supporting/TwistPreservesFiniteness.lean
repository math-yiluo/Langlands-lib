/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Native.NativeSignedLineFiniteness
import Mathlib.Tactic.CongrExclamation

import WeilConjectures.AlgebraicGeometry.Native.NativeFiniteTwistLocalLine
import WeilConjectures.AlgebraicGeometry.Native.NativeIntegralTwistLocalLine
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTateBasis
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.SmoothPurity.Supporting.FieldTwistInverse
import WeilConjectures.SmoothPurity.Finite.FiniteLineTensorConditions
import WeilConjectures.SmoothPurity.Integral.IntegralLineTensorCompleteness
import WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence
import WeilConjectures.SmoothPurity.Supporting.SignedTwistReductionComparison
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Tate twists preserve finiteness conditions

Source: blueprint definition-tate-twists--10, order 1802; main-20261015 order 2148
(blueprint: definition-tate-twists--10).

## Main definitions
* `TwistReductionMaps`
* `IsCanonicalTwistReductionMaps`

## Main statements
* `AlgebraicGeometry.ProEtale.twist_preserves_native_finiteness`: the current condensed statement.
* `twist_preserves_finiteness`: the retained legacy compatibility theorem.

The current primary attachment uses ordinary unbounded derived tensor over the
actual pulled-back condensed coefficient rings. The completed/rationalized API
below remains for its existing callers.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
local instance (priority := 10000) (Y : AlgebraicGeometry.Scheme.{u}) :
    CategoryTheory.EssentiallySmall.{u + 1} Y.ProEt :=
  CategoryTheory.essentiallySmallSelf.{0} _
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (S : Scheme.{u})
  [∀ x : S, Invertible (l : S.residueField x)]

/-- The quotient unit in the prescribed first finite line, using the original
constant-integer tensor construction. Source: blueprint proof, steps 1 and 6
(blueprint: definition-tate-twists--10). -/
def twistFiniteFirstReductionSection (n : ℕ) (U : S.ProEtᵒᵖ)
    (x : (purTwistIntegralModule S l E).val.obj U) :
    (purTwistFiniteOne S l E n).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction
    (𝟙 (integralCoefficientSheaf l E S n).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
        (purTwistIntegralQuotient S l E n) (purTwistIntegralOne S l E))).app U)
      ((1 : (integralCoefficientSheaf l E S n).obj.obj U) ⊗ₜ[
        (purTwistIntegralConstant S l E).obj.obj U,
        ((purTwistIntegralQuotient S l E n).hom.app U).hom] x)

/-- Semilinear reductions of all signed completed lines along the actual limit projection.
Source: blueprint proof, steps 1 and 6 (blueprint: definition-tate-twists--10). -/
abbrev TwistReductionMaps (n : ℕ) := ∀ m : ℤ,
  integralTwistLine l E S m ⟶
    (scalarReductionRestriction l E S n).obj (finiteCoefficientTwist l E S n m)

/-- The reduction is fixed at zero by the coefficient projection, at one by the
original quotient tensor, at positive powers by tensoring, and at negative powers
by the dual evaluation pairing. Thus no arbitrary isomorphism is called canonical.
Source: blueprint proof, steps 1 and 6 (blueprint: definition-tate-twists--10). -/
def IsCanonicalTwistReductionMaps (n : ℕ) (c : TwistReductionMaps l E S n) : Prop :=
  (∀ (U : S.ProEtᵒᵖ)
      (a : (completedIntegralCommRingSheafUnrestricted l E S).obj.obj U),
    (c 0).val.app U a = (completedIntegralCommRingProjectionUnrestricted l E S n).hom.app U a) ∧
  (∀ (U : S.ProEtᵒᵖ) (x : (purTwistIntegralModule S l E).val.obj U),
    (c 1).val.app U x = twistFiniteFirstReductionSection l E S n U x) ∧
  (∀ (k : ℕ) (U : S.ProEtᵒᵖ)
      (x : (coefficientTwistPower S
        (R := completedIntegralCommRingSheafUnrestricted l E S)
        (purTwistIntegralModule S l E) (k + 1)).val.obj U)
      (y : (purTwistIntegralModule S l E).val.obj U),
    (c (Int.ofNat (k + 2))).val.app U
      (SheafOfModules.siteSheafTensorTmul
        (A := completedIntegralCommRingSheafUnrestricted l E S) _ _ U x y) =
      SheafOfModules.siteSheafTensorTmul
        (A := integralCoefficientCommRingSheaf l E S n) _ _ U
        ((c (Int.ofNat (k + 1))).val.app U x) ((c 1).val.app U y)) ∧
  ∀ (k : ℕ) (U : S.ProEtᵒᵖ)
      (f : (integralTwistLine l E S (Int.negSucc k)).val.obj U)
      (x : (coefficientTwistPower S
        (R := completedIntegralCommRingSheafUnrestricted l E S)
        (purTwistIntegralModule S l E) (k + 1)).val.obj U),
    (((c (Int.negSucc k)).val.app U f).app (Opposite.op (Over.mk (𝟙 U.unop))))
      ((c (Int.ofNat (k + 1))).val.app U x) =
      (completedIntegralCommRingProjectionUnrestricted l E S n).hom.app U
        ((f.app (Opposite.op (Over.mk (𝟙 U.unop)))) x)

private noncomputable def constantModulePullbackFunctor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] :
    proEtaleRingModules Y (proEtaleConstantRing Y A) ⥤
      proEtaleRingModules X (proEtaleConstantRing X A) := by
  have := constantComparison_isIso f A
  exact proEtaleRingModulePullback f (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
    (asIso (proEtaleCoefficientInverseImageMap f A))

private theorem locallyConstant_of_iso (Y : Scheme.{u}) (A : Type u) [CommRing A]
    {F G : proEtaleRingModules Y (proEtaleConstantRing Y A)} (e : F ≅ G)
    (hF : IsLocallyConstantProEtaleModuleSheaf Y A F) :
    IsLocallyConstantProEtaleModuleSheaf Y A G := by
  obtain ⟨I, U, f, hc, ht⟩ := hF
  refine ⟨I, U, f, hc, fun i ↦ ?_⟩
  obtain ⟨M, ⟨hM⟩⟩ := ht i
  exact ⟨M, ⟨(SheafOfModules.overFunctor _ (U i)).mapIso e.symm ≪≫ hM⟩⟩

private theorem finite_stalk_of_iso (Y : Scheme.{u}) (A : Type u) [CommRing A]
    {F G : proEtaleRingModules Y (proEtaleConstantRing Y A)} (e : F ≅ G)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    [Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing Y A) F)] :
    Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing Y A) G) := by
  let E : proEtaleRingModules Y (proEtaleConstantRing Y A) ⥤
      ModuleCat.{u + 1} (proEtaleGeometricStalkRing y (proEtaleConstantRing Y A)) :=
    (SheafOfModules.forget _ ⋙
    PresheafOfModules.pushforward₀ (proEtaleGeometricNeighbourhoodForget y) _ ⋙
    PresheafOfModules.colimitFunctor (C := ProEtaleGeometricNeighbourhood y)
      (colimit.isColimit (proEtaleGeometricStalkRingDiagram y (proEtaleConstantRing Y A))))
  have : Finite (E.obj F) :=
    ‹Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing Y A) F)›
  change Finite (E.obj G)
  exact Finite.of_injective (E.mapIso e.symm).toLinearEquiv
    (E.mapIso e.symm).toLinearEquiv.injective

private theorem constructibleProEtale_of_iso (Y : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    {F G : proEtaleRingModules Y (proEtaleConstantRing Y A)} (e : F ≅ G)
    (hF : IsConstructibleProEtaleModuleSheaf Y A F) :
    IsConstructibleProEtaleModuleSheaf Y A G := by
  obtain ⟨S, hn, hS⟩ := hF
  refine ⟨S, hn, fun i ↦ ?_⟩
  let e' : proEtaleConstantModulePullback (S.immersion i) A F ≅
      proEtaleConstantModulePullback (S.immersion i) A G :=
    (constantModulePullbackFunctor (S.immersion i) A).mapIso e
  refine ⟨locallyConstant_of_iso _ A e' (hS i).1, ?_⟩
  intro Ω _ _ y
  have := (hS i).2 Ω y
  exact finite_stalk_of_iso _ A e' y

private theorem exact_support_subset (A : Type u) [CommRing A]
    (F : proEtaleRingModules S (proEtaleConstantRing S A) ⥤
      proEtaleRingModules S (proEtaleConstantRing S A))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : proEtaleDerivedCategory S A) :
    proEtaleCohomologicalSupport (F.mapDerivedCategory.obj K) ⊆
      proEtaleCohomologicalSupport K := by
  intro i hi hz
  exact hi (((F.mapDerivedCategoryHomologyFunctorIso i).app K).isZero_iff.mp
    (F.map_isZero hz))

private theorem support_iso (A : Type u) [CommRing A]
    {K K' : proEtaleDerivedCategory S A} (e : K ≅ K') :
    proEtaleCohomologicalSupport K = proEtaleCohomologicalSupport K' := by
  ext i
  exact not_congr ((DerivedCategory.homologyFunctor _ i).mapIso e).isZero_iff

private theorem tor_of_iso (A : Type u) [CommRing A]
    {K K' : proEtaleDerivedCategory S A} (e : K ≅ K') (a b : ℤ)
    (h : HasProEtaleTorAmplitude S A K a b) : HasProEtaleTorAmplitude S A K' a b := by
  refine ⟨h.1, ?_⟩
  intro L P hL f hf hP M i hi
  exact h.2 L P (hL.map (fun e' ↦ e' ≪≫ e.symm)) f hf hP M i hi

omit [∀ x : S, Invertible (l : S.residueField x)] in
private theorem intrinsic_of_iso (n : ℕ)
    {K K' : proEtaleDerivedCategory S (Padic.coefficientExtensionRing l E (n + 1))}
    (e : K ≅ K') (h : intrinsicFiniteTorsionConstructible l E (n + 1)
      (Nat.succ_pos n) S K) :
    intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) S K' := by
  let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  refine ⟨?_, fun i ↦ constructibleProEtale_of_iso S _
    ((DerivedCategory.homologyFunctor _ i).mapIso e) (h.2 i)⟩
  change (proEtaleCohomologicalSupport K').Finite
  rw [← support_iso S _ e]
  exact h.1

private theorem finite_twist_constructible (n : ℕ) (m : ℤ)
    (hr : (finiteCoefficientTwist l E S n m).IsFiniteLocallyFreeOfRank 1)
    (K : proEtaleDerivedCategory S (Padic.coefficientExtensionRing l E (n + 1)))
    (hK : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) S K) :
    intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) S
      ((finiteComplexTwist l E S n m).obj K) := by
  let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let := hr
  let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) m).1
  let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) m).2.1
  let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) m).2.2
  let F := SheafOfModules.siteSheafTensorRight
    (A := integralCoefficientCommRingSheaf l E S n) (finiteCoefficientTwist l E S n m)
  refine ⟨hK.1.subset (exact_support_subset S _ F K), ?_⟩
  intro i
  exact constructibleProEtale_of_iso S _
    ((F.mapDerivedCategoryHomologyFunctorIso i).app K)
    ((finiteLineTensor_conditions S _ (finiteCoefficientTwist l E S n m)).2.1 _ (hK.2 i))

/-- The exact preservation and inverse-twist assertions at all four coefficients.
Source: blueprint node definition-tate-twists--10, order 1802; main order 2148
(blueprint: definition-tate-twists--10).

Proof plan:
1. Let $R$ be $(A_{E,n})_S$ or $\widehat{\mathcal O}_{E,S}$. The finite and integral assertions of
[lem-pur-twist-sheaf-locally-free], clauses 3 and 4, give a covering on which $\Lambda(1)$ is $R$,
its finite reductions, and the integral membership of $\mathcal O_E(1)$ in $D^b_c$. Apply the
tensor-power and sheaf-Hom definitions of [definition-tate-twists]. On the same covering
every positive power is $R^{\otimes m}\cong R$, and its dual is $\mathcal Hom_R(R,R)\cong R$. Thus
$L=\Lambda(m)$ is locally free of rank one for every integer $m$, including $m=0$ and $m<0$. The
evaluation maps $L\otimes_R L^\vee\to R$ and $L^\vee\otimes_R L\to R$ are isomorphisms: locally
they are multiplication $R\otimes_R R\to R$. These maps are defined without a choice of basis, so
the local inverses agree on overlaps and glue. The tensor and Hom formulas identify $L^\vee$ with
$\Lambda(-m)$ for $m\geq0$; for $m<0$ use the canonical bidual map from the positive power to its
double dual, which locally is $R\to\operatorname{Hom}_R(\operatorname{Hom}_R(R,R),R)$, an
isomorphism by evaluation at $1$. This uses the completed sheaf as integral unit, not the discrete
constant sheaf $(\mathcal O_E)_S$. Uses: lem-pur-twist-sheaf-locally-free, def-coefficient-twists-
detailed, def-pur-sheaf-hom, lem-pc-sheaf-modules-tensor-closed.

2. For either $R$ from step 1, put $T_L(F)=F\otimes_R L$. Associativity, symmetry and unit maps of
[lem-pc-sheaf-modules-tensor-closed], followed by the evaluation isomorphisms in step 1, give
$T_{L^\vee}T_L(F)\cong F$ and $T_LT_{L^\vee}(F)\cong F$, naturally in $F$. Hence these are inverse
additive equivalences. They preserve kernels and cokernels directly by their universal properties:
for example maps $B\to T_L(\ker f)$ correspond, after applying $T_{L^\vee}$, to maps
$T_{L^\vee}B\to\ker f$, hence exactly to maps $B\to T_L(\operatorname{dom}f)$ killed by $T_L(f)$;
for cokernels, maps $T_L(\operatorname{coker}f)\to B$ correspond to maps $\operatorname{coker}f\to
T_{L^\vee}B$, hence exactly to maps $T_L(\operatorname{cod}f)\to B$ annihilating $T_L(f)$. Thus
$T_L$ is exact, so $L$ is flat by [def-pc-flat-sheaf-modules]. Uses: lem-pc-sheaf-modules-tensor-
closed, def-pc-flat-sheaf-modules.

3. Apply [lem-weil-pbc-exact-functor-complex-cohomology] and [lem-sf-exact-functor-derived-
triangulated] to the exact functors $T_L$ and $T_{L^\vee}$ from step 2. They act termwise on
complexes, induce inverse triangulated equivalences, and satisfy $\mathcal H^i(T_L C)\cong\mathcal
H^i(C)\otimes_R L$ for every complex, without a boundedness assumption. To identify this functor
with derived tensor, first observe that $L[0]$ and $L^\vee[0]$ are K-flat with flat terms:
tensoring any acyclic complex with either is exactly its termwise image under the corresponding
exact functor, hence remains acyclic by the cohomology formula. Choose $P\to C$ K-flat with flat
terms by [lem-pc-kflat-resolution]. Exactness makes $P\otimes_RL\to C\otimes_RL$ a quasi-
isomorphism. The terms of $P\otimes_RL$ are flat: tensor with $P^i\otimes_RL$ is the composite of
the exact functors tensor with $P^i$ and $T_L$. Moreover $P\otimes_RL$ is K-flat: for any acyclic
$B$, the total complex $B\otimes_R(P\otimes_RL)$ identifies, by termwise tensor associativity,
with $(B\otimes_RP)\otimes_RL$, which is acyclic since $P$ is K-flat and $T_L$ is exact. In this
rebracketing, $T_L$ commutes with the direct sums in the total tensor [def-pc-tensor-complex-
sheaves], since the closed tensor statement makes it a left adjoint:
$\operatorname{Hom}(T_L(\bigoplus_i B_i),D)\cong\prod_i\operatorname{Hom}(T_LB_i,D)$. The degree-
zero line introduces no additional differential sign. The derived tensor computation of [lem-weil-
pbc-site-derived-tensor-descent] applies to the two K-flat flat-term complexes $P$ and $L[0]$ and
gives $C\otimes_R^LL\cong T_L(C)$. In particular the cohomology formula holds for derived tensor.
Both $L$ and its dual have amplitude $[0,0]$, and the inverse equivalence shows that $\mathcal
H^i(C\otimes_R^LL)$ vanishes exactly when $\mathcal H^i(C)$ vanishes. Uses: lem-weil-pbc-exact-
functor-complex-cohomology, situation-conventions, lem-pc-kflat-resolution,
def-pc-kflat-complex, lem-weil-pbc-site-derived-tensor-descent, lem-pc-sheaf-modules-tensor-
closed, def-pc-tensor-complex-sheaves.

4. Take $R=(A_{E,n})_S$. For an arbitrary derived object $C$ whose
cohomological support is contained in $[a,b]$, the exact tensor calculation of step 3
shows directly that the support of $C\otimes_R^LL$ is contained in the same interval.
For the separate finite constructibility assertion, assume the intrinsic finite-torsion
constructibility predicate on $C$. Each nonzero cohomology sheaf then has a finite
constructible stratification. On a stratum, the restriction of
$\mathcal H^i(C)\otimes_RL$ is the tensor of the restrictions, by
[lem-weil-pbc-ringed-topoi-module-pullback-tensor] and the pro-etale inverse-image
construction [def-weil-proetale-inverse-image]. Pulling back a trivializing cover of $L$
identifies it with the constant rank-one module. Refining the finite local covers gives
$M\otimes_{A_{E,n}}A_{E,n}\cong M$ on each object, so the same partition and finite
stalks prove constructibility for $L$ and its dual. Uses: def-weil-finite-torsion-
constructibility, lem-weil-pbc-ringed-topoi-module-pullback-tensor, def-weil-proetale-
inverse-image.
5. Still at finite coefficients, suppose $C$ has Tor amplitude in $[a,b]$ in [def-weil-finite-tor-
amplitude]. For an arbitrary sheaf $M$ placed in degree zero, choose also a K-flat flat-term
resolution $Q\to M$ by [lem-pc-kflat-resolution], and use the K-flat $P$ of step 3. Since
$P\otimes_RL$ is K-flat, $(C\otimes_R^LL)\otimes_R^LM$ is represented by
$(P\otimes_RL)\otimes_RQ\cong(P\otimes_RQ)\otimes_RL$, by the total-tensor direct-sum comparison
proved in step 3 and the sheaf tensor symmetry and associativity of [lem-pc-sheaf-modules-tensor-
closed]. The latter is $T_L$ applied to the representative of $C\otimes_R^LM$. Exactness and the
cohomology formula of step 3 imply that its cohomology vanishes outside $[a,b]$. The implication
just proved also holds with $L^\vee$ as its line; applying that implication to $C\otimes_R^LL$ and
using $(C\otimes_R^LL)\otimes_R^LL^\vee\cong C$ proves the converse. Thus the entire Tor interval,
rather than merely existence of some finite interval, is preserved. This tests all module sheaves
$M$, not just constructible ones. Uses: definition-constructible-sheaves, lem-pc-sheaf-modules-
tensor-closed, def-pc-kflat-complex, lem-weil-pbc-site-derived-tensor-descent, lem-pc-kflat-
resolution.

6. For the integral stage write $R=\widehat{\mathcal O}_{E,S}$, $A_j=(A_{E,j})_S$, and $L=\mathcal
O_E(m)$. Reducing a trivialization $L|_V\cong R|_V$ gives $L_j=L\otimes_RA_j$ free of rank one
locally. The canonical base-change maps for tensor powers and their duals are isomorphisms, since
locally they are the identities on $A_j$; hence step 1 and [definition-tate-twists]
identify $L_j$ with $A_{E,j}(m)$ for every $j$. Choose $P\to C$ as in step 3. The termwise
rebracketing map $$(P\otimes_RL)\otimes_RA_j\cong(P\otimes_RA_j)\otimes_{A_j}L_j$$ is an
isomorphism of complexes. The left computes the reduction of $C\otimes_R^LL$, by [def-weil-
integral-derived-reduction], because $P\otimes_RL$ is K-flat with flat terms; on the right
$P\otimes_RA_j$ is K-flat over $A_j$ by [lem-pur-kflat-change-of-rings]. Also $L_j[0]$ is K-flat
with flat terms by the finite-level calculation of step 3, so the two-input derived tensor formula
applies on the right. Thus $$(C\otimes_R^LL)\otimes_R^LA_j\cong
(C\otimes_R^LA_j)\otimes_{A_j}^LA_{E,j}(m).$$ These maps are compatible with $A_{j+1}\to A_j$ and
the maps from $C$: on tensor representatives they send $(x\otimes l)\otimes a$ to $(x\otimes
a)\otimes(l\otimes1)$; reducing either before or after this formula has the same result. After
restriction of scalars, the same comparison for a reduction complex $B$ is the termwise identity
$B\otimes_RL\cong B\otimes_{A_j}L_j$; it computes $T_L$ on that reduction since $T_L$ is exact,
without assuming $B$ is K-flat over $R$. The tensor computations use the ringed-site derived
tensor of [lem-weil-pbc-site-derived-tensor-descent], so no discrete integral coefficient category
is substituted. Uses: definition-tate-twists, lem-pc-sheaf-modules-tensor-closed, lem-pc-
kflat-resolution, lem-pur-kflat-change-of-rings, lem-weil-pbc-site-derived-tensor-descent, def-
weil-integral-derived-reduction.

7. The integral derived equivalences $T_L$ and $T_{L^\vee}$ of step 3 preserve the countable
products that occur in [def-weil-derived-complete]. Indeed for every derived object $B$ and family
$(C_j)$ there are natural bijections $$\operatorname{Hom}(B,T_L(\prod_jC_j))\cong\operatorname{Hom
}(T_{L^\vee}B,\prod_jC_j)\cong\prod_j\operatorname{Hom}(T_{L^\vee}B,C_j)\cong\prod_j\operatorname{
Hom}(B,T_LC_j).$$ This is exactly the product universal property; it identifies the comparison
with the map having components $T_L$ of the projections. The following argument is quantified over
either line from step 1. Let $C$ be derived complete. Apply the triangulated functor from [lem-sf-
exact-functor-derived-triangulated] to its defining distinguished Roos triangle
$$C\xrightarrow{c}\prod_jC_j\xrightarrow{1-s}\prod_jC_j\longrightarrow C[1],$$ where $C_j$ denotes
its derived reduction restricted back to $R$-modules. The product isomorphisms and step 6 identify
this triangle with a Roos triangle for the reductions of $T_LC$. Its first map has the reduction
maps as components, and its second map is $1-s$ for that tower, by the compatibility checked in
step 6. Consequently $T_LC$ is derived complete by precisely the existential Roos-triangle
condition of [def-weil-derived-complete]. This does not choose a purported unique morphism into a
derived limit. Taking the line in this quantified argument to be $L^\vee$ proves preservation by
the inverse twist. Uses: def-weil-derived-complete, situation-conventions.

8. For the integral interval clauses, take an arbitrary derived object $C$ whose
reductions satisfy the displayed common cohomological interval, or the displayed common
Tor interval, without assuming constructibility. Steps 5 and 6 preserve the same bound
at every level, giving exactly the two unconditional interval implications in the
statement. Separately, if $C\in D^b_c(S,\mathcal O_E)$, [def-weil-derived-complete-
integral-detailed] supplies derived completeness and one cohomological interval for all
reductions. Steps 4 and 6 give bounded constructible reductions of $T_LC$, and step 7
gives completeness, proving membership in the integral $D^b_c$. If $C$ satisfies the
integral finite-Tor condition, its reductions have one Tor interval independent of the
level by [definition-constructible-sheaves], and steps 5 and 6 preserve it. All statements
hold for the inverse line as well. In particular the integral unit and every signed line
have the required degree-zero reductions and completeness. Uses: def-weil-derived-
complete-integral-detailed, definition-constructible-sheaves, lem-pur-twist-sheaf-locally-free.
9. The functors $T_L$ and $T_{L^\vee}$ are exact and $\mathcal O_E$-linear by their tensor
definitions and the inverse identities of step 2. Applying [lem-weil-twist-rationalization] to the
scalar localization in [def-weil-rationalization-karoubi] gives inverse functors on $D^b_c(S,E)$
and makes the images $E(m)$ invertible. Uses: lem-weil-twist-rationalization, def-weil-
rationalization-karoubi.

10. For $E\subset F$, clause 3 of [lem-pur-twist-sheaf-locally-free] and the formula in [def-
coefficient-twists-detailed] give the canonical identification $\mathcal O_H(1)\cong
T\otimes_{R_0}R_H$ for $H=E,F$: substitute $R_H=R_0\otimes_{(\mathbf Z_\ell)_S}(\mathcal O_H)_S$
and rebracket. Thus [lem-weil-integral-twist-base-change] applies and gives $\mathcal
O_E(m)\otimes_{R_E}R_F\cong\mathcal O_F(m)$ for every integer $m$, compatibly with evaluation and
tensor/dual powers. Uses: lem-weil-integral-twist-base-change, lem-pur-twist-sheaf-locally-free,
definition-tate-twists.

11. For a derived-complete $C$ and a K-flat flat-term representative $P\to C$, [lem-weil-integral-
twist-derived-scalar] supplies the chain isomorphism $(P\otimes_{R_E}\mathcal
O_E(m))\otimes_{R_E}R_F\cong(P\otimes_{R_E}R_F)\otimes_{R_F}\mathcal O_F(m)$ and the natural
comparison $\operatorname{Ext}_{F/E}(C(m))\cong\operatorname{Ext}_{F/E}(C)(m)$. The K-flat and
flat-term hypotheses are preserved by [lem-pur-kflat-change-of-rings], while [lem-weil-finite-
free-completed-scalar-comparison] identifies completed and ordinary scalar extension on these
complete objects. Uses: lem-weil-integral-twist-derived-scalar, lem-pur-kflat-change-of-rings,
lem-weil-finite-free-completed-scalar-comparison.

12. For $E\subset F\subset G$, [lem-weil-integral-twist-scalar-coherence] gives the commutative
square relating successive and direct twist comparisons, with the integral composition map
transported from tensor associativity by the specified ordinary-to-completed comparison. Both
paths send $(x\otimes l)\otimes b\otimes c$ to $(x\otimes bc)\otimes(l\otimes1)$. Its
rationalization agrees with [lem-weil-scalar-extension-composition]; identity extensions use the
tensor unit maps. Thus these are comparisons for exactly the transition functors in the common-
stage definition. Uses: lem-weil-integral-twist-scalar-coherence, lem-weil-scalar-extension-
composition.

13. The inverse identities of steps 2 and 9, evaluation compatibility of step 10, and scalar
compatibilities of steps 11–12 verify the hypotheses of [lem-weil-qbar-twist-common-stage]. Hence
a common-stage morphism $[F,f]$ in [def-weil-algebraically-closed-coefficients] is sent to
$[F,T_{F,m}(f)]$ with endpoints identified by the scalar comparisons: explicitly its
representative is $\beta_{F/E',C'}^{-1}\circ T_{F,m}(f)\circ\beta_{F/E,C}$. The lemma gives
independence of enlarging $F$, functoriality, and the descended line-evaluation inverse
identities. Thus these are inverse twists on the common-stage category with inverse $(-m)$, and
$\Qlb(m)$ is invertible. At $E$ and $\Qlb$ coefficients, [definition-constructible-sheaves]
identifies the finite-Tor subcategory with the constructible category. All constructions use
integral representatives and common finite stages. Uses: lem-weil-qbar-twist-common-stage, def-
weil-algebraically-closed-coefficients, definition-constructible-sheaves.

The intrinsic names sfIntegralConstructible, IsSfDerivedComplete and
scalarReductionDerivedExtension give the same completed-coefficient objects,
canonical augmented Roos triangles and positive reductions used in these steps.
Rational tensor and common-stage tensor use the recorded intrinsic categories.
-/
theorem twist_preserves_finiteness
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (S : Scheme.{u})
    [∀ x : S, Invertible (l : S.residueField x)]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] :
    ∀ m : ℤ,
      (∀ n : ℕ,
        (finiteCoefficientTwist l E S n m).IsFiniteLocallyFreeOfRank 1 ∧
        IsLocallyConstantProEtaleModuleSheaf S (Padic.coefficientExtensionRing l E (n + 1))
          (finiteCoefficientTwist l E S n m)) ∧
      (integralTwistLine l E S m).IsFiniteLocallyFreeOfRank 1 ∧
      (∀ n : ℕ, ∃! c : TwistReductionMaps l E S n,
        IsCanonicalTwistReductionMaps l E S n c ∧
        ∀ k : ℤ, ∃! α : (scalarReductionExtension l E S n).obj
            (integralTwistLine l E S k) ≅ finiteCoefficientTwist l E S n k,
          ∀ (U : S.ProEtᵒᵖ) (a : (integralCoefficientCommRingSheaf l E S n).obj.obj U)
              (x : (integralTwistLine l E S k).val.obj U),
            α.hom.val.app U (sfReductionTensor l E S n (integralTwistLine l E S k) U a x) =
              a • (@id ((finiteCoefficientTwist l E S n k).val.obj U) ((c k).val.app U x))) ∧
      (∀ k : ℤ, ∀ n : ℕ, Nonempty ((scalarReductionDerivedExtension l E S n).obj
        (sfIntegralTwistingObject l E S k) ≅
          (DerivedCategory.singleFunctor _ 0).obj (finiteCoefficientTwist l E S n k))) ∧
      (∀ (n : ℕ) (K : proEtaleDerivedCategory S
          (Padic.coefficientExtensionRing l E (n + 1))),
        intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) S K →
        intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) S
          ((finiteComplexTwist l E S n m).obj K)) ∧
      (∀ (n : ℕ) (K : proEtaleDerivedCategory S
          (Padic.coefficientExtensionRing l E (n + 1))),
        finiteTorConstructible l E (n + 1) (Nat.succ_pos n) S K →
        finiteTorConstructible l E (n + 1) (Nat.succ_pos n) S
          ((finiteComplexTwist l E S n m).obj K)) ∧
      (∀ (n : ℕ) (a b : ℤ) (K : proEtaleDerivedCategory S
          (Padic.coefficientExtensionRing l E (n + 1))),
        proEtaleCohomologicalSupport K ⊆ Set.Icc a b →
        proEtaleCohomologicalSupport ((finiteComplexTwist l E S n m).obj K) ⊆ Set.Icc a b) ∧
      (∀ (n : ℕ) (a b : ℤ) (K : proEtaleDerivedCategory S
          (Padic.coefficientExtensionRing l E (n + 1))),
        HasProEtaleTorAmplitude S (Padic.coefficientExtensionRing l E (n + 1)) K a b →
        HasProEtaleTorAmplitude S (Padic.coefficientExtensionRing l E (n + 1))
          ((finiteComplexTwist l E S n m).obj K) a b) ∧
      (∀ K : DerivedCategory (scalarReductionSource l E S),
        sfIntegralConstructible l E S K →
        sfIntegralConstructible l E S ((sfIntegralTwistingFunctor l E S m).obj K)) ∧
      sfIntegralConstructible l E S (sfIntegralTwistingObject l E S m) ∧
      (∀ K : DerivedCategory (scalarReductionSource l E S),
        IsSfDerivedComplete l E S K →
        IsSfDerivedComplete l E S ((sfIntegralTwistingFunctor l E S m).obj K)) ∧
      (∀ K : DerivedCategory (scalarReductionSource l E S),
        finiteTorConstructibleIntegral l E S K →
        finiteTorConstructibleIntegral l E S ((sfIntegralTwistingFunctor l E S m).obj K)) ∧
      (∀ (a b : ℤ) (K : DerivedCategory (scalarReductionSource l E S)),
        (∀ n : ℕ, proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension l E S n).obj K) ⊆ Set.Icc a b) →
        ∀ n : ℕ, proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension l E S n).obj
            ((sfIntegralTwistingFunctor l E S m).obj K)) ⊆ Set.Icc a b) ∧
      (∀ (a b : ℤ) (K : DerivedCategory (scalarReductionSource l E S)),
        (∀ n : ℕ, HasProEtaleTorAmplitude S (Padic.coefficientExtensionRing l E (n + 1))
          ((scalarReductionDerivedExtension l E S n).obj K) a b) →
        ∀ n : ℕ, HasProEtaleTorAmplitude S (Padic.coefficientExtensionRing l E (n + 1))
          ((scalarReductionDerivedExtension l E S n).obj
            ((sfIntegralTwistingFunctor l E S m).obj K)) a b) ∧
      (∀ n : ℕ, Nonempty (finiteComplexTwist l E S n m ⋙
        finiteComplexTwist l E S n (-m) ≅ 𝟭 _)) ∧
      Nonempty (sfIntegralTwistingFunctor l E S m ⋙
        sfIntegralTwistingFunctor l E S (-m) ≅ 𝟭 _) ∧
      Nonempty (sfRationalTwistingFunctor l E S m ⋙
        sfRationalTwistingFunctor l E S (-m) ≅ 𝟭 _) ∧
      Nonempty (sfQbarTwistingFunctor l S Ω m ⋙ sfQbarTwistingFunctor l S Ω (-m) ≅ 𝟭 _) := by
  intro m
  have hfinite (n : ℕ) := signedLineTensor_equivalence S
    (integralCoefficientCommRingSheaf l E S n) (purTwistFiniteOne S l E n) m
  have hintegral := signedLineTensor_equivalence S
    (completedIntegralCommRingSheafUnrestricted l E S) (purTwistIntegralModule S l E) m
  have hred := signedTwistReduction_comparison l E S
  have hfin (n : ℕ) : (finiteCoefficientTwist l E S n m).IsFiniteLocallyFreeOfRank 1 :=
    (hfinite n).1
  have htor (n : ℕ) (a b : ℤ)
      (K : proEtaleDerivedCategory S (Padic.coefficientExtensionRing l E (n + 1)))
      (hK : HasProEtaleTorAmplitude S (Padic.coefficientExtensionRing l E (n + 1)) K a b) :
      HasProEtaleTorAmplitude S (Padic.coefficientExtensionRing l E (n + 1))
        ((finiteComplexTwist l E S n m).obj K) a b := by
    let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    let := hfin n
    let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) m).1
    let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) m).2.1
    let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) m).2.2
    exact (finiteLineTensor_conditions S _ (finiteCoefficientTwist l E S n m)).2.2 K a b hK
  have hsupp (n : ℕ) (a b : ℤ)
      (K : proEtaleDerivedCategory S (Padic.coefficientExtensionRing l E (n + 1)))
      (hK : proEtaleCohomologicalSupport K ⊆ Set.Icc a b) :
      proEtaleCohomologicalSupport ((finiteComplexTwist l E S n m).obj K) ⊆ Set.Icc a b := by
    let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) m).1
    let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) m).2.1
    let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) m).2.2
    exact (exact_support_subset S _ (SheafOfModules.siteSheafTensorRight
      (A := integralCoefficientCommRingSheaf l E S n) (finiteCoefficientTwist l E S n m)) K).trans
        hK
  have hcomplete (K : DerivedCategory (scalarReductionSource l E S))
      (hK : IsSfDerivedComplete l E S K) :
      IsSfDerivedComplete l E S ((sfIntegralTwistingFunctor l E S m).obj K) := by
    let := hintegral.1
    have : (SheafOfModules.siteSheafTensorRight
        (A := completedIntegralCommRingSheafUnrestricted l E S)
        (integralTwistLine l E S m)).Additive := integralSheafTwist_additive l E S m
    have : PreservesFiniteLimits (SheafOfModules.siteSheafTensorRight
        (A := completedIntegralCommRingSheafUnrestricted l E S)
        (integralTwistLine l E S m)) := integralSheafTwist_finiteLimits l E S m
    have : PreservesFiniteColimits (SheafOfModules.siteSheafTensorRight
        (A := completedIntegralCommRingSheafUnrestricted l E S)
        (integralTwistLine l E S m)) := integralSheafTwist_finiteColimits l E S m
    exact integralLineTensor_complete l E S (integralTwistLine l E S m) K hK
  have hireduce (n : ℕ) (K : DerivedCategory (scalarReductionSource l E S)) :=
    (hred.2.2 m n).some.app K
  have hisupp (a b : ℤ) (K : DerivedCategory (scalarReductionSource l E S))
      (hK : ∀ n : ℕ, proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension l E S n).obj K) ⊆ Set.Icc a b) (n : ℕ) :
      proEtaleCohomologicalSupport ((scalarReductionDerivedExtension l E S n).obj
        ((sfIntegralTwistingFunctor l E S m).obj K)) ⊆ Set.Icc a b := by
    exact (support_iso S _ (hireduce n K)).symm ▸ hsupp n a b _ (hK n)
  have hitor (a b : ℤ) (K : DerivedCategory (scalarReductionSource l E S))
      (hK : ∀ n : ℕ, HasProEtaleTorAmplitude S (Padic.coefficientExtensionRing l E (n + 1))
        ((scalarReductionDerivedExtension l E S n).obj K) a b) (n : ℕ) :
      HasProEtaleTorAmplitude S (Padic.coefficientExtensionRing l E (n + 1))
        ((scalarReductionDerivedExtension l E S n).obj
          ((sfIntegralTwistingFunctor l E S m).obj K)) a b :=
    tor_of_iso S _ (hireduce n K).symm a b (htor n a b _ (hK n))
  have hiconst (K : DerivedCategory (scalarReductionSource l E S))
      (hK : sfIntegralConstructible l E S K) :
      sfIntegralConstructible l E S ((sfIntegralTwistingFunctor l E S m).obj K) := by
    obtain ⟨hc, a, b, hab, hr⟩ := hK
    refine ⟨hcomplete K hc, a, b, hab, fun n ↦ ⟨?_, ?_⟩⟩
    · exact intrinsic_of_iso l E S n (hireduce n K).symm
        (finite_twist_constructible l E S n m (hfin n) _ (hr n).1)
    · exact hisupp a b K (fun n ↦ (hr n).2) n
  refine ⟨?_, hintegral.1, hred.1, hred.2.1, ?_, ?_, hsupp, htor,
    hiconst, sfIntegralTwistingObject_mem l E S m, hcomplete, ?_, hisupp, hitor, ?_, ?_,
    (fieldTwist_inverse l E S Ω m).1, (fieldTwist_inverse l E S Ω m).2⟩
  · intro n
    let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    let := hfin n
    let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) m).1
    let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) m).2.1
    let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) m).2.2
    exact ⟨hfin n, (finiteLineTensor_conditions S _ (finiteCoefficientTwist l E S n m)).1⟩
  · exact fun n K hK ↦ finite_twist_constructible l E S n m (hfin n) K hK
  · intro n K hK
    obtain ⟨hc, a, b, ht⟩ := hK
    exact ⟨finite_twist_constructible l E S n m (hfin n) K hc, a, b, htor n a b K ht⟩
  · intro K hK
    obtain ⟨hc, a, b, hab, ht⟩ := hK
    exact ⟨hiconst K hc, a, b, hab, hitor a b K ht⟩
  · intro n
    let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) m).1
    let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) m).2.1
    let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) m).2.2
    let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) (-m)).1
    let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) (-m)).2.1
    let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) (-m)).2.2
    obtain ⟨e⟩ := (hfinite n).2
    exact ⟨Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso _⟩
  · obtain ⟨e⟩ := hintegral.2
    let C := integralTowerModules l E S
    have : (𝟭 C).Additive := ⟨fun {_ _} _ _ ↦ rfl⟩
    have : PreservesFiniteLimits (𝟭 C) := inferInstance
    have : PreservesFiniteColimits (𝟭 C) := inferInstance
    exact ⟨Functor.mapDerivedCategoryCompIso (integralSheafTwist l E S m)
      (integralSheafTwist l E S (-m)) ≪≫
      Functor.mapDerivedCategoryNatIso
        (G := 𝟭 (integralTowerModules l E S)) e ≪≫
          Functor.mapDerivedCategoryIdIso _⟩

end WeilConjectures

set_option backward.isDefEq.respectTransparency true

open scoped CategoryTheory.Obj

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

private def freeUnitIso (R : C) [MonObj R] : (free R).obj (𝟙_ C) ≅ regular R :=
  isoMk (ρ_ R) (by
    change ((α_ R R (𝟙_ C)).inv ≫ μ[R] ▷ (𝟙_ C)) ≫ (ρ_ R).hom =
      R ◁ (ρ_ R).hom ≫ μ[R]
    rw [Category.assoc, rightUnitor_naturality]
    monoidal)

variable [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)] [BraidedCategory C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] (φ : R ⟶ S) [IsMonHom φ]

private noncomputable def extendFreeIso : free R ⋙ extendScalars φ ≅ free S :=
  ((freeForgetAdjunction R).comp (extendRestrictAdjunction φ)).leftAdjointUniq
    (freeForgetAdjunction S)

private noncomputable def extendRegularIso : (extendScalars φ).obj (regular R) ≅ regular S :=
  (extendScalars φ).mapIso (freeUnitIso R).symm ≪≫
    (extendFreeIso φ).app (𝟙_ C) ≪≫ freeUnitIso S

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint

private noncomputable def pullExtendIso
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] :
    (upperStar Ab.{u + 1} f).mapMod R ⋙
        Mod.extendScalars ((upperStar Ab.{u + 1} f).map a) ≅
      Mod.extendScalars a ⋙ (upperStar Ab.{u + 1} f).mapMod S := by
  let adj := upperStarLowerStarAdjunction Ab.{u + 1} f
  letI : (upperStar Ab.{u + 1} f).OplaxMonoidal :=
    Functor.Monoidal.toOplaxMonoidal
  letI : adj.IsMonoidal := by
    constructor
    · exact (isMonoidal_upperStarLowerStarAdjunction Ab.{u + 1} f).leftAdjoint_ε
    · intro A B
      exact (isMonoidal_upperStarLowerStarAdjunction Ab.{u + 1} f).leftAdjoint_μ A B
  exact Adjunction.pullIsoOfComapIso
    (Mod.extendRestrictAdjunction ((upperStar Ab.{u + 1} f).map a))
    (Mod.extendRestrictAdjunction a)
    (adj.mapModAdjunction R) (adj.mapModAdjunction S)
    (Mod.comapMapModComapIso (lowerStar Ab.{u + 1} f)
      ((upperStar Ab.{u + 1} f).map a) a
      (adj.unitAlgHom R) (adj.unitAlgHom S) (adj.unit.naturality a))

end AlgebraicGeometry.ProEtale
