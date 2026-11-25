/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.PoincareDuality.Integral.IntegralPullbackComparisonRealization
public import WeilConjectures.SixFunctors.Supporting.SpecifiedPullbackComparisonAlpha
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.PoincareDuality.Pod.PodCounitScalarWordCoordinates
import WeilConjectures.PoincareDuality.ExplicitScalarCone.ExplicitScalarConeWordCoordinates

/-!
# Agreement of the specified integral pullback scalar comparisons

Source: blueprint main-20261015,
`sec-six-functors/sk-rem-sf-pf-done/lem-fix-weil-operations.proof.md`,
first paragraph, pullback and inverse automorphism squares; the normalization
comparison is agent-written
(blueprint: lem-pod-isomorphism-scalar-comparison-agreement).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory
namespace WeilConjectures

/-- The whole-system counit comparison equals the specified tensor-and-completion
comparison, as a morphism in the ambient derived category. The model parameter D
carries the representative normalizations of the whole-system construction;
no arbitrary comparison map is supplied. The completeness proof used on the
right is supplied by the specified-alpha theorem, and is proof irrelevant.

Source: blueprint main-20261015,
sec-six-functors/sk-rem-sf-pf-done/lem-fix-weil-operations.proof.md, first paragraph,
pullback and inverse automorphism squares; agent-written normalization statement
(blueprint: lem-pod-isomorphism-scalar-comparison-agreement).

Proof:
1. Choose simultaneous normalized quotient models by
   lem-trf-effective-comparison-realization-models, with the actual quotient
   transitions. For C = R_E,Y K set A = S_X U_g,E C and B = U_g,L S_Y C,
   using def-trf-integral-comparison-sequence-systems. Use the same flat-term
   K-flat P and Q = P tensor S_Y as lem-weil-specified-pullback-comparison-alpha.
   Effectivity makes all intermediate counits invertible. Let beta_A and beta_B
   be the resulting source and target word-realization isomorphisms.
2. Lem-trf-counit-realization-substitution identifies the counit-built completed
   map with beta_B inverse followed by realization of kappa followed by beta_A.
   These are precisely the lambda and mu normalizations of
   lem-trf-integral-pullback-comparison-realization. Thus beta_B a = L(kappa) beta_A
   as entire derived arrows, retaining the tower homotopies.
3. Apply lem-pur-normalized-scalar-comparison-realization in the same normalized
   coordinates of def-trf-integral-comparison-realization-models. Balanced scalar
   association on the simultaneous K-flat quotient systems is the specified d_m:
   ((g^-1(p tensor a)) tensor b) tensor s maps to
   (g^-1(p tensor iota_m(a))) tensor (iota_m(b) pi_L,m(s)).
   Lem-weil-specified-pullback-comparison-alpha applies this map to BOTH Roos
   coordinates and uses quotient augmentations with zero shifted coordinate.
   Its canonical tensor/completion alpha therefore satisfies
   beta_B alpha = L(kappa) beta_A. No finite quotient flatness or finite
   Tor-amplitude assumption is used.
4. The two right sides coincide. Cancel beta_B to obtain equality of the two
   specified morphisms in D(X_proet, O_L), for every constructible-complete K.
-/
theorem isomorphismScalarComparisonAgreement
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (D : IntegralComparisonSystem.{u} l)
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfIntegralConstructibleCategory l E Y) :
    (integralComparisonScalar l E L ι D g K).hom =
      (scalarPullbackCompleted l E L ι g K.obj K.property.1
        (specifiedPullbackComparisonAlpha l E L ι g K.obj K.property).choose).hom := by
  let e : CounitRealization.Coefficient.{u} l := ⟨E, inferInstance, inferInstance, inferInstance⟩
  let f : CounitRealization.Coefficient.{u} l := ⟨L, inferInstance, inferInstance, inferInstance⟩
  have h := (podCounitScalarWordCoordinates l).2 D e f ι g
  have hα := ExplicitScalarCone.explicitScalarConeWordCoordinates l E L ι g
    ((D.coefficient E).system Y) ((D.coefficient E).system X)
    ((D.coefficient L).system Y) ((D.coefficient E).roos X)
    ((D.coefficient L).roos X) ((D.coefficient L).roos Y)
    ((D.coefficient E).pullback g) ((D.coefficient L).pullback g)
    ((D.scalar E L ι).model X) ((D.scalar E L ι).model Y)
    ((D.coefficient L).system X) K.obj K.property
    (h.initial K) (h.pullback K) (h.scalar K) (h.sourceWord K) (h.targetWord K)
  have hβ := (h.coordinates K).2
  apply (cancel_mono (podCounitScalarBetaB l D e f ι g K.obj)).1
  rw [h.comparison K]
  simpa only [podCounitScalarBetaA, podCounitScalarBetaB,
    CounitRealization.Primitive.comparison, CounitRealization.Primitive.model,
    CounitRealization.Primitive.system, podCounitWordModels,
    ExplicitScalarCone.betaA, ExplicitScalarCone.betaB,
    ExplicitScalarCone.pullbackSystem, ExplicitScalarCone.scalarSystem,
    ExplicitScalarCone.sourceSystem, ExplicitScalarCone.targetSystem,
    Category.assoc] using hα.symm

end WeilConjectures
