/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructibleBaseChange
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap

public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ChangeOfCoefficients

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperBaseChangeRationalPushforward

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralProperBaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.InternalScalarTensorComparison
import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
import all WeilConjectures.AlgebraicGeometry.NormedCoefficientRealization.NormedCoefficientRealization
import all WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructibleTensorPreservation
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizedDirectImageComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperBaseChange.Compatibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientProjectionSquare

/-!
# Proper direct image with rational condensed coefficients: proper base change

Source: blueprint main-20261015, chap-Construction-of-f,
sk-thm-sfb-proper-base-change/sk-thm-sfb-proper-base-change-rational.md, clause 3, proper base
change (blueprint: proposition-proper-direct-image-constructible-complexes).

Split off from
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperBaseChangeRational`
for compile time. The recorded
unit--square--counit base-change map with the named rational preservation proof is invertible.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStarFromPoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  derivedPushSource derivedPushTarget derivedPushHom
  moduleObjectProjectionMap boundedConstructibleBaseChangeOfPreserves
  DerivedCategory HasDerivedCategory.standard CategoryTheory.Mod.monoidalCategory

attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

attribute [local irreducible] rationalizationPushHom
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  Functor.mapDerivedCategory
set_option allowUnsafeReducibility true in
attribute [local irreducible] rationalCoefficientPushforwardPreservation
  rationalFinitenessPushforwardPreservation
  ContinuousMapRingObj.rationalFinitenessPushforwardPreservation

attribute [local irreducible] derivedTensor moduleObjectProjectionData

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (p : X ⟶ Y) [IsProper p.left]

variable {X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

attribute [local irreducible] boundedConstructibleUpperStar
  derivedUpperStarLowerStarAdjunction ObjectProperty.lift
  boundedConstructibleUpperStarCompatibility boundedConstructiblePullbackSquareComparison
  Functor.squareTransport Adjunction.restrictFullyFaithful

private theorem baseChange_restriction_eq
    (H : PreservesBoundedConstructiblePushforwards (Profinite.padicAlgClRingObj ℓ) k)
    (sq : CommSq g' p' p g) :
    boundedConstructibleBaseChangeOfPreserves (Profinite.padicAlgClRingObj ℓ) ℓ H sq =
      boundedConstructibleBaseChange ℓ sq := by
  rw [boundedConstructibleBaseChange_def]
  with_unfolding_all rfl

private theorem baseChange_restriction_eq_subfield
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (H : PreservesBoundedConstructiblePushforwards (Profinite.continuousMapRingObj E) k)
    (sq : CommSq g' p' p g) :
    boundedConstructibleBaseChangeOfPreserves (Profinite.continuousMapRingObj E) ℓ H sq =
      ContinuousMapRingObj.boundedConstructibleBaseChange ℓ E sq := by
  rw [ContinuousMapRingObj.boundedConstructibleBaseChange_def]
  with_unfolding_all rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The recorded unit--square--counit base-change map is invertible for every proper
cartesian square in the standing setting, with no condition on g.
Source: blueprint rational proper direct image, clause 3, proper base change
(blueprint: proposition-proper-direct-image-constructible-complexes).

Proof: the conditional restriction and the finiteness-coefficient restriction have
identical functor data; their preservation arguments are proofs of the same proposition.
After unfolding just the restricted unit, square and counit constructions, proof
irrelevance identifies their base-change transformations. In each of the two bundled
coefficient cases, apply the existing proper base-change theorem to this same map.
The cartesian square is arbitrary apart from the stated properness of p.
-/
theorem isIso_properBaseChange_boundedConstructible_rational
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj Λ.X]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      Λ = Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Λ = Mon.mk (Profinite.padicAlgClRingObj ℓ))
    (sq : IsPullback g' p' p g)
    (K : ProEtale.BoundedConstructible
      (condensedRingObj Λ.X X.left)) :
    IsIso ((boundedConstructibleBaseChangeOfPreserves Λ.X ℓ
      (rationalCoefficientPushforwardPreservation ℓ Λ hΛ)
      sq.toCommSq).app K) := by
  have hΛ' := hΛ
  rcases hΛ' with ⟨E, hE⟩ | hQ
  · subst Λ
    have hstd : IsIso (boundedConstructibleBaseChangeOfPreserves _ ℓ
        (rationalCoefficientPushforwardPreservation ℓ _ hΛ) sq.toCommSq) := by
      have h := isIso_boundedConstructibleBaseChange_of_isProper ℓ E sq
      rw [← baseChange_restriction_eq_subfield ℓ p E
        (ContinuousMapRingObj.rationalFinitenessPushforwardPreservation ℓ E) sq.toCommSq] at h
      exact h
    infer_instance
  · subst Λ
    have hstd : IsIso (boundedConstructibleBaseChangeOfPreserves _ ℓ
        (rationalCoefficientPushforwardPreservation ℓ _ hΛ) sq.toCommSq) := by
      have h := isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl ℓ sq
      rw [← baseChange_restriction_eq ℓ p
        (rationalFinitenessPushforwardPreservation ℓ) sq.toCommSq] at h
      exact h
    infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing
