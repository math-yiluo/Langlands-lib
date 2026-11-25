/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import all WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
import WeilConjectures.CategoryTheory.Brown.BrownHypotheses
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteLocalizingExceptionalPreservation
import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralBrownAdjoint
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralExceptionalRestriction
import all WeilConjectures.AlgebraicGeometry.SixFunctors.ShriekCoefficientIsomorphism
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import Mathlib.NumberTheory.Padics.Complex
import WeilConjectures.CategoryTheory.ModuleObjects.ProperBaseChange.GrothendieckAbelian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Rational.RationalRestrictionGlue
import all WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Existence of the exceptional inverse image

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-existence/_section.md,
and det-existence-localizing.proof.md and det-existence-restriction.proof.md
(blueprint: theorem-exceptional-inverse-image).

The lower shriek is the existing restriction of the actual compactification composite.
All categories are full subcategories of the ordinary unbounded module-object derived
category, with the recorded finite constant-model constructibility convention.
-/

@[expose] public section
set_option linter.privateModule false

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Compactness transports by precomposition with an isomorphism. -/
private theorem compact_of_iso
    {C : Type*} [Category C] [Preadditive C] [HasCoproducts.{u} C]
    {K L : C} (e : K ≅ L) (hL : IsCompactObject L) : IsCompactObject K := by
  classical
  intro I A
  let d := DirectSum.map (fun i ↦ Preadditive.leftComp (A i) e.hom)
  have hd : Function.Bijective d :=
    ⟨(DirectSum.map_injective _).2 (fun i ↦ e.symm.homFromEquiv.injective),
      (DirectSum.map_surjective _).2 (fun i ↦ e.symm.homFromEquiv.surjective)⟩
  let post := Preadditive.leftComp (∐ A) e.hom
  have hp : Function.Bijective post := e.symm.homFromEquiv.bijective
  let a := DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp K (Sigma.ι A i))
  let b := DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp L (Sigma.ι A i))
  have square : a.comp d = post.comp b := by
    apply DirectSum.addHom_ext
    intro i f
    simp only [AddMonoidHom.comp_apply]
    dsimp [a, b, d]
    rw [DirectSum.map_of, DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
    exact Category.assoc _ _ _
  have hb : Function.Bijective b := hL I A
  have hcomp : Function.Bijective (a ∘ d) := by
    change Function.Bijective (a.comp d)
    rw [square]
    exact hp.comp hb
  exact (Function.Bijective.of_comp_iff a hd).mp hcomp

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

local notation "S(" T ")" =>
  (constantModelBoundedConstructible Λ T ⊓ fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K)
local notation "L(" T ")" => localizingClosureProEtale Λ T

end AlgebraicGeometry.ProEtale.CondensedRing
