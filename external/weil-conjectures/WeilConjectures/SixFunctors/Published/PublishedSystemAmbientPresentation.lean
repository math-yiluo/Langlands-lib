/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.System.SystemPullbackCompositorIdentification
/-! # Ambient pullback data in the published sequence categories
Source: Stacks 03D3, 03EL, 07A4 and 07A7. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  WeilConjectures.pullbackTensorCalculus HasDerivedCategory.standard
  WeilConjectures.CoefficientClosedStructure.tensor
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
/-- The ambient functors and comparisons with their published sequence-category types.
Source: Stacks 03D3, 03EL, 07A4 and 07A7
(blueprint: def-sf-published-system-ambient-presentation). -/
structure PublishedSystemAmbientData where
  pull : ∀ {X Y : Scheme.{u}} (_f : X ⟶ Y),
    coefficientSequenceDerived l E Y ⥤ coefficientSequenceDerived l E X
  tensor : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    (pullbackTensorCalculus l E Y).systemClosed.tensor ⋙ pull f ≅
      (pull f).prod (pull f) ⋙ (pullbackTensorCalculus l E X).systemClosed.tensor
  comp : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    pull g ⋙ pull f ≅ pull (f ≫ g)
/-- Record the existing ambient constructions; no additional choices are made.
Source: AmbientPullbackTensor.derivedPull, tensorData and derivedComp, Stacks 07A4
(blueprint: def-sf-published-system-ambient-presentation). -/
def publishedSystemAmbientData : PublishedSystemAmbientData l E where
  pull f := AmbientPullbackTensor.derivedPull l E f none
  tensor {X Y} f :=
    @SemilinearSections.BundledTensorComparison.mu.{u + 1, u, u}
      (AmbientPullbackTensor.Site Y none) (AmbientPullbackTensor.Site X none)
      (AmbientPullbackTensor.siteCategory Y none)
      (AmbientPullbackTensor.siteCategory X none)
      (AmbientPullbackTensor.siteSmall.{u, u} Y none)
      (AmbientPullbackTensor.siteSmall.{u, u} X none)
      (AmbientPullbackTensor.topology Y none) (AmbientPullbackTensor.topology X none)
      (AmbientPullbackTensor.coefficients l E Y none)
      (AmbientPullbackTensor.coefficients l E X none)
      (AmbientPullbackTensor.pull l E f none)
      (AmbientPullbackTensor.pullAdditive l E f none)
      (AmbientPullbackTensor.pullLimits l E f none)
      (AmbientPullbackTensor.pullColimits l E f none)
      (pullbackTensorCalculus l E Y).systemClosed
      (pullbackTensorCalculus l E X).systemClosed
      (pullbackTensorCalculus l E Y).systemTensorModel
      (pullbackTensorCalculus l E X).systemTensorModel
      (AmbientPullbackTensor.tensorData.{u, u} l E f none
        (pullbackTensorCalculus l E Y).systemClosed
        (pullbackTensorCalculus l E X).systemClosed
        (pullbackTensorCalculus l E Y).systemTensorModel
        (pullbackTensorCalculus l E X).systemTensorModel)
  comp f g := AmbientPullbackTensor.derivedComp l E f g none

/-- The published inverse image is the pullback recorded by the ambient package.
Source: Stacks 015F and sequence_derived_eq
(blueprint: def-sf-published-system-ambient-presentation).
Proof: the package pull field is derivedPull itself. Apply sequence_derived_eq. -/
theorem publishedSystemAmbientPull_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullbackTensorSequenceDerived l E f = (publishedSystemAmbientData l E).pull f := by
  exact sequence_derived_eq l E f
/-- The specified functor identification, recorded with its sequence-category type.
Source: Stacks 015F and publishedSystemAmbientPull_eq
(blueprint: def-sf-published-system-ambient-presentation). -/
@[irreducible] def publishedSystemAmbientPullIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullbackTensorSequenceDerived l E f ≅ (publishedSystemAmbientData l E).pull f :=
  eqToIso (publishedSystemAmbientPull_eq l E f)

end WeilConjectures
