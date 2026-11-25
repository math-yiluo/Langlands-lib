/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom

/-! # Object formulas for the recorded common-stage operations

Source: the common-stage operation specifications in the current blueprint, Step 5.
(blueprint: lem-pod-common-stage-operation-object-normalizations).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The chosen common-stage functors retain their specified literal object formulas.
Source: blueprint Step 5 and the object clauses of the common-stage operation
specifications (blueprint: lem-pod-common-stage-operation-object-normalizations).
Proof: each functor is the choice from its unique normalized existence theorem.
Unfold that choice and project the object clause of its specification, separately
for pullback, tensor and internal Hom. This also covers zero objects and empty
schemes: no argument depends on a section or a nonempty coefficient basis. -/
theorem podCommonStageObjectNormalizations :
    (∀ {X Y : Scheme.{u}} (g : X ⟶ Y)
      [∀ x : X, Invertible (l : X.residueField x)]
      [∀ y : Y, Invertible (l : Y.residueField y)]
      (P : generalAlgebraicallyClosedConstructibleCategory l Ω Y),
      (commonStageDerivedPullback l Ω g).obj P = commonStagePullbackObject l Ω g P) ∧
    (∀ (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
      (M N : generalAlgebraicallyClosedConstructibleCategory l Ω W),
      (commonStageDerivedTensor l Ω W).obj (M, N) = commonStageTensorObject l Ω W M N) ∧
    (∀ (W : Scheme.{u}) (P : (commonStageHomPairs l Ω W).FullSubcategory),
      (commonStageDerivedInternalHom l Ω W).obj P = commonStageHomObject l Ω W P) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X Y g hX hY P
    exact (commonStageDerivedPullback_existsUnique l Ω g).exists.choose_spec.1 P
  · intro W hW M N
    exact (commonStageDerivedTensor_existsUnique l Ω W).exists.choose_spec.1 M N
  · intro W P
    exact (commonStageDerivedInternalHom_existsUnique l Ω W).exists.choose_spec.1 P

end WeilConjectures
