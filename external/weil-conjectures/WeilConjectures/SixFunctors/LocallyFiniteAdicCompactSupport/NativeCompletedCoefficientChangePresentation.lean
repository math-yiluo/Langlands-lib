/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportData
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompletedCoefficientPresentationAt

/-! # Existence of normalized completed-to-native coefficient maps -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]

/--
There is a family of maps from completed coefficients to native coefficients which is
represented by normalized coefficient presentations.

Proof source: Bhatt--Scholze, Lemma 6.8.2 and Section 6.8. Construct the maps by the
finite quotient realization of the completed coefficient sheaf, and use the finite
constant and residue normalizations of the presentations to identify each component.
The pullback compatibility is deliberately left to the separate square theorem.
(blueprint: lem-sf-native-completed-coefficient-change-presentation)
-/
theorem exists_native_completed_coefficient_presentation
    [G : NativeGeometry.{u} l]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (i : E →ₐ[Padic l] PadicAlgCl l) :
    ∃ (m : ∀ T : Scheme.{u},
        (PurCompactSupport.completed l E).ring T ⟶ (nativeCoefficients l).ring T)
      (C : ∀ T : Scheme.{u}, CoefficientPresentation l T E i),
      ∀ T : Scheme.{u}, m T = (C T).integralMap l T := by
  classical
  let C : ∀ T : Scheme.{u}, CoefficientPresentation l T E i :=
    fun T ↦ Classical.choice (exists_native_completed_coefficient_presentation_at l E i T)
  refine ⟨fun T ↦ (C T).integralMap l T, C, ?_⟩
  intro T
  rfl

end WeilConjectures.LocallyFiniteAdicCompactSupport
