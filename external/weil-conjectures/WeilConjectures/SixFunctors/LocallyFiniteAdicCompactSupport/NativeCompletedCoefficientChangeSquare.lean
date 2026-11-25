/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportData
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompletedCoefficientIntegralMapSquare

/-! # Pullback compatibility of normalized completed-to-native maps -/

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
Any family of maps represented by normalized coefficient presentations is compatible
with inverse image along scheme morphisms.

Proof source: Bhatt--Scholze, Lemma 6.8.2 and Section 6.8. Compose both sides with
every finite quotient projection. The finite constant and residue equations identify
both composites pointwise, and the inverse-limit projections are jointly monic.
(blueprint: lem-sf-native-completed-coefficient-change-square)
-/
theorem native_completed_coefficient_change_square_of_presentation
    [G : NativeGeometry.{u} l]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (i : E →ₐ[Padic l] PadicAlgCl l)
    (m : ∀ T : Scheme.{u},
      (PurCompactSupport.completed l E).ring T ⟶ (nativeCoefficients l).ring T)
    (C : ∀ T : Scheme.{u}, CoefficientPresentation l T E i)
    (hC : ∀ T : Scheme.{u}, m T = (C T).integralMap l T) :
    ∀ {U V : Scheme.{u}} (g : U ⟶ V),
      ((PurCompactSupport.completed l E).pull g).hom ≫ m U =
        (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map (m V) ≫
          ((nativeCoefficients l).pull g).hom := by
  intro U V g
  rw [hC U, hC V]
  exact coefficient_presentation_integralMap_pull_square l E i C g

end WeilConjectures.LocallyFiniteAdicCompactSupport
