/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportData
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompletedCoefficientChangePresentation
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompletedCoefficientChangeSquare

/-! # Data for the normalized completed-to-native coefficient map -/

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
The completed integral coefficient sheaf admits a simultaneously pullback-compatible
family of maps into the native locally finite coefficient sheaves, and the family is
represented by normalized coefficient presentations.  This is the construction step
in Bhatt--Scholze, Lemma 6.8.2 and Section 6.8.
(blueprint: lem-sf-native-completed-coefficient-change)

Proof source: realize completed coefficients by their finite quotient projections,
compose with the integral-to-rational map and the specified embedding into the
algebraic closure, and verify the pullback square pointwise on sections.  The finite
constant and residue normalizations then identify the resulting map with the chosen
presentation at every scheme.
-/
theorem native_completed_coefficient_change_data
    [G : NativeGeometry.{u} l]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (i : E →ₐ[Padic l] PadicAlgCl l) :
    ∃ (m : ∀ T : Scheme.{u},
        (PurCompactSupport.completed l E).ring T ⟶ (nativeCoefficients l).ring T)
      (C : ∀ T : Scheme.{u}, CoefficientPresentation l T E i),
      (∀ {U V : Scheme.{u}} (g : U ⟶ V),
        ((PurCompactSupport.completed l E).pull g).hom ≫ m U =
          (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map (m V) ≫
            ((nativeCoefficients l).pull g).hom) ∧
      (∀ T : Scheme.{u}, m T = (C T).integralMap l T) := by
  obtain ⟨m, C, hC⟩ := exists_native_completed_coefficient_presentation l E i
  refine ⟨m, C, ?_, hC⟩
  exact native_completed_coefficient_change_square_of_presentation l E i m C hC

end WeilConjectures.LocallyFiniteAdicCompactSupport
