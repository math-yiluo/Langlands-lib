/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportData
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompletedCoefficientIntegralMapSquareComponent

/-! # Pullback compatibility of normalized integral presentation maps -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]

/--
The explicit family of normalized integral presentation maps is pullback compatible.
This is the finite-quotient comparison step used by the completed-to-native change
square.  It is strictly smaller than the wrapper theorem because it has no arbitrary
family of maps and no representation hypothesis.

Proof source: Bhatt--Scholze, Lemma 6.8.2 and Section 6.8. Compose both sides with
all finite quotient projections; the finite constant and residue equations identify
the composites pointwise, and the completed projections are jointly monic.
(blueprint: lem-sf-native-completed-coefficient-integral-map-square)
-/
theorem coefficient_presentation_integralMap_pull_square
    [G : NativeGeometry.{u} l]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (i : E →ₐ[Padic l] PadicAlgCl l)
    (C : ∀ T : Scheme.{u}, CoefficientPresentation l T E i) :
    ∀ {U V : Scheme.{u}} (g : U ⟶ V),
      ((PurCompactSupport.completed l E).pull g).hom ≫
          (C U).integralMap l U =
        (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
            ((C V).integralMap l V) ≫
          ((nativeCoefficients l).pull g).hom := by
  intro U V g
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  exact coefficient_presentation_integralMap_pull_square_component l E i C g W

end WeilConjectures.LocallyFiniteAdicCompactSupport
