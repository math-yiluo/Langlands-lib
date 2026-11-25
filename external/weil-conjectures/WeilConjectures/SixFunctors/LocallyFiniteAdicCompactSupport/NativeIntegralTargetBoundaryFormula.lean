/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeIntegralScalarBoundaryConditions

/-! # The canonical two-arrow formula for the target integral boundary -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [local irreducible] HasDerivedCategory.standard Padic
  CategoryTheory.ScalarLocalization.category
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
set_option allowUnsafeReducibility true in
attribute [local irreducible] WeilConjectures.LocallyFiniteAdicCompactSupport.actual
  WeilConjectures.PurCompactSupport.image
attribute [local instance 2000] Shrink.instField
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} {f : X ⟶ Y}
  (c : Compactification f)

/-- The endpoint-recorded last two factors determine the target boundary arrow.
Source: Bhatt--Scholze, Remark 6.8.15.
Proof: unpack the two factors and their composite equation, then compose their
endpoint-recorded comparisons with the canonical prescribed values.
(blueprint: lem-sf-native-integral-target-boundary-formula). -/
theorem integralTargetBoundary_formula [G : NativeGeometry.{u} l]
    (source : Realization l X) (E : Index l (PadicAlgCl l))
    (K : finiteTorConstructibleIntegralCategory l (Coefficient.{u} l (PadicAlgCl l) E) X)
    {U V : DerivedCategory (proEtaleRingModules Y (ringSheaf l Y))} (d : U ⟶ V)
    (hd : IntegralTargetBoundary l c source E K d) :
    ArrowHEq d
      ((PurCompactSupport.image (nativeCoefficients l) c).map
          ((source.integral E).inv.app
            ((PurCompactSupport.finiteTorIntegralInclusion l
              (Coefficient.{u} l (PadicAlgCl l) E) X).obj K)) ≫
        (operationTransport l c).inv.app
          (source.J.obj ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := l) (Ω := PadicAlgCl l) (Y := X) E).obj
              ((rationalization l (ULift.{u} (PadicAlgCl l))
                (finiteField l E) X).obj K)))) := by
  rcases hd with ⟨M, a₄, a₅, h₄, h₅, rfl⟩
  exact h₄.comp h₅

end WeilConjectures.LocallyFiniteAdicCompactSupport
