/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProjectionCoefficientTransport.RationalProjectionTensorCompatibility
import WeilConjectures.SixFunctors.Common.CommonProjectionProperFactor
import WeilConjectures.SixFunctors.Common.CommonProjectionOpenFactor

/-! # A shared tensor comparison for common-stage projection mates

Source: thm-sf-pf-field.proof.md, Compatibility and the common coefficient-field paragraph.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale

namespace WeilConjectures
open ProjectionCoefficientTransport

set_option backward.isDefEq.respectTransparency false in
/-- Inclusion preserves each compact-support projection through one tensor comparison,
independent of the compactification. This is an individual mate calculation: no
compactification comparison law, composition law or invertibility of projection is assumed.

Source: current blueprint, sec-six-functors-basics/sk-thm-sf-pf-field/
thm-sf-pf-field.proof.md, Compatibility and the common finite coefficient-field paragraph.
(blueprint: lem-sf-common-projection-tensor-compatibility).

Proof: the coefficient prime is invertible on every SixFunctorSpace, since it is
invertible in the base field. On two objects included from E, use the literal
common-stage tensor object, its isoToStage at E, commonStageTensorComparison, and
the two normalized scalar unit isomorphisms at E. The inverse composite gives
inclusion of the rational tensor isomorphic to the common-stage tensor of the
inclusions. This construction involves neither a morphism nor a compactification.
The representative formula of commonStageDerivedTensor and naturality of the
scalar tensor comparison prove naturality in both inputs. Transport the endpoints
by the recorded rationalTensorNormalization and commonStageTensorNormalization;
this yields the family t in the statement.

The canonical common-stage pullback/tensor formula on these same finite models
identifies each rational proper and open tensor/pullback comparison with its
included common-stage counterpart. The operation comparison components are the
prescribed ones: commonStageModelNormalization makes them identity components
on the chosen finite models. For the proper projection, transpose under the
recorded pull/direct adjunctions. Its transpose is tensor/pullback followed by the
counit; the counit square of commonStageComparison and the preceding tensor square
identify the two transposes. For the open inverse projection, transpose under the
open adjunctions instead; the unit square and the canonical open tensor/pullback
normalization identify the transposes. Invert this equality of open isomorphisms.
Paste the proper and open squares, using the support-factorization normalization
and the pullComposition equation to identify their final pullback factor. The
result is the displayed projection square with exactly source and target as
specified. This argument never uses a rational coherence law and concerns only
one compactification at a time. Zero inputs, empty schemes and identity opens
satisfy the same naturality and unit/counit identities. -/
theorem commonProjectionTensorCompatibility
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (H : SixFunctorCommonStages D C)
    (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar) :
    ∃ t : ∀ X : SixFunctorSpace D,
      Functor.uncurry.obj ((H.coefficientStages E₀).rationalTensor X) ⋙
          GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀ ≅
        (GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀).prod
          (GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀) ⋙
          Functor.uncurry.obj (H.commonStageTensor X),
      ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
        (c : Compactification f.hom.left)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar X.obj.left E₀)
        (L : GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar Y.obj.left E₀),
        (GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) E₀).map
            (compactSupportProjectionComponent (H.coefficientStages E₀).rationalExchange
              f c K L) ≫
          (target (H.commonStageComparison E₀) t f c K L).hom =
        (source (H.commonStageComparison E₀) t f c K L).hom ≫
          compactSupportProjectionComponent H.commonStageExchange f c
            ((GeneralAlgebraicallyClosedCoefficients.inclusion
              (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀).obj K)
            ((GeneralAlgebraicallyClosedCoefficients.inclusion
              (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) E₀).obj L) := by
  refine ⟨commonProjectionTensorComparison H E₀, ?_⟩
  intro X Y f c K L
  let Q := compactSupportProjectionSquare f c
  exact projection_preserved_of_factors (H.commonStageComparison E₀)
    (commonProjectionTensorComparison H E₀)
    ((H.coefficientStages E₀).rationalExchange Q) (H.commonStageExchange Q) K L
    (commonProjectionProperFactor H E₀ Q K L)
    (commonProjectionOpenFactor H E₀ Q K L)

end WeilConjectures
