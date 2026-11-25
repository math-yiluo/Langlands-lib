/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Compact.CompactSupportProjectionCoherence
import all WeilConjectures.SixFunctors.Rational.RationalProjectionComparisonEquations
import WeilConjectures.SixFunctors.Common.CommonProjectionTensorCompatibility

/-! # Projection comparison equations on finite coefficient models

Source: thm-sf-pf-field.proof.md, Compatibility and the common finite coefficient
field paragraph, and fix-prop-projection-formula.proof.md, final coherence sentence.
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
open CategoryTheory.SuppliedExchangeProjection

namespace WeilConjectures

set_option backward.isDefEq.respectTransparency false in
/-- The composition equation on two models included from one finite field.
Source: thm-sf-pf-field.proof.md, Compatibility and the common coefficient-field
paragraph, and fix-prop-projection-formula.proof.md, final coherence sentence.
(blueprint: lem-sf-common-projection-composition-on-stage).
Proof: Apply inclusion to the finite-stage composition equation at the given two models.
Use the canonical common-stage tensor comparisons and the normalized pullback-tensor
comparisons. Preservation of the proper counit and the open adjunction identifies each
finite projection mate with the common-stage projection under these comparisons.
Move the support and tensor comparisons past each projection by naturality.
The composition and pullComposition equations of commonStageComparison identify the
support compositor and the final pullback compositor. Both sides are now conjugates
of the two sides of the included finite-stage equation, with the same endpoints.
Cancel the endpoint isomorphisms. The calculation includes identities, repeated
fields, zero objects and empty schemes; no equality is reflected through inclusion. -/
theorem commonProjectionComposition_onStage
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (H : SixFunctorCommonStages D C)
    (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar)
    (hH : CompactSupportProjectionCoherence (H.coefficientStages E₀).rational
      (H.coefficientStages E₀).rationalTensor (H.coefficientStages E₀).rationalExchange
      (fun _ _ ↦ True))
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left)
    (K₀ : GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar X.obj.left E₀)
    (L₀ : GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar Z.obj.left E₀) :
    let K := (GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀).obj K₀;
    let L := (GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := C.l) (Ω := C.Qbar) (Y := Z.obj.left) E₀).obj L₀;
      ((H.commonStageTensor Z).map ((H.commonStage.composition f g cf cg cfg).hom.app K)).app L ≫
          compactSupportProjectionComponent H.commonStageExchange g cg
            ((H.commonStage.support f cf).obj K) L ≫
          (H.commonStage.support g cg).map
            (compactSupportProjectionComponent H.commonStageExchange f cf K
              ((H.commonStage.pull g).obj L)) =
        compactSupportProjectionComponent H.commonStageExchange (f ≫ g) cfg K L ≫
          (H.commonStage.composition f g cf cg cfg).hom.app
            (((H.commonStageTensor X).obj K).obj ((H.commonStage.pull (f ≫ g)).obj L)) ≫
          (H.commonStage.support g cg).map ((H.commonStage.support f cf).map
            (((H.commonStageTensor X).obj K).map
              ((H.commonStage.pullComposition f g).hom.app L))) := by
  obtain ⟨t, hp⟩ := commonProjectionTensorCompatibility H E₀
  exact ProjectionCoefficientTransport.composition_transfer
    (H.commonStageComparison E₀) t
    (H.coefficientStages E₀).rationalExchange H.commonStageExchange hp
    f g cf cg cfg K₀ L₀ (hH.composition f g cf cg cfg K₀ L₀ trivial)

end WeilConjectures
