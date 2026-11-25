/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarTowerPullbackLimitBridge
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarTowerPullbackStrictSquare

/-! # Canonical scalar comparison in total-limit coordinates

Source: Stacks 07A4 and 0941; realization step 8 of
lem-pur-scalar-extension-tower-coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible]
  integralCompletedTensor integralDerivedPullback
  integralComparisonDerivedSequenceScalar integralComparisonDerivedSequencePullback
  pullbackReduction scalarReduction tensorReduction derivedSigma

/-- The pullback scalar comparison in its specified total-limit coordinates.
This fixes the comparison before transposing through coherent reduction; it does
not assert the tensor comparison or existence of realization models.
Source: Stacks 07A4, 0941; original realization step 8
(blueprint: stage3-pur-scalar-pullback-limit-square).

Proof: choose a flat-term K-flat representative of M. Use the simultaneous
quotient presentation from the reduction model at Y and its scalar and pullback
presentations. The normalization fields of SX, SY and the two pullback models
identify the displayed coordinates with their strict quotient Roos maps. On each
local generator the two scalar/pullback associations multiply the same coefficient
and insert one. This is an equality of chain maps on the whole quotient tower,
including all transitions. The normalized scalar completion comparison has the
same quotient augmentation, with zero shifted Roos coordinate. Its ordinary
pullback normalization therefore identifies the specified scalarPullbackCompleted
with this map. Naturality of the normalized Roos bridge gives the displayed
limit equation. Localization from good representatives and naturality along their
resolution isomorphisms give the equation for M. The input hF only supplies the
completion inverse; proof irrelevance removes its choice. This argument includes
identity maps, empty schemes and ramified coefficient inclusions without assuming
flatness of finite quotient ring maps. -/
theorem scalarTowerPullbackLimitSquare (W : Bool → Scheme.{u})
    (ME : CompletedOperations.Models.{u, u} l E W)
    (ML : CompletedOperations.Models.{u, u} l L W)
    (SX : IntegralComparisonScalarModel.{u, u} l E L ι (W true)
      (ME.calculus true) (ML.roos true))
    (SY : IntegralComparisonScalarModel.{u, u} l E L ι (W false)
      (ME.calculus false) (ML.roos false))
    (f : W true ⟶ W false)
    (_hX : IsUnit (l : Γ(W true, ⊤))) (_hY : IsUnit (l : Γ(W false, ⊤)))
    (M : sfIntegralConstructibleCategory l E (W false))
    (hF : IsSfDerivedComplete l E (W true)
      ((integralDerivedPullback.{u, u} l E f).obj M.obj)) :
    (scalarPullbackCompleted l E L ι f M.obj M.property.1 hF).hom ≫
        (ML.pullback f).realization.hom.app
          ((integralScalarExtension.{u} l E L ι (W false)).obj M.obj) ≫
        (coefficientSequenceLimit.{u, u} l L (W true)).map
          ((integralComparisonDerivedSequencePullback.{u, u} l L f).map
            (scalarReduction l E L ι (W false) (ME.calculus false) (ML.calculus false)
              (ML.roos false) SY M.obj)) =
      SX.realization.hom.app ((integralDerivedPullback.{u, u} l E f).obj M.obj) ≫
        (coefficientSequenceLimit.{u, u} l L (W true)).map
          ((integralComparisonDerivedSequenceScalar.{u, u} l E L ι (W true)).map
            (pullbackReduction l E W ME f M.obj) ≫
          (integralComparisonSystemScalarPullback.{u, u} l E L ι f).hom.app
            ((ME.calculus false).reduction.obj M.obj)) := by
  let k := (coefficientSequenceLimit.{u, u} l L (W true)).map
    ((integralComparisonSystemScalarPullback.{u, u} l E L ι f).inv.app
      ((ME.calculus false).reduction.obj M.obj))
  apply (cancel_mono k).1
  simpa only [k, Category.assoc] using
    scalarTowerPullbackLimitSquare_mate l E L ι W ME ML SX SY f _hX _hY M hF
      (scalarTowerPullbackStrictSquare l E L ι f)

end WeilConjectures.ScalarExtensionTower
