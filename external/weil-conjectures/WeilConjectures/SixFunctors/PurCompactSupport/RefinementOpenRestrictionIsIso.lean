/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurCompactSupport.RefinementOpenRestrictionData
import WeilConjectures.SixFunctors.PurCompactSupport.RefinementOpenRestrictionComponentIsIso

/-! Invertibility of the specified refinement-restriction transformation. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.PurCompactSupport

variable (R : Coefficients.{u})
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)
  (hi : R.pull (c.i ≫ r.hom) = proEtaleRingCompositeCoefficients c.i r.hom
    (R.ring d.Z) (R.ring c.Z) (R.ring X) (R.pull r.hom) (R.pull c.i))

/--
Source: Stacks 0F7B and 0F7I, clopen restriction of the proper refinement
image.  A natural transformation whose components are the specified proper
restriction maps is invertible on the whole unbounded derived category.  The
component identification is the only hypothesis; the clopen calculation
supplies the inverse componentwise and hence the natural-transformation
isomorphism.
Proof: the refinement fibre product has a clopen distinguished section; extension by
zero is exact there, so the component maps have inverses. Extensionality identifies
any transformation with those components.
(blueprint: lem-sf-refinement-open-restriction-is-iso).
-/
theorem refinementRestriction_data_isIso
    (θ : ((openExtension R c.i).mapDerivedCategory ⋙ push R r.hom) ⋙ pull R d.i ⟶
        (openExtension R c.i).mapDerivedCategory ⋙ pull R c.i)
    (hθ : ∀ M, θ.app M = refinementRestriction R r hi M) :
    IsIso θ := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  rw [hθ M]
  exact refinementRestriction_component_isIso R r hi M

end WeilConjectures.PurCompactSupport
