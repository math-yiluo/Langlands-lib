/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-! # Additivity of the inverse image from the point

The inverse image `p_X^* : Cond(Ab) ⥤ Sh(X_proét, Ab)` is a left adjoint, hence additive.
This records it as a global instance, so that the module categories over pulled-back condensed
rings can be equipped with linear structures without local copies of the argument.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- The inverse image `p_X^*` from condensed abelian groups to abelian sheaves on `X_proét` is
additive, being a left adjoint. -/
instance upperStarFromPoint_additive (X : Scheme.{u}) : (upperStarFromPoint X).Additive := by
  have adj : upperStarFromPoint X ⊣ _ := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  have : (upperStarFromPoint X).IsLeftAdjoint := adj.isLeftAdjoint
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (upperStarFromPoint X)
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    adj.leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (upperStarFromPoint X)
  exact Functor.additive_of_preservesBinaryBiproducts _

end AlgebraicGeometry.ProEtale.CondensedRing
