/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.PullbackFlat
public import WeilConjectures.Mathlib.CategoryTheory.Limits.MorphismProperty
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.KFlat

/-!
# The pro-étale pullback preserves flat sheaves of modules

For a Noetherian commutative ring `Λ` and a morphism of schemes `g : Z ⟶ Y`, the pullback
`g^* : Sh(Y_proét, Λ) ⥤ Sh(Z_proét, Λ)` sends flat sheaves of `Λ`-modules to flat ones. This is
`CategoryTheory.flat_sheafPullback_obj` for base change along `g`, which is representably flat
and preserves pro-étale coverings (`AlgebraicGeometry.Scheme.ProEt.coverPreserving_overPullback`).
This is the pro-étale counterpart of
`AlgebraicGeometry.Etale.upperStarPreservesFlat_moduleCat`.

## Main results

- `AlgebraicGeometry.ProEtale.upperStarPreservesFlat_moduleCat`: the instance
  `AlgebraicGeometry.ProEtale.UpperStarPreservesFlat (ModuleCat Λ)` for Noetherian `Λ`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]

-- the instances `WEqualsLocallyBijective` and `HasSheafCompose` on the small pro-étale sites
-- take long to synthesize
/-- **The pro-étale pullback preserves flat sheaves of modules.** For a Noetherian commutative
ring `Λ` and every morphism of schemes `g`, the pullback `g^*` sends flat pro-étale sheaves of
`Λ`-modules to flat ones. -/
instance upperStarPreservesFlat_moduleCat :
    ProEtale.UpperStarPreservesFlat (ModuleCat.{u + 1} Λ) where
  preservesFlat g :=
    have := MorphismProperty.Over.representablyFlat_pullback @WeaklyEtale g
    ⟨fun hF ↦ flat_sheafPullback_obj (ProEt.coverPreserving_overPullback g) hF⟩

end AlgebraicGeometry.ProEtale
