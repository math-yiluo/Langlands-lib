/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.Sites.PullbackFlat
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs

/-!
# The comparison functor `ν^*` preserves flat sheaves

For a Noetherian (for instance finite) commutative ring `Λ`, the inverse image
`ν^* : Sh(X_ét, Λ) ⥤ Sh(X_proét, Λ)` along the inclusion of the small étale site into the small
pro-étale site sends flat étale sheaves of `Λ`-modules to flat pro-étale sheaves
(`AlgebraicGeometry.ProEtale.flat_comparisonUpperStar_obj`, blueprint
`corollary-finite-tor-amplitude-under-comparison`).

## Main results

- `AlgebraicGeometry.ProEtale.coverPreserving_toProEt`: the inclusion `ν` is cover-preserving.
- `AlgebraicGeometry.ProEtale.flat_comparisonUpperStar_obj`: `ν^*` preserves flat sheaves.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u})

/-- The inclusion `ν : X_ét ⥤ X_proét` sends étale coverings to pro-étale coverings. -/
lemma coverPreserving_toProEt :
    CoverPreserving X.smallEtaleTopology (ProEt.topology X) (toProEt X) := by
  rw [ProEt.topology_eq_restrictedTopology]
  exact MorphismProperty.Over.coverPreserving_changeProp X etale_le_weaklyEtale
    etaleTopology_le_proetaleTopology

variable {X} {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ]

-- the instances `WEqualsLocallyBijective` and `HasSheafCompose` on the small étale and
-- pro-étale sites take long to synthesize
/-- Blueprint `corollary-finite-tor-amplitude-under-comparison`: Constant-coefficient inverse image
preserves flat sheaves.

For a Noetherian commutative ring `Λ`, for instance a finite one, the site inverse image
`ν^* : Sh(X_ét, Λ) ⥤ Sh(X_proét, Λ)` takes flat étale sheaves of `Λ`-modules to flat
pro-étale sheaves of `Λ`-modules. Flat means that tensoring with the sheaf is exact.

This is `CategoryTheory.flat_sheafPullback_obj` for the representably flat, cover-preserving
inclusion `ν` of the small étale site into the small pro-étale site: the relation criterion
for flatness holds locally for the flat étale sheaf, and is transported to the pro-étale site
along the filtered colimits computing `ν^*`. -/
theorem flat_comparisonUpperStar_obj {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (hF : ObjectProperty.flat F) :
    ObjectProperty.flat ((ν^*(X)[ModuleCat.{u + 1} Λ]).obj F) :=
  flat_sheafPullback_obj (coverPreserving_toProEt X) hF

-- as for `flat_comparisonUpperStar_obj`
/-- The comparison pullback `ν^*` preserves flat sheaves of `Λ`-modules, for a Noetherian ring
`Λ` (`AlgebraicGeometry.ProEtale.flat_comparisonUpperStar_obj`). -/
instance preservesFlat_comparisonUpperStar :
    (ν^*(X)[ModuleCat.{u + 1} Λ]).PreservesFlat :=
  ⟨fun hF ↦ flat_comparisonUpperStar_obj hF⟩

end AlgebraicGeometry.ProEtale
