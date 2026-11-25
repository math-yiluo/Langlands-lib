/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous

/-!

# The comparison functors between the small étale and pro-étale sites

For a scheme `X`, the inclusion `ν = AlgebraicGeometry.toProEt X : X.Etale ⥤ X.ProEt`
of the small étale site into the small pro-étale site is continuous, so composition with it
defines the restriction `ν_*` from pro-étale to étale sheaves. Its left adjoint `ν^*` is the
left Kan extension on presheaves followed by sheafification. Since `ν` is representably flat,
`ν^*` is exact.

This is a port, for a general Grothendieck abelian coefficient category, of the definitions
`ProEt.sheafPushforward`, `ProEt.sheafPullback` and `ProEt.sheafAdjunction` of the file
`Comparator/Definitions.lean` of the `proetale` package, which are stated there for `Ab`.

## Main definitions

- `AlgebraicGeometry.ProEtale.comparisonLowerStar`: the restriction functor
  `ν_* : Sh(X_proét, A) ⥤ Sh(X_ét, A)`, with scoped notation `ν_*(X)[A]`.
- `AlgebraicGeometry.ProEtale.comparisonUpperStar`: its left adjoint
  `ν^* : Sh(X_ét, A) ⥤ Sh(X_proét, A)`, with scoped notation `ν^*(X)[A]`.
- `AlgebraicGeometry.ProEtale.comparisonAdjunction`: the adjunction `ν^* ⊣ ν_*`.

## Main results

- `AlgebraicGeometry.ProEtale.preservesFiniteLimits_comparisonUpperStar` and
  `AlgebraicGeometry.ProEtale.preservesHomology_comparisonUpperStar`: `ν^*` is exact. Left
  exactness comes from the flatness of `ν`, through
  `CategoryTheory.preservesFiniteLimits_op_lan_of_flat`, and from the left exactness of
  sheafification. The pointwise left Kan extensions along `ν` exist by
  `CategoryTheory.Functor.hasPointwiseLeftKanExtension_of_hasColimitsOfSize`.

## Implementation notes

As for `AlgebraicGeometry.ProEtale.upperStar`, the coefficient category `A` is Grothendieck
abelian with `Hom`-types in the universe `u + 1`, and sheafification on the small pro-étale
site is `CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable (X : Scheme.{u})

/-- The restriction functor `ν_* : Sh(X_proét, A) ⥤ Sh(X_ét, A)` along the inclusion
`AlgebraicGeometry.toProEt X` of the small étale site into the small pro-étale site,
given objectwise by `(ν_* G)(U) = G(U)` for `U` étale over `X`. -/
noncomputable def comparisonLowerStar :
    Sheaf (ProEt.topology X) A ⥤ Sheaf X.smallEtaleTopology A :=
  (toProEt X).sheafPushforwardContinuous A X.smallEtaleTopology (ProEt.topology X)

@[inherit_doc comparisonLowerStar]
scoped notation "ν_*(" X ")[" A "]" => comparisonLowerStar A X

/-- The comparison functor `ν^* : Sh(X_ét, A) ⥤ Sh(X_proét, A)`: left Kan extension of
presheaves along the inclusion `AlgebraicGeometry.toProEt X` of the small étale site
into the small pro-étale site, followed by sheafification. It is left adjoint to
`ProEtale.comparisonLowerStar`. -/
noncomputable def comparisonUpperStar :
    Sheaf X.smallEtaleTopology A ⥤ Sheaf (ProEt.topology X) A :=
  Functor.sheafPullbackConstruction.sheafPullback (toProEt X) A X.smallEtaleTopology
    (ProEt.topology X)

@[inherit_doc comparisonUpperStar]
scoped notation "ν^*(" X ")[" A "]" => comparisonUpperStar A X

/-- The adjunction `ν^* ⊣ ν_*` between étale and pro-étale sheaves. -/
noncomputable def comparisonAdjunction : ν^*(X)[A] ⊣ ν_*(X)[A] :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (toProEt X) A
    X.smallEtaleTopology (ProEt.topology X)

/-- `ν_*` is a right adjoint. -/
instance : ν_*(X)[A].IsRightAdjoint :=
  (comparisonAdjunction A X).isRightAdjoint

/-- `ν^*` is a left adjoint. -/
instance : ν^*(X)[A].IsLeftAdjoint :=
  (comparisonAdjunction A X).isLeftAdjoint

example : PreservesFiniteLimits ν_*(X)[A] := inferInstance

/-- The comparison functor `ν^*` is left exact. -/
instance preservesFiniteLimits_comparisonUpperStar : PreservesFiniteLimits ν^*(X)[A] :=
  -- the composite of the inclusion of sheaves into presheaves, the left Kan extension along
  -- the opposite of the representably flat functor `toProEt X` and sheafification, all of
  -- which are left exact
  inferInstanceAs <| PreservesFiniteLimits <|
    Functor.sheafPullbackConstruction.sheafPullback (toProEt X) A X.smallEtaleTopology
      (ProEt.topology X)

example : PreservesFiniteColimits ν^*(X)[A] := inferInstance

/-- The restriction `ν_*` is additive. -/
instance additive_comparisonLowerStar : ν_*(X)[A].Additive where

/-- The comparison functor `ν^*` is additive. -/
instance additive_comparisonUpperStar : ν^*(X)[A].Additive :=
  (comparisonAdjunction A X).left_adjoint_additive

/-- The comparison functor `ν^*` preserves homology. -/
instance preservesHomology_comparisonUpperStar : ν^*(X)[A].PreservesHomology :=
  -- the two fields of `PreservesHomology` are `autoParam`s, found by instance synthesis
  {}

end AlgebraicGeometry.ProEtale
