/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.Mathlib.CategoryTheory.Limits.HasLimits
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-!

# Stalks of a pullback of étale sheaves

For a morphism of schemes `f : X ⟶ Y`, pulling an étale sheaf back to `X` does not change
its stalks: the stalk of `f^* F` at a geometric point `s : Spec Ω ⟶ X` is the stalk of `F`
at the image point `s ≫ f`.

The pullback `(f)^*[A]` of `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence` is the sheaf
pullback along base change `f.Etale`. Mathlib's
`CategoryTheory.GrothendieckTopology.Point.sheafFiberComapIso` computes the fibre functor on
sheaves of the point `Point.comap` of a representably flat, cover preserving functor as the
sheaf pullback followed by the fibre functor of the original point; and by
`AlgebraicGeometry.Scheme.pointSmallEtaleComapIso` the point obtained from `s` along base
change is the geometric point `s ≫ f`.

## Main results

- `AlgebraicGeometry.Scheme.Hom.hasLeftKanExtension_op_etale`: all left Kan extensions of
  `A`-valued presheaves along the opposite of base change `f.Etale` exist. This is what
  makes `f^*` available as a sheaf pullback along `f.Etale`.
- `AlgebraicGeometry.Etale.upperStarCompSheafFiberIso`: the natural isomorphism
  `(f)^*[A] ⋙ (pointSmallEtale s).sheafFiber ≅ (pointSmallEtale (s ≫ f)).sheafFiber`,
  that is, `(f^* F)_s ≅ F_(s ≫ f)`, naturally in the sheaf `F`.
- `AlgebraicGeometry.Etale.upperStarCompUliftSheafFiberIso`: the same isomorphism for the
  universe-lifted points `CategoryTheory.GrothendieckTopology.Point.ulift`.

## Implementation notes

Base change occurs under its two interchangeable names: `AlgebraicGeometry.Etale.upperStar`
is defined along `MorphismProperty.Over.pullback @Etale ⊤ f`, whereas the point API is
applied to the definitionally equal `AlgebraicGeometry.Scheme.Hom.Etale f`, whose stated
type `Y.Etale ⥤ X.Etale` is the one the geometric points of `X` and `Y` come with. Both
names appear below, each where its instances are available.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ X)

/-- All left Kan extensions of `A`-valued presheaves along the opposite of base change
`f.Etale` exist. This is an instance of
`CategoryTheory.Functor.hasPointwiseLeftKanExtension_of_hasColimitsOfSize`, restated
for `AlgebraicGeometry.Scheme.Hom.Etale`; it is what makes the sheaf pullback along
`f.Etale` available, hence also the fibre functor on sheaves of the point
`(pointSmallEtale s).comap f.Etale _`. -/
instance Scheme.Hom.hasLeftKanExtension_op_etale (G : Y.Etaleᵒᵖ ⥤ A) :
    f.Etale.op.HasLeftKanExtension G :=
  inferInstance

/-- The stalk of a pullback of étale sheaves is the stalk at the image point: for a morphism
of schemes `f : X ⟶ Y` and a geometric point `s : Spec Ω ⟶ X`, the stalk of `f^* F` at `s`
is the stalk of `F` at `s ≫ f`, naturally in the sheaf `F`.

The three steps are the comparison
`CategoryTheory.Functor.sheafPullbackConstruction.sheafPullbackIso` between `(f)^*[A]` and
the abstract sheaf pullback along base change, the isomorphism
`CategoryTheory.GrothendieckTopology.Point.sheafFiberComapIso` of the sheaf pullback with
the fibre functor of the point obtained from `s` by `Point.comap`, and the identification
`AlgebraicGeometry.Scheme.pointSmallEtaleComapIso` of that point with `s ≫ f`.
(blueprint: `lemma-openclosed-stalk-upperstar`) -/
noncomputable def Etale.upperStarCompSheafFiberIso :
    (f)^*[A] ⋙ (pointSmallEtale s).sheafFiber ≅ (pointSmallEtale (s ≫ f)).sheafFiber :=
  Functor.isoWhiskerRight
      (Functor.sheafPullbackConstruction.sheafPullbackIso
        (MorphismProperty.Over.pullback @Etale ⊤ f) A _ _).symm _ ≪≫
    (GrothendieckTopology.Point.sheafFiberComapIso (pointSmallEtale s) f.Etale
      (Hom.coverPreserving_etale f) A).symm ≪≫
    GrothendieckTopology.Point.sheafFiberIso (pointSmallEtaleComapIso f s)

/-- The universe-lifted form of `AlgebraicGeometry.Etale.upperStarCompSheafFiberIso`: the
stalk of `f^* F` at the geometric point `s`, taken at the universe of the coefficients, is
the stalk of `F` at `s ≫ f`. This is the form in which the comparison is used, since the
coefficient categories of the six functor formalism are concrete over `Type (u + 1)` and the
fibre functor of `pointSmallEtale s` takes values in `Type u`.
(blueprint: `lemma-openclosed-stalk-upperstar`) -/
noncomputable def Etale.upperStarCompUliftSheafFiberIso :
    (f)^*[A] ⋙ ((pointSmallEtale s).ulift.{u + 1}).sheafFiber ≅
      ((pointSmallEtale (s ≫ f)).ulift.{u + 1}).sheafFiber :=
  Functor.isoWhiskerLeft _ ((pointSmallEtale s).uliftSheafFiberIso A) ≪≫
    upperStarCompSheafFiberIso A f s ≪≫
    ((pointSmallEtale (s ≫ f)).uliftSheafFiberIso A).symm

end AlgebraicGeometry
