/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!

# Stalks of a pushforward along a closed immersion of étale sheaves

Pushing an étale sheaf forward along a *closed immersion* `i : Z ⟶ X` does not change stalks
at points of `Z`: the stalk of `i_* H` at `s ≫ i` is the stalk of `H` at `s`, for a geometric
point `s : Spec Ω ⟶ Z`.

Here `(i)_*[A]` is restriction along base change `i.Etale`, so both stalks are filtered
colimits over categories of pointed étale neighbourhoods, and the comparison is the
initiality of `AlgebraicGeometry.Scheme.pointSmallEtaleElementsBaseChange`, which sends a
pointed étale neighbourhood `(V, v)` of `s ≫ i` in `X` to `(V ×_X Z, (v, s))`. That
initiality is `AlgebraicGeometry.Scheme.initial_pointSmallEtaleElementsBaseChange` of
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`, and it is where the geometric
input — the local lifting of étale morphisms along a closed immersion — enters.

## Main definitions

- `AlgebraicGeometry.Etale.lowerStarCompPresheafFiberIso`: the presheaf form of the
  comparison, an isomorphism of functors on `A`-valued presheaves.
- `AlgebraicGeometry.Etale.lowerStarCompSheafFiberIso`: the natural isomorphism
  `(i)_*[A] ⋙ (pointSmallEtale (s ≫ i)).sheafFiber ≅ (pointSmallEtale s).sheafFiber`,
  that is, `(i_* H)_(s ≫ i) ≅ H_s`.

## Implementation notes

Base change occurs under its two interchangeable names: `AlgebraicGeometry.Etale.lowerStar`
is defined along `MorphismProperty.Over.pullback @Etale ⊤ i`, whereas the point API is
applied to the definitionally equal `AlgebraicGeometry.Scheme.Hom.Etale i`, whose stated
type `X.Etale ⥤ Z.Etale` is the one the geometric points of `Z` and `X` come with. Both
names appear below, each where its instances are available.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Z)

/-- The presheaf form of `AlgebraicGeometry.Etale.lowerStarCompSheafFiberIso`: restricting an
`A`-valued presheaf on the small étale site of `Z` along base change by a closed immersion
`i : Z ⟶ X` and taking the fibre at the geometric point `s ≫ i` of `X` gives the fibre at
`s`. Both sides are colimits over categories of pointed étale neighbourhoods, and the
comparison is `AlgebraicGeometry.Scheme.initial_pointSmallEtaleElementsBaseChange` read
through `CategoryTheory.Functor.Final.colimIso`. -/
noncomputable def Etale.lowerStarCompPresheafFiberIso :
    (Functor.whiskeringLeft _ _ A).obj i.Etale.op ⋙ (pointSmallEtale (s ≫ i)).presheafFiber ≅
      (pointSmallEtale s).presheafFiber :=
  have := Scheme.initial_pointSmallEtaleElementsBaseChange i s
  Functor.isoWhiskerLeft
    ((Functor.whiskeringLeft _ _ A).obj (Functor.Elements.π (pointSmallEtale s).fiber).op)
    (Functor.Final.colimIso (pointSmallEtaleElementsBaseChange i s).op)

omit [HasSmallSiteSheafify A] in
/-- The comparison `AlgebraicGeometry.Etale.lowerStarCompPresheafFiberIso` on the canonical
maps from the sections over a pointed étale neighbourhood: the section of `P` over
`V ×_X Z` attached to a point `y` of `V` above `s ≫ i` has the same image in the fibre of
`P` at `s` whether it is seen as a section of the restriction of `P` over `(V, y)` or as a
section of `P` over the pointed étale neighbourhood `(V ×_X Z, y)` of `s`. In other words
the triangle of germ maps
```
                   (i.Etale.op ⋙ P)(V) = P(V ×_X Z)
                     /                          \
     toPresheafFiber at (V, y)          toPresheafFiber at (V ×_X Z, y)
                   /                              \
                  ↓                                ↓
  ((i.Etale.op ⋙ P) at s ≫ i) --- lowerStarCompPresheafFiberIso ---> (P at s)
```
commutes. -/
lemma Etale.toPresheafFiber_lowerStarCompPresheafFiberIso_hom_app (P : Z.Etaleᵒᵖ ⥤ A)
    (V : X.Etale) (y : (pointSmallEtale (s ≫ i)).fiber.obj V) :
    (pointSmallEtale (s ≫ i)).toPresheafFiber V y (i.Etale.op ⋙ P) ≫
        (Etale.lowerStarCompPresheafFiberIso A i s).hom.app P =
      (pointSmallEtale s).toPresheafFiber (i.Etale.obj V)
        ((pointSmallEtaleFiberEtaleIso i s).inv.app V y) P :=
  have := Scheme.initial_pointSmallEtaleElementsBaseChange i s
  Functor.Final.ι_colimitIso_hom (pointSmallEtaleElementsBaseChange i s).op
    ((Functor.Elements.π (pointSmallEtale s).fiber).op ⋙ P)
    (op (Functor.elementsMk _ V y))

/-- Blueprint `lemma-finite-direct-images--1`: **The stalk of a pushforward along a closed
immersion.** For a closed immersion
`i : Z ⟶ X` and a geometric point `s : Spec Ω ⟶ Z`, the stalk of `i_* H` at the geometric
point `s ≫ i` of `X` is the stalk of `H` at `s`, naturally in the sheaf `H`.

On underlying presheaves `(i)_*[A]` *is* restriction along base change, so this is
`AlgebraicGeometry.Etale.lowerStarCompPresheafFiberIso` restricted to sheaves. -/
noncomputable def Etale.lowerStarCompSheafFiberIso :
    (i)_*[A] ⋙ (pointSmallEtale (s ≫ i)).sheafFiber ≅ (pointSmallEtale s).sheafFiber :=
  Functor.isoWhiskerLeft (sheafToPresheaf _ A) (Etale.lowerStarCompPresheafFiberIso A i s)

end AlgebraicGeometry
