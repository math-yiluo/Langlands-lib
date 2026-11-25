/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.NatIso
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.AbsoluteFrobenius

/-!
# The absolute Frobenius acts as the identity on the derived étale topos

For a scheme `X` of characteristic `p` with absolute `p ^ n`-power Frobenius `F_X`, the
isomorphism `(F_X)^* ≅ (𝟙 X)^*` of `AlgebraicGeometry.Etale.upperStarIterateFrobeniusIso`
induces an isomorphism `L(F_X)^* ≅ L(𝟙 X)^*` of derived pullbacks, compatible with derived
pullback along morphisms of schemes of characteristic `p`.

## Main definitions

- `AlgebraicGeometry.Etale.leftDerivedUpperStarIterateFrobeniusIso`: `L(F_X)^* ≅ L(𝟙 X)^*`.

## Main results

- `AlgebraicGeometry.Etale.leftDerivedUpperStarIterateFrobeniusIso_naturality`: the derived
  form of `AlgebraicGeometry.Etale.upperStarIterateFrobeniusIso_naturality`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

variable {p : ℕ} (hp : p.Prime) {X : Scheme.{u}} (hX : (p : Γ(X, ⊤)) = 0) (n : ℕ)

/-- Étale analogue of blueprint `lemma-scheme-frobenius-geometric-frobenius--1` (stated there for
the small pro-étale site), derived form: the absolute Frobenius acts as the
identity on the derived étale topos. For a scheme `X` of characteristic `p`, the derived pullback
`L(F_X)^*` along the absolute `p ^ n`-power Frobenius is isomorphic to the derived pullback
`L(𝟙 X)^*` along the identity: it is the derived functor of
`AlgebraicGeometry.Etale.upperStarIterateFrobeniusIso`. -/
noncomputable def leftDerivedUpperStarIterateFrobeniusIso :
    L((X.iterateFrobenius hp hX n)^*[A]) ≅ L((𝟙 X)^*[A]) :=
  Functor.leftDerivedFunctorNatIso _ (upperStarIterateFrobeniusIso A hp hX n)

variable {Y : Scheme.{u}} (hY : (p : Γ(Y, ⊤)) = 0) (f : X ⟶ Y)

/-- The isomorphisms `L(F_X)^* ≅ L(𝟙 X)^*` of
`AlgebraicGeometry.Etale.leftDerivedUpperStarIterateFrobeniusIso` are compatible with derived
pullback along a morphism `f : X ⟶ Y` of schemes of characteristic `p`: writing
`F_X ≫ f = f ≫ F_Y`, the two isomorphisms `L(F_X ≫ f)^* ≅ Lf^*`
```
L(F_X ≫ f)^* ≅ LF_Y^* ⋙ Lf^* ≅ L(𝟙 Y)^* ⋙ Lf^* ≅ Lf^*
L(F_X ≫ f)^* ≅ Lf^* ⋙ LF_X^* ≅ Lf^* ⋙ L(𝟙 X)^* ≅ Lf^*
```
agree. This is the derived form of
`AlgebraicGeometry.Etale.upperStarIterateFrobeniusIso_naturality`, to which it reduces by
the functoriality of the derived isomorphisms of exact functors. -/
theorem leftDerivedUpperStarIterateFrobeniusIso_naturality
    (hFf : X.iterateFrobenius hp hX n ≫ f = f ≫ Y.iterateFrobenius hp hY n) :
    leftDerivedUpperStarComp A f (Y.iterateFrobenius hp hY n) (X.iterateFrobenius hp hX n ≫ f)
        hFf ≪≫
      Functor.isoWhiskerRight (leftDerivedUpperStarIterateFrobeniusIso A hp hY n) L((f)^*[A]) ≪≫
      (leftDerivedUpperStarComp A f (𝟙 Y) f (Category.comp_id f).symm).symm =
    leftDerivedUpperStarComp A (X.iterateFrobenius hp hX n) f (X.iterateFrobenius hp hX n ≫ f)
        rfl ≪≫
      Functor.isoWhiskerLeft L((f)^*[A]) (leftDerivedUpperStarIterateFrobeniusIso A hp hX n) ≪≫
      (leftDerivedUpperStarComp A (𝟙 X) f f (Category.id_comp f).symm).symm := by
  have key := congrArg Iso.hom (congrArg (Functor.leftDerivedFunctorNatIso _)
    (upperStarIterateFrobeniusIso_naturality A hp hX n hY f))
  simp only [Functor.leftDerivedFunctorNatIso_trans, Functor.leftDerivedFunctorNatIso_symm,
    Iso.trans_hom, Iso.symm_hom] at key
  ext : 1
  simp only [leftDerivedUpperStarComp, leftDerivedUpperStarIterateFrobeniusIso, Iso.trans_hom,
    Iso.symm_hom, Iso.trans_inv, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Category.assoc]
  rw [← reassoc_of% (Functor.leftDerivedFunctorNatIso_isoWhiskerRight _
      (upperStarIterateFrobeniusIso A hp hY n) (f)^*[A]),
    ← reassoc_of% (Functor.leftDerivedFunctorNatIso_isoWhiskerLeft (f)^*[A]
      (upperStarIterateFrobeniusIso A hp hX n)),
    Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc]
  exact key

/-- The component form of
`AlgebraicGeometry.Etale.leftDerivedUpperStarIterateFrobeniusIso_naturality`. -/
lemma leftDerivedUpperStarIterateFrobeniusIso_naturality_app
    (hFf : X.iterateFrobenius hp hX n ≫ f = f ≫ Y.iterateFrobenius hp hY n)
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (leftDerivedUpperStarComp A f (Y.iterateFrobenius hp hY n)
        (X.iterateFrobenius hp hX n ≫ f) hFf).hom.app M ≫
      L((f)^*[A]).map ((leftDerivedUpperStarIterateFrobeniusIso A hp hY n).hom.app M) ≫
      (leftDerivedUpperStarComp A f (𝟙 Y) f (Category.comp_id f).symm).inv.app M =
    (leftDerivedUpperStarComp A (X.iterateFrobenius hp hX n) f
        (X.iterateFrobenius hp hX n ≫ f) rfl).hom.app M ≫
      (leftDerivedUpperStarIterateFrobeniusIso A hp hX n).hom.app (L((f)^*[A]).obj M) ≫
      (leftDerivedUpperStarComp A (𝟙 X) f f (Category.id_comp f).symm).inv.app M := by
  have h := NatTrans.congr_app (congrArg Iso.hom
    (leftDerivedUpperStarIterateFrobeniusIso_naturality A hp hX n hY f hFf)) M
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Category.assoc] using h

end Etale

end AlgebraicGeometry
