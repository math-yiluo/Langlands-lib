/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Defs

/-!

# Derived Upper Star and Lower Star

The derived pullback and pushforward of étale sheaves are *not* given definitions of
their own: they are the generic derived-functor constructions of the folder
`WeilConjectures.CategoryTheory.DerivedCategory` applied to the underived pullback
`(g)^*[A]` and pushforward `(g)_*[A]`, and they are written by nesting the generic
notations inside the underived ones:

| derived functor | notation | meaning |
| --- | --- | --- |
| `Rg_* : D(Z_ét) ⥤ D(Y_ét)` | `R((g)_*[A])` | `(g)_*[A].rightDerivedFunctor` |
| `Rg_* : D⁺(Z_ét) ⥤ D⁺(Y_ét)` | `R+((g)_*[A])` | `(g)_*[A].rightDerivedFunctorPlus` |
| `Lg^* : D(Y_ét) ⥤ D(Z_ét)` | `L((g)^*[A])` | `(g)^*[A].leftDerivedFunctor` |
| `g^* : D(Y_ét) ⥤ D(Z_ét)` | `D((g)^*[A])` | `(g)^*[A].mapDerivedCategory` |
| `g^* : D⁺(Y_ét) ⥤ D⁺(Z_ét)` | `D+((g)^*[A])` | `(g)^*[A].mapDerivedCategoryPlus` |

The generic notations `R(-)`, `R+(-)`, `L(-)`, `D(-)` and `D+(-)` are scoped in the
`CategoryTheory.Functor` namespace, so a file using them needs
`open scoped CategoryTheory.Functor`. Each row above is recorded below as an `example`,
at the place where a definition of the corresponding functor would have stood, so that
the type of the functor is spelled out.

## Main results

- `AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory` : the derived
  pullback `L((g)^*[A])` is the functor `D((g)^*[A])` induced levelwise by the exact
  functor `g^*`.

- `AlgebraicGeometry.Etale.leftDerivedUpperStarComp` : the composition isomorphism
  `L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*`.

- `AlgebraicGeometry.Etale.leftDerivedUpperStarHomologyFunctorIso` : the derived pullback
  commutes with the homology functors, `H^n ⋙ g^* ≅ Lg^* ⋙ H^n`.

- `AlgebraicGeometry.Etale.singleFunctorCompLeftDerivedUpperStarIso` : the derived
  pullback of a sheaf placed in degree `0` is the pullback of the sheaf placed in degree
  `0`.

- `AlgebraicGeometry.Etale.mapDerivedUpperStarLowerStarAdjunction`,
  `AlgebraicGeometry.Etale.derivedUpperStarLowerStarAdjunction` and
  `AlgebraicGeometry.Etale.derivedUpperStarLowerStarAdjunctionPlus` : the derived
  adjunctions `D((g)^*[A]) ⊣ R((g)_*[A])`, `L((g)^*[A]) ⊣ R((g)_*[A])` and
  `D+((g)^*[A]) ⊣ R+((g)_*[A])`. The first one needs no monoidal structure on `A`.

- `AlgebraicGeometry.Etale.rightDerivedLowerStarComp` : the composition isomorphism
  `Rg₁_* ⋙ Rg₂_* ≅ R(g₁ ≫ g₂)_*`, conjugate to the composition isomorphism of the functors
  `D(g^*)`. It needs no monoidal structure on `A`.

- `AlgebraicGeometry.Etale.rightDerivedLowerStarCongr` : the isomorphism `Rg₁_* ≅ Rg₂_*`
  induced by an equality `g₁ = g₂`.

- `AlgebraicGeometry.Etale.linear_rightDerivedLowerStar` and
  `AlgebraicGeometry.Etale.linear_leftDerivedUpperStar` : for a `Λ`-linear `A`, the derived
  functors `Rg_*` and `Lg^*` are `Λ`-linear.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section DerivedLowerStar

namespace Etale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The total right derived functor `Rg_* : D(Z_ét) ⥤ D(Y_ét)` of the pushforward `g_*`
along an arbitrary morphism `g : Z ⟶ Y` on the unbounded derived categories of étale
sheaves.

It is not a definition of its own: it is the generic `Functor.rightDerivedFunctor`,
written `R(-)`, applied to the underived pushforward `(g)_*[A]`. -/
noncomputable example :
    DerivedCategory (Sheaf Z.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  R((g)_*[A])

/-- The right derived functor `Rg_* : D⁺(Z_ét) ⥤ D⁺(Y_ét)` of the pushforward `g_*` on
the *bounded below* derived categories of étale sheaves: the generic
`Functor.rightDerivedFunctorPlus`, written `R+(-)`, applied to `(g)_*[A]`. -/
noncomputable example :
    DerivedCategory.Plus (Sheaf Z.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  R+((g)_*[A])

/-- The pushforward `g_*` preserves K-injective complexes, being right adjoint to the exact
pullback `g^*`. -/
instance preservesKInjectiveComplexes_lowerStar : ((g)_*[A]).PreservesKInjectiveComplexes :=
  (Etale.upperStarLowerStarAdjunction A g).preservesKInjectiveComplexes

/-- The derived adjunction `g^* ⊣ Rg_*` on the unbounded derived categories of étale sheaves,
where the pullback `g^*`, being exact, is applied levelwise. Unlike
`Etale.derivedUpperStarLowerStarAdjunction`, it needs no monoidal structure on `A`. -/
noncomputable def mapDerivedUpperStarLowerStarAdjunction : D((g)^*[A]) ⊣ R((g)_*[A]) :=
  (Etale.upperStarLowerStarAdjunction A g).mapDerivedCategoryRightDerivedAdjunction

/-- The total right derived pushforward `Rg_*` on the unbounded derived categories of étale
sheaves is additive, being right adjoint to `D(g^*)`. -/
instance additive_rightDerivedLowerStar : (R((g)_*[A])).Additive :=
  (mapDerivedUpperStarLowerStarAdjunction A g).right_adjoint_additive

/-- The isomorphism `Rg₁_* ≅ Rg₂_*` induced by an equality `g₁ = g₂`. -/
noncomputable def rightDerivedLowerStarCongr {g₁ g₂ : Z ⟶ Y} (h : g₁ = g₂) :
    R((g₁)_*[A]) ≅ R((g₂)_*[A]) :=
  eqToIso (congrArg (fun g ↦ R((g)_*[A])) h)

@[simp]
lemma rightDerivedLowerStarCongr_refl : rightDerivedLowerStarCongr A (g₁ := g) rfl = Iso.refl _ :=
  rfl

@[simp]
lemma rightDerivedLowerStarCongr_hom_app {g₁ g₂ : Z ⟶ Y} (h : g₁ = g₂)
    (K : DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    (rightDerivedLowerStarCongr A h).hom.app K = eqToHom (by subst h; rfl) := by
  subst h
  rfl

@[simp]
lemma rightDerivedLowerStarCongr_inv_app {g₁ g₂ : Z ⟶ Y} (h : g₁ = g₂)
    (K : DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    (rightDerivedLowerStarCongr A h).inv.app K = eqToHom (by subst h; rfl) := by
  subst h
  rfl

/-- The composition isomorphism `Rg₁_* ⋙ Rg₂_* ≅ R(g₁ ≫ g₂)_*` of the derived direct images.
It is the conjugate, under the adjunctions `D(g^*) ⊣ Rg_*` of
`AlgebraicGeometry.Etale.mapDerivedUpperStarLowerStarAdjunction`, of the composition
isomorphism `D((g₁ ≫ g₂)^*) ≅ D(g₂^*) ⋙ D(g₁^*)` of the functors induced by the exact
pullbacks:
```
   D((g₁ ≫ g₂)^*)  ≅  D(g₂^*) ⋙ D(g₁^*)
         ⊣                    ⊣
   R(g₁ ≫ g₂)_*    ≅  Rg₁_* ⋙ Rg₂_*
```
`conjugateIsoEquiv` turns an isomorphism of left adjoints into an isomorphism of right
adjoints in the opposite direction, so the isomorphism of left adjoints is inverted before
and the result after. Unlike `AlgebraicGeometry.Etale.leftDerivedUpperStarComp`, this needs no
monoidal structure on `A`. -/
noncomputable def rightDerivedLowerStarComp {T S U : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ U) :
    R((g₁)_*[A]) ⋙ R((g₂)_*[A]) ≅ R((g₁ ≫ g₂)_*[A]) :=
  (conjugateIsoEquiv (mapDerivedUpperStarLowerStarAdjunction A (g₁ ≫ g₂))
    ((mapDerivedUpperStarLowerStarAdjunction A g₂).comp
      (mapDerivedUpperStarLowerStarAdjunction A g₁))
    (Functor.mapDerivedCategoryNatIso (Etale.upperStarComp A g₁ g₂) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm).symm).symm

variable (Λ : Type*) [Ring Λ] [Linear Λ A] in
/-- If `A` is `Λ`-linear, the total right derived pushforward `Rg_*` is `Λ`-linear, being right
adjoint to the functor `D(g^*)` induced by the `Λ`-linear exact functor `g^*`. -/
instance linear_rightDerivedLowerStar : (R((g)_*[A])).Linear Λ :=
  (mapDerivedUpperStarLowerStarAdjunction A g).right_adjoint_linear

end Etale

end DerivedLowerStar

section DerivedUpperStar

/-!
## The derived pullback `Lg^*`

The pullback `g^* = Etale.upperStar` is left derived using the K-flat left
derivability structure of `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs`.
This requires the source sheaf category `Sheaf Y.smallEtaleTopology A` to carry a
preadditive monoidal structure whose tensor product preserves colimits, to have countable
coproducts and exact `ℤ`-indexed colimits, and to admit functorial flat resolutions.
These inputs are stated as hypotheses on the coefficient category `A` only; they are
supplied for the sheaf categories by the instances of the folder
`WeilConjectures.CategoryTheory.GrothendieckAbelian`, with the monoidal structure and its
compatibility with colimits provided by its `Monoidal` subfolder, and its preadditivity
by `CategoryTheory.Sheaf.monoidalPreadditive`, which holds for any sheaf category.

The functorial flat resolutions of étale sheaves are
`AlgebraicGeometry.Etale.hasFunctorialFlatResolution_sheaf`
(`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution`: a flat separator of
the sheaf category on an essentially small site, from one of `A`), and the tensor-colimit input
is `AlgebraicGeometry.Etale.preservesColimitsOfSize_tensorLeft_sheaf` (Day's reflection theorem).

The additivity and exactness of `g^*` are `Etale.additive_upperStar`,
`Etale.preservesFiniteLimits_upperStar` and `Etale.preservesHomology_upperStar` of
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`; the left exactness there rests on the
`HasSheafify` instance for the small étale site of `Z` and on left exactness of
the left Kan extension along the opposite of base change, both global instances of the
folder `WeilConjectures.CategoryTheory.GrothendieckAbelian` (for an étale `g` the latter
is proved directly). Since `g^*` is exact, it preserves in particular all K-flat
quasi-isomorphisms, which is the input needed by the derivability-structure machinery.
-/

open MonoidalCategory Etale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/- The preadditive monoidal structure on the coefficient category. It is assumed closed
and *symmetric* (as is the intended application `A = ModuleCat.{u + 1} Λ` for a
commutative ring `Λ`): that is what makes the class of sheafification-inverting
morphisms of presheaves monoidal, hence what lets the monoidal structure descend to the
étale sheaf categories, see
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs`. Closedness and the
symmetry moreover make the étale sheaf categories monoidal closed by Day's reflection
theorem, hence make tensoring by a fixed sheaf preserve colimits, which is what the
tensor product of complexes needs, see
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits`; no further
tensor-colimit hypothesis on `A` is required. -/
variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]

/- Functorial flat resolutions on the coefficient category; they induce functorial flat
resolutions of étale sheaves via `Etale.hasFunctorialFlatResolution_sheaf`. -/
variable [Abelian.HasFunctorialFlatResolution A]

namespace Etale

/-- The total left derived functor `Lg^* : D(Y_ét) ⥤ D(Z_ét)` of the pullback `g^*`
along an arbitrary morphism `g : Z ⟶ Y` on the unbounded derived categories of étale
sheaves, defined via the K-flat left derivability structure: `Lg^*` is computed by
applying `g^*` to a K-flat resolution.

It is not a definition of its own: it is the generic `Functor.leftDerivedFunctor`,
written `L(-)`, applied to the underived pullback `(g)^*[A]`.

Since `g^*` is exact, the counit `Lg^* ∘ Q ⟶ Q ∘ g^*` is in fact an isomorphism
everywhere; the construction via the derivability structure is uniform in the functor
and applies verbatim once `g^*` is replaced by a non-exact functor (e.g. the pullback
of sheaves of modules over a varying sheaf of rings). -/
noncomputable example :
    DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Z.smallEtaleTopology A) :=
  L((g)^*[A])

/-- The compatibility of the derived pullback with the levelwise functor: the total left
derived functor `Lg^*`, computed via K-flat resolutions, is canonically isomorphic to
the functor induced by the exact functor `g^*` on the derived categories.

```
                        Lg^*
                 -------------------->
        D(Y_ét)            ≅             D(Z_ét)
                 -------------------->
                     D((g)^*[A])
```

This is `Functor.leftDerivedFunctorIsoMapDerivedCategory` at `g^*`. -/
noncomputable def leftDerivedUpperStarIsoMapDerivedCategory :
    L((g)^*[A]) ≅ D((g)^*[A]) :=
  (g)^*[A].leftDerivedFunctorIsoMapDerivedCategory

/-- The derived pullback `Lg^*` is additive: it is isomorphic to the functor `D(g^*)` induced by
the additive exact functor `g^*`. -/
instance additive_leftDerivedUpperStar : (L((g)^*[A])).Additive :=
  Functor.additive_of_iso (leftDerivedUpperStarIsoMapDerivedCategory A g).symm

variable (Λ : Type*) [Ring Λ] [Linear Λ A] in
/-- If `A` is `Λ`-linear, the derived pullback `Lg^*` is `Λ`-linear: it is isomorphic to the
functor `D(g^*)` induced by the `Λ`-linear exact functor `g^*`. -/
instance linear_leftDerivedUpperStar : (L((g)^*[A])).Linear Λ :=
  Functor.linear_of_iso Λ (leftDerivedUpperStarIsoMapDerivedCategory A g).symm

/-- The composition isomorphism `L(g₁ ≫ g₂)^* ≅ Lg₂^* ∘ Lg₁^*` of derived pullbacks,
obtained from the underived composition isomorphism `Etale.upperStarComp` and the
compatibility of left derivation with `mapDerivedCategory` for exact functors. As for
`Etale.upperStarComp`, the composite may be given as any `g₁₂` with `g₁₂ = g₁ ≫ g₂`.

```
                 L(g₁ ≫ g₂)^*
D(R_ét) -------------------------------> D(T_ét)
      |                                    ^
      |                                    |
      +---------> D(S_ét) -----------------+
        Lg₂^*              Lg₁^*
```
-/
noncomputable def leftDerivedUpperStarComp {T S R : Scheme.{u}}
    (g₁ : T ⟶ S) (g₂ : S ⟶ R) (g₁₂ : T ⟶ R := g₁ ≫ g₂)
    (hg₁₂ : g₁₂ = g₁ ≫ g₂ := by cat_disch) :
    L((g₁₂)^*[A]) ≅ L((g₂)^*[A]) ⋙ L((g₁)^*[A]) :=
  Functor.leftDerivedFunctorNatIso _ (Etale.upperStarComp A g₁ g₂ g₁₂ hg₁₂) ≪≫
    Functor.leftDerivedFunctorCompIso (g₂)^*[A] (g₁)^*[A]

/-- The exactness comparison `H^n ∘ g^* ≅ g^* ∘ H^n`: since the underived pullback `g^*`
on étale sheaves is exact, applying it to the `n`-th homology sheaf of an object of the
derived category computes the `n`-th homology sheaf of the derived pullback.

```
                H^n
D(Y_ét) -----------------> Sh(Y_ét)
   |                           |
 Lg^*                        g^*
   |                           |
   v                           v
D(Z_ét) -----------------> Sh(Z_ét)
                H^n
```

This is `Functor.leftDerivedFunctorHomologyFunctorIso` at `g^*`. -/
noncomputable def leftDerivedUpperStarHomologyFunctorIso (n : ℤ) :
    DerivedCategory.homologyFunctor (Sheaf Y.smallEtaleTopology A) n ⋙ (g)^*[A] ≅
      L((g)^*[A]) ⋙ DerivedCategory.homologyFunctor (Sheaf Z.smallEtaleTopology A) n :=
  (g)^*[A].leftDerivedFunctorHomologyFunctorIso n

/-- The single-degree comparison for the derived pullback: since the underived pullback
`g^*` on étale sheaves is exact, the derived pullback of a sheaf placed in degree `0` is
the pullback of the sheaf placed in degree `0`, `Lg^*(F[0]) ≅ (g^* F)[0]`.

```
                (-)[0]
Sh(Y_ét) -----------------> D(Y_ét)
    |                           |
    g^*                       Lg^*
    |                           |
    v                           v
Sh(Z_ét) -----------------> D(Z_ét)
                (-)[0]
```

This is `Functor.singleFunctorCompLeftDerivedFunctorIso` at `g^*`. -/
noncomputable def singleFunctorCompLeftDerivedUpperStarIso :
    DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology A) 0 ⋙ L((g)^*[A]) ≅
      (g)^*[A] ⋙ DerivedCategory.singleFunctor (Sheaf Z.smallEtaleTopology A) 0 :=
  (g)^*[A].singleFunctorCompLeftDerivedFunctorIso

end Etale

end DerivedUpperStar

section DerivedUpperLowerStarAdjunction

/-!
## The derived adjunction `Lg^* ⊣ Rg_*`

The adjunction `g^* ⊣ g_*` between the pullback and the pushforward of étale sheaves
induces an adjunction `Lg^* ⊣ Rg_*` between their total derived functors on the
unbounded derived categories, by
`CategoryTheory.Adjunction.derivedAdjunction`
(`WeilConjectures.CategoryTheory.DerivedCategory.Adjunction`): the left adjoint is
derived via the K-flat left derivability structure on `D(Y_ét)` and the right adjoint
via the K-injective right derivability structure on `D(Z_ét)`, and the two
"absoluteness" hypotheses of mathlib's abstract theorem `Adjunction.derived` hold
because the derived-functor comparison maps are isomorphisms on K-flat, respectively
K-injective, complexes.

The hypotheses of this section are those of the section `DerivedUpperStar`: the
K-injective resolutions on the pushforward side are supplied by the sheaf category
being Grothendieck abelian.
-/

open MonoidalCategory Etale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/- The closed symmetric preadditive monoidal structure on the coefficient category, as in
the section `DerivedUpperStar`; it is what the monoidal transport instances of
`WeilConjectures.CategoryTheory.GrothendieckAbelian` are stated under. -/
variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]

/- Functorial flat resolutions on the coefficient category, as in the section
`DerivedUpperStar`. -/
variable [Abelian.HasFunctorialFlatResolution A]

namespace Etale

/-- The derived adjunction `Lg^* ⊣ Rg_*` between the total derived functors of the
pullback and the pushforward along an arbitrary morphism `g : Z ⟶ Y` on the unbounded
derived categories of étale sheaves, induced by the adjunction `g^* ⊣ g_*`. -/
noncomputable def derivedUpperStarLowerStarAdjunction :
    L((g)^*[A]) ⊣ R((g)_*[A]) :=
  (Etale.upperStarLowerStarAdjunction A g).derivedAdjunction

/-- The bounded below version of `Etale.derivedUpperStarLowerStarAdjunction`: since the
pullback `g^*` on étale sheaves is exact, its derived functor on the bounded below
derived categories is the restriction `D+((g)^*[A])` of the functor induced by `g^*`,
and it is left adjoint to the right derived functor `R+((g)_*[A])` of the pushforward on
the bounded below derived categories. The right adjoint is derived via injective
resolutions, which exist since the étale sheaf category is Grothendieck abelian.
(blueprint: `prose-04-06`) -/
noncomputable def derivedUpperStarLowerStarAdjunctionPlus :
    D+((g)^*[A]) ⊣ R+((g)_*[A]) :=
  (Etale.upperStarLowerStarAdjunction A g).derivedAdjunctionPlus

end Etale

end DerivedUpperLowerStarAdjunction

end AlgebraicGeometry
