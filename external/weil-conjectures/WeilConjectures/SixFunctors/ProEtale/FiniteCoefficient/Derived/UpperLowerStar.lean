/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs

/-!

# Derived Upper Star and Lower Star

This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`.

As there, the derived pullback and pushforward of pro-étale sheaves are *not* given
definitions of their own: they are the generic derived-functor constructions of the folder
`WeilConjectures.CategoryTheory.DerivedCategory` applied to the underived pullback
`(g)^*[A]` and pushforward `(g)_*[A]`, and they are written by nesting the generic
notations inside the underived ones:

| derived functor | notation | meaning |
| --- | --- | --- |
| `Rg_* : D(Z_proét) ⥤ D(Y_proét)` | `R((g)_*[A])` | `(g)_*[A].rightDerivedFunctor` |
| `Rg_* : D⁺(Z_proét) ⥤ D⁺(Y_proét)` | `R+((g)_*[A])` | `(g)_*[A].rightDerivedFunctorPlus` |
| `Lg^* : D(Y_proét) ⥤ D(Z_proét)` | `L((g)^*[A])` | `(g)^*[A].leftDerivedFunctor` |
| `g^* : D(Y_proét) ⥤ D(Z_proét)` | `D((g)^*[A])` | `(g)^*[A].mapDerivedCategory` |
| `g^* : D⁺(Y_proét) ⥤ D⁺(Z_proét)` | `D+((g)^*[A])` | `(g)^*[A].mapDerivedCategoryPlus` |

The generic notations `R(-)`, `R+(-)`, `L(-)`, `D(-)` and `D+(-)` are scoped in the
`CategoryTheory.Functor` namespace, so a file using them needs
`open scoped CategoryTheory.Functor`. Each row above is recorded below as an `example`,
at the place where a definition of the corresponding functor would have stood, so that
the type of the functor is spelled out.

## Main results

- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarIsoMapDerivedCategory` : the derived
  pullback `L((g)^*[A])` is the functor `D((g)^*[A])` induced levelwise by the exact
  functor `g^*`.

- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarComp` : the composition isomorphism
  `L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*`.

- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarId` : the identity isomorphism
  `L(𝟙 X)^* ≅ 𝟭` of the derived pullback.

- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarCongr` : the transport `Lf^* ≅ Lg^*`
  along an equality `f = g`.

- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarHomologyFunctorIso` : the derived
  pullback commutes with the homology functors, `H^n ⋙ g^* ≅ Lg^* ⋙ H^n`.

- `AlgebraicGeometry.ProEtale.singleFunctorCompLeftDerivedUpperStarIso` : the derived
  pullback of a sheaf placed in degree `0` is the pullback of the sheaf placed in degree
  `0`.

- `AlgebraicGeometry.ProEtale.derivedUpperStarLowerStarAdjunction` and
  `AlgebraicGeometry.ProEtale.derivedUpperStarLowerStarAdjunctionPlus` : the derived
  adjunctions `L((g)^*[A]) ⊣ R((g)_*[A])` and `D+((g)^*[A]) ⊣ R+((g)_*[A])`.

- `AlgebraicGeometry.ProEtale.derivedBaseChangeMap` : the derived base change map
  `Lg^* Rf_* ⟶ Rf'_* Lg'^*` of a commutative square, the mate of the isomorphism
  `AlgebraicGeometry.ProEtale.leftDerivedUpperStarSquareIso : Lf'^* Lg^* ≅ Lg'^* Lf^*`.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section DerivedLowerStar

namespace ProEtale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The total right derived functor `Rg_* : D(Z_proét) ⥤ D(Y_proét)` of the pushforward
`g_*` along an arbitrary morphism `g : Z ⟶ Y` on the unbounded derived categories of
pro-étale sheaves.

It is not a definition of its own: it is the generic `Functor.rightDerivedFunctor`,
written `R(-)`, applied to the underived pushforward `(g)_*[A]`. -/
noncomputable example :
    DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) :=
  R((g)_*[A])

/-- The right derived functor `Rg_* : D⁺(Z_proét) ⥤ D⁺(Y_proét)` of the pushforward `g_*`
on the *bounded below* derived categories of pro-étale sheaves: the generic
`Functor.rightDerivedFunctorPlus`, written `R+(-)`, applied to `(g)_*[A]`. -/
noncomputable example :
    DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Z) A) ⥤
      DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y) A) :=
  R+((g)_*[A])

end ProEtale

end DerivedLowerStar

section DerivedUpperStar

/-!
## The derived pullback `Lg^*`

The pullback `g^* = ProEtale.upperStar` is left derived using the K-flat left
derivability structure of `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs`.
This requires the source sheaf category `Sheaf (Scheme.ProEt.topology Y) A` to carry a
preadditive monoidal structure whose tensor product preserves colimits, to have countable
coproducts and exact `ℤ`-indexed colimits, and to admit functorial flat resolutions.
These inputs are stated as hypotheses on the coefficient category `A` only; they are
supplied for the sheaf categories by the instances of the folder
`WeilConjectures.CategoryTheory.GrothendieckAbelian`, with the monoidal structure and its
compatibility with colimits provided by its `Monoidal` subfolder, and its preadditivity
by `CategoryTheory.Sheaf.monoidalPreadditive`, which holds for any sheaf category.

As in the étale case, the functorial flat resolutions of pro-étale sheaves are
`AlgebraicGeometry.ProEtale.hasFunctorialFlatResolution_sheaf`
(`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution`), and the
tensor-colimit input is `AlgebraicGeometry.ProEtale.preservesColimitsOfSize_tensorLeft_sheaf`
(Day's reflection theorem).

The additivity and exactness of `g^*` are `ProEtale.additive_upperStar`,
`ProEtale.preservesFiniteLimits_upperStar` and `ProEtale.preservesHomology_upperStar` of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`; the left exactness
there rests on the `HasSheafify` instance for the small pro-étale site of `Z` and on left
exactness of the left Kan extension along the opposite of base change, both global
instances of the folder `WeilConjectures.CategoryTheory.GrothendieckAbelian` (for a weakly
étale `g` the latter is proved directly). Since `g^*` is exact, it preserves in
particular all K-flat quasi-isomorphisms, which is the input needed by the
derivability-structure machinery.
-/

open MonoidalCategory ProEtale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/- The preadditive monoidal structure on the coefficient category. It is assumed closed
and *symmetric* (as is the intended application `A = ModuleCat.{u + 1} Λ` for a
commutative ring `Λ`): that is what makes the class of sheafification-inverting
morphisms of presheaves monoidal, hence what lets the monoidal structure descend to the
pro-étale sheaf categories, see
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs`. Closedness and the
symmetry moreover make the pro-étale sheaf categories monoidal closed by Day's reflection
theorem, hence make tensoring by a fixed sheaf preserve colimits, which is what the
tensor product of complexes needs, see
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits`; no further
tensor-colimit hypothesis on `A` is required. -/
variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]

/- Functorial flat resolutions on the coefficient category; they induce functorial flat
resolutions of pro-étale sheaves via `ProEtale.hasFunctorialFlatResolution_sheaf`. -/
variable [Abelian.HasFunctorialFlatResolution A]

namespace ProEtale

/-- The total left derived functor `Lg^* : D(Y_proét) ⥤ D(Z_proét)` of the pullback `g^*`
along an arbitrary morphism `g : Z ⟶ Y` on the unbounded derived categories of pro-étale
sheaves, defined via the K-flat left derivability structure: `Lg^*` is computed by
applying `g^*` to a K-flat resolution.

It is not a definition of its own: it is the generic `Functor.leftDerivedFunctor`,
written `L(-)`, applied to the underived pullback `(g)^*[A]`.

Since `g^*` is exact, the counit `Lg^* ∘ Q ⟶ Q ∘ g^*` is in fact an isomorphism
everywhere; the construction via the derivability structure is uniform in the functor
and applies verbatim once `g^*` is replaced by a non-exact functor (e.g. the pullback
of sheaves of modules over a varying sheaf of rings). -/
noncomputable example :
    DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A) :=
  L((g)^*[A])

/-- The compatibility of the derived pullback with the levelwise functor: the total left
derived functor `Lg^*`, computed via K-flat resolutions, is canonically isomorphic to
the functor induced by the exact functor `g^*` on the derived categories.

```
                          Lg^*
                   -------------------->
        D(Y_proét)           ≅            D(Z_proét)
                   -------------------->
                       D((g)^*[A])
```

This is `Functor.leftDerivedFunctorIsoMapDerivedCategory` at `g^*`. -/
noncomputable def leftDerivedUpperStarIsoMapDerivedCategory :
    L((g)^*[A]) ≅ D((g)^*[A]) :=
  (g)^*[A].leftDerivedFunctorIsoMapDerivedCategory

/-- The composition isomorphism `L(g₁ ≫ g₂)^* ≅ Lg₂^* ∘ Lg₁^*` of derived pullbacks,
obtained from the underived composition isomorphism `ProEtale.upperStarComp` and the
compatibility of left derivation with `mapDerivedCategory` for exact functors.

```
                    L(g₁ ≫ g₂)^*
D(R_proét) -----------------------------> D(T_proét)
      |                                       ^
      |                                       |
      +---------> D(S_proét) -----------------+
          Lg₂^*                  Lg₁^*
```
-/
noncomputable def leftDerivedUpperStarComp {T S R : Scheme.{u}}
    (g₁ : T ⟶ S) (g₂ : S ⟶ R) :
    L((g₁ ≫ g₂)^*[A]) ≅ L((g₂)^*[A]) ⋙ L((g₁)^*[A]) :=
  Functor.leftDerivedFunctorNatIso _ (ProEtale.upperStarComp A g₁ g₂) ≪≫
    Functor.leftDerivedFunctorCompIso (g₂)^*[A] (g₁)^*[A]

/-- The identity isomorphism `L(𝟙 X)^* ≅ 𝟭` of the derived pullback on pro-étale sheaves. -/
noncomputable def leftDerivedUpperStarId (X : Scheme.{u}) : L((𝟙 X)^*[A]) ≅ 𝟭 _ :=
  -- the derived functor of `ProEtale.upperStarId`, followed by `L(𝟭) ≅ D(𝟭) ≅ 𝟭`
  Functor.leftDerivedFunctorNatIso _ (ProEtale.upperStarId A X) ≪≫
    (𝟭 _).leftDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso _

/-- Transport of the derived pullback along an equality of morphisms: `Lf^* ≅ Lg^*` for
`f = g`. -/
noncomputable def leftDerivedUpperStarCongr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    L((f)^*[A]) ≅ L((g)^*[A]) :=
  -- not `eqToIso`: the kernel would compare `Lf^*` and `Lg^*` when reducing the transport
  h ▸ Iso.refl _

@[simp]
lemma leftDerivedUpperStarCongr_rfl {X Y : Scheme.{u}} {f : X ⟶ Y} :
    leftDerivedUpperStarCongr A (rfl : f = f) = Iso.refl _ :=
  rfl

/-- The exactness comparison `H^n ∘ g^* ≅ g^* ∘ H^n`: since the underived pullback `g^*`
on pro-étale sheaves is exact, applying it to the `n`-th homology sheaf of an object of
the derived category computes the `n`-th homology sheaf of the derived pullback.

```
                    H^n
D(Y_proét) -----------------> Sh(Y_proét)
    |                              |
  Lg^*                            g^*
    |                              |
    v                              v
D(Z_proét) -----------------> Sh(Z_proét)
                    H^n
```

This is `Functor.leftDerivedFunctorHomologyFunctorIso` at `g^*`. -/
noncomputable def leftDerivedUpperStarHomologyFunctorIso (n : ℤ) :
    DerivedCategory.homologyFunctor (Sheaf (Scheme.ProEt.topology Y) A) n ⋙ (g)^*[A] ≅
      L((g)^*[A]) ⋙
        DerivedCategory.homologyFunctor (Sheaf (Scheme.ProEt.topology Z) A) n :=
  (g)^*[A].leftDerivedFunctorHomologyFunctorIso n

/-- The single-degree comparison for the derived pullback: since the underived pullback
`g^*` on pro-étale sheaves is exact, the derived pullback of a sheaf placed in degree `0`
is the pullback of the sheaf placed in degree `0`, `Lg^*(F[0]) ≅ (g^* F)[0]`.

```
                     (-)[0]
Sh(Y_proét) -----------------> D(Y_proét)
     |                              |
     g^*                          Lg^*
     |                              |
     v                              v
Sh(Z_proét) -----------------> D(Z_proét)
                     (-)[0]
```

This is `Functor.singleFunctorCompLeftDerivedFunctorIso` at `g^*`. -/
noncomputable def singleFunctorCompLeftDerivedUpperStarIso :
    DerivedCategory.singleFunctor (Sheaf (Scheme.ProEt.topology Y) A) 0 ⋙ L((g)^*[A]) ≅
      (g)^*[A] ⋙ DerivedCategory.singleFunctor (Sheaf (Scheme.ProEt.topology Z) A) 0 :=
  (g)^*[A].singleFunctorCompLeftDerivedFunctorIso

end ProEtale

end DerivedUpperStar

section DerivedUpperLowerStarAdjunction

/-!
## The derived adjunction `Lg^* ⊣ Rg_*`

The adjunction `g^* ⊣ g_*` between the pullback and the pushforward of pro-étale sheaves
induces an adjunction `Lg^* ⊣ Rg_*` between their total derived functors on the
unbounded derived categories, by
`CategoryTheory.Adjunction.derivedAdjunction`
(`WeilConjectures.CategoryTheory.DerivedCategory.Adjunction`): the left adjoint is
derived via the K-flat left derivability structure on `D(Y_proét)` and the right adjoint
via the K-injective right derivability structure on `D(Z_proét)`, and the two
"absoluteness" hypotheses of mathlib's abstract theorem `Adjunction.derived` hold
because the derived-functor comparison maps are isomorphisms on K-flat, respectively
K-injective, complexes.

The hypotheses of this section are those of the section `DerivedUpperStar`: the
K-injective resolutions on the pushforward side are supplied by the sheaf category
being Grothendieck abelian.
-/

open MonoidalCategory ProEtale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/- The closed symmetric preadditive monoidal structure on the coefficient category, as in
the section `DerivedUpperStar`; it is what the monoidal transport instances of
`WeilConjectures.CategoryTheory.GrothendieckAbelian` are stated under. -/
variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]

/- Functorial flat resolutions on the coefficient category, as in the section
`DerivedUpperStar`. -/
variable [Abelian.HasFunctorialFlatResolution A]

namespace ProEtale

/-- Blueprint `prose-03-02`: Derived direct image; and blueprint
`prose-03-02`, the derived pullback. The derived direct image
`Rg_* = R((g)_*[A])` (the generic total right derived functor, computed by K-injective
resolutions) and the derived pullback `Lg^* = L((g)^*[A])` (computed by K-flat resolutions,
isomorphic to `D((g)^*[A])` by `leftDerivedUpperStarIsoMapDerivedCategory`) have no
definitions of their own; this is their adjunction.

The derived adjunction `Lg^* ⊣ Rg_*` between the total derived functors of the
pullback and the pushforward along an arbitrary morphism `g : Z ⟶ Y` on the unbounded
derived categories of pro-étale sheaves, induced by the adjunction `g^* ⊣ g_*`. -/
noncomputable def derivedUpperStarLowerStarAdjunction :
    L((g)^*[A]) ⊣ R((g)_*[A]) :=
  (ProEtale.upperStarLowerStarAdjunction A g).derivedAdjunction

/-- The bounded below version of `ProEtale.derivedUpperStarLowerStarAdjunction`: since the
pullback `g^*` on pro-étale sheaves is exact, its derived functor on the bounded below
derived categories is the restriction `D+((g)^*[A])` of the functor induced by `g^*`,
and it is left adjoint to the right derived functor `R+((g)_*[A])` of the pushforward on
the bounded below derived categories. The right adjoint is derived via injective
resolutions, which exist since the pro-étale sheaf category is Grothendieck abelian. -/
noncomputable def derivedUpperStarLowerStarAdjunctionPlus :
    D+((g)^*[A]) ⊣ R+((g)_*[A]) :=
  (ProEtale.upperStarLowerStarAdjunction A g).derivedAdjunctionPlus

section Square

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The isomorphism `Lf'^* Lg^* ≃ L(f' ≫ g)^* = L(g' ≫ f)^* ≃ Lg'^* Lf^*` of derived pullbacks
attached to a commutative square `g' ≫ f = f' ≫ g` of schemes. -/
noncomputable def leftDerivedUpperStarSquareIso (sq : CommSq g' f' f g) :
    L((g)^*[A]) ⋙ L((f')^*[A]) ≅ L((f)^*[A]) ⋙ L((g')^*[A]) :=
  (leftDerivedUpperStarComp A f' g).symm ≪≫ leftDerivedUpperStarCongr A sq.w.symm ≪≫
    leftDerivedUpperStarComp A g' f

/-- Blueprint `definition-pro-etale-base-change-map--1`: Exchange and projection transformations,
the direct-image exchange `Ex_*`.

The derived base change map `Lg^* Rf_* ⟶ Rf'_* Lg'^*` of a commutative square
`g' ≫ f = f' ≫ g` of schemes,

```
  X' ──g'──▶ X
  │          │
  f'         f
  ▼          ▼
  Y' ──g───▶ Y
```

the mate (`CategoryTheory.mateEquiv`), along `Lf^* ⊣ Rf_*` and `Lf'^* ⊣ Rf'_*`, of the
isomorphism `leftDerivedUpperStarSquareIso : Lf'^* Lg^* ≃ Lg'^* Lf^*`. The square is not
required to be Cartesian, and the map is not an isomorphism in general. -/
noncomputable def derivedBaseChangeMap (sq : CommSq g' f' f g) :
    R((f)_*[A]) ⋙ L((g)^*[A]) ⟶ L((g')^*[A]) ⋙ R((f')_*[A]) :=
  mateEquiv (derivedUpperStarLowerStarAdjunction A f) (derivedUpperStarLowerStarAdjunction A f')
    (leftDerivedUpperStarSquareIso A sq).hom

end Square

end ProEtale

end DerivedUpperLowerStarAdjunction

end AlgebraicGeometry
