/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs

/-!
# The degree-`q` base-change map and the recorded base-change property

This file records the base-change map of the smooth base change theorem and the property
of it being an isomorphism.

Fix a morphism `p : X ⟶ S` — the morphism along which one pulls back, smooth in the
theorem — a coefficient ring `Λ` and a degree `q`. For a Cartesian square

```
Y --e--> T
|        |
h        g
v        v
X --p--> S
```

with `g` quasi-compact quasi-separated, and a sheaf `F` of `Λ`-modules on `T_ét`, the
base-change map `p⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is the degree-`q` homology of the derived
base-change morphism `AlgebraicGeometry.Etale.baseChange` of
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs`, evaluated at `F`
placed in degree `0`; it is `AlgebraicGeometry.Etale.baseChangeHomologyMap`, the component
at `F` of the natural transformation
`AlgebraicGeometry.Etale.baseChangeHomologyNatTrans`. The property `BC(p, Λ, q)` of the
blueprint is that this map is an isomorphism for every such square and every `F`.

The base-change square of the blueprint (`definition-derived-base-change-map`) is a Cartesian square
recorded as `CategoryTheory.IsPullback e h g p`; the coefficient conventions
(`sbc-def-coefficient-conventions`) are a commutative ring `Λ` and sheaves of `Λ`-modules on the
small étale site, `Sheaf T.smallEtaleTopology (ModuleCat Λ)`, with the derived categories of
`WeilConjectures.SixFunctors.Etale.Derived`.

The coefficient condition of the theorem is
`AlgebraicGeometry.Scheme.IsTorsionSheafOfInvertibleOrder`, which lives next to the
torsion condition of proper base change in
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf`. A natural number `n`
is *invertible on `S`* when `IsUnit (n : Γ(S, ⊤))`; no definition is introduced for that,
it is written out where it is used.

## Implementation notes

The source and the target of the base-change map are the values of the two functors
`AlgebraicGeometry.Etale.baseChangeSourceFunctor` and
`AlgebraicGeometry.Etale.baseChangeTargetFunctor`, namely `H^q(p^*(R g_* F[0]))` and
`H^q(R h_*(e^*(F[0])))`. Since `p⁻¹` and `e⁻¹` are exact these are the sheaves
`p⁻¹ R^q g_* F` and `R^q h_* e⁻¹ F` of the blueprint, but the two identifications are not
yet available: the isomorphisms `Etale.leftDerivedUpperStarHomologyFunctorIso` and
`Etale.singleFunctorCompLeftDerivedUpperStarIso` of
`WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar` are stated on the unbounded
derived category, and their bounded below counterparts are not in Mathlib. Recording them
is the first thing a file connecting these statements to the classical ones needs.

The compatibilities of the base-change map asserted by the blueprint subsection `prose-08-06`
are proved elsewhere: naturality in `F` is
`AlgebraicGeometry.Etale.baseChangeHomologyMap_naturality` (and
`AlgebraicGeometry.Etale.baseChange_naturality` for the derived map), while compatibility with
the composition of two Cartesian squares and with étale localisation are in
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality`.

## Main definitions

- `AlgebraicGeometry.Etale.constantModSheaf`: the constant sheaf with value `Λ/dΛ`.
- `AlgebraicGeometry.Etale.higherDirectImage`: the higher direct image `R^q h_* F`.
- `AlgebraicGeometry.Etale.baseChangeHomologyNatTrans` and
  `AlgebraicGeometry.Etale.baseChangeHomologyMap`: the degree-`q` base-change map.
- `AlgebraicGeometry.Etale.BaseChangeProperty`: the recorded property `BC(p, Λ, q)`.
- `AlgebraicGeometry.Etale.UniversalBaseChangeProperty`: `BC(p, Λ, q)` for every base change
  of `p`.

## References

- Stacks Project, Section 59.88, <https://stacks.math.columbia.edu/tag/0F02>
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The constant sheaf on the small étale site of `Y` with value the `Λ`-module `Λ/dΛ`,
the coefficients `ℤ/dℤ` of the blueprint read over `Λ`. -/
noncomputable def Etale.constantModSheaf (Y : Scheme.{u}) (d : ℕ) :
    Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
    (ModuleCat.of Λ (Λ ⧸ (Ideal.span {(d : Λ)} : Ideal Λ)))

/-- The degree-`q` higher direct image `R^q h_* F` of a sheaf `F` of `Λ`-modules on the
small étale site of `Y` along `h : Y ⟶ X`: the degree-`q` homology of the derived
pushforward of `F` placed in degree `0`. -/
noncomputable def Etale.higherDirectImage {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (DerivedCategory.Plus.homologyFunctor _ q).obj
    (R+((h)_*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F))

section BaseChangeMap

variable {X S T Y : Scheme.{u}}

/-- The source of the degree-`q` base-change map, as a functor of the coefficient sheaf:
`F ↦ H^q(p^*(R g_* F[0]))`. Since `p⁻¹` is exact this is the sheaf `p⁻¹ R^q g_* F`. -/
noncomputable def Etale.baseChangeSourceFunctor (p : X ⟶ S) (g : T ⟶ S) (q : ℤ) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  DerivedCategory.Plus.singleFunctor _ 0 ⋙
    ((R+((g)_*[ModuleCat.{u + 1} Λ]) ⋙ D+((p)^*[ModuleCat.{u + 1} Λ])) ⋙
      DerivedCategory.Plus.homologyFunctor _ q)

/-- The target of the degree-`q` base-change map, as a functor of the coefficient sheaf:
`F ↦ H^q(R h_*(e^*(F[0])))`. Since `e⁻¹` is exact this is the sheaf `R^q h_* e⁻¹ F`. -/
noncomputable def Etale.baseChangeTargetFunctor (e : Y ⟶ T) (h : Y ⟶ X) (q : ℤ) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  DerivedCategory.Plus.singleFunctor _ 0 ⋙
    ((D+((e)^*[ModuleCat.{u + 1} Λ]) ⋙ R+((h)_*[ModuleCat.{u + 1} Λ])) ⋙
      DerivedCategory.Plus.homologyFunctor _ q)

variable {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

/-- The degree-`q` base-change map `p⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` attached to a Cartesian
square

```
Y --e--> T
|        |
h        g
v        v
X --p--> S
```

as a natural transformation in the coefficient sheaf `F`: the degree-`q` homology of the
derived base-change morphism `AlgebraicGeometry.Etale.baseChange`, whiskered by the
inclusion of sheaves in degree `0`. -/
noncomputable def Etale.baseChangeHomologyNatTrans (sq : IsPullback e h g p) (q : ℤ) :
    Etale.baseChangeSourceFunctor Λ p g q ⟶ Etale.baseChangeTargetFunctor Λ e h q :=
  Functor.whiskerLeft _
    (Functor.whiskerRight (Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq) _)

/-- The degree-`q` base-change transformation is the degree-`q` homology of the derived
base-change morphism, restricted to sheaves placed in degree `0`. -/
lemma Etale.baseChangeHomologyNatTrans_eq (sq : IsPullback e h g p) (q : ℤ) :
    Etale.baseChangeHomologyNatTrans Λ sq q =
      Functor.whiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
        (Functor.whiskerRight (Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq)
          (DerivedCategory.Plus.homologyFunctor _ q)) := rfl

/-- The degree-`q` base-change map `p⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` at a sheaf `F` of
`Λ`-modules on `T_ét`: the component at `F` of
`AlgebraicGeometry.Etale.baseChangeHomologyNatTrans`. -/
noncomputable def Etale.baseChangeHomologyMap (sq : IsPullback e h g p) (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Etale.baseChangeSourceFunctor Λ p g q).obj F ⟶
      (Etale.baseChangeTargetFunctor Λ e h q).obj F :=
  (Etale.baseChangeHomologyNatTrans Λ sq q).app F

/-- The base-change map is natural in the coefficient sheaf. This is the naturality
asserted by the blueprint subsection `prose-08-06`, and the input to the comparison of the
two long exact sequences in `AlgebraicGeometry.Etale.mono_baseChangeHomologyMap`. -/
lemma Etale.baseChangeHomologyMap_naturality (sq : IsPullback e h g p) (q : ℤ)
    {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (α : F ⟶ G) :
    Etale.baseChangeHomologyMap Λ sq q F ≫ (Etale.baseChangeTargetFunctor Λ e h q).map α =
      (Etale.baseChangeSourceFunctor Λ p g q).map α ≫
        Etale.baseChangeHomologyMap Λ sq q G :=
  ((Etale.baseChangeHomologyNatTrans Λ sq q).naturality α).symm

end BaseChangeMap

variable {X S : Scheme.{u}}

/-- Blueprint `prose-08-06`: The recorded base-change property.

`BC(p, Λ, q)` holds when, for every quasi-compact quasi-separated `g : T ⟶ S`, every sheaf
`F` of `Λ`-modules on `T_ét` and every Cartesian square

```
Y --e--> T
|        |
h        g
v        v
X --p--> S
```

the base-change map `p⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` of
`AlgebraicGeometry.Etale.baseChangeHomologyMap` is an isomorphism. The coefficient ring `Λ`
plays the role of `ℤ/nℤ` in the blueprint; the hypothesis that `n` be invertible on `S` is
not part of the property and is carried separately by the statements that need it.

The Cartesian squares are the base-change squares of blueprint `definition-derived-base-change-map`,
recorded as `IsPullback e h g p`; following blueprint `sbc-def-coefficient-conventions`, the
coefficients are sheaves of modules over a commutative ring `Λ` on the small étale sites. -/
def Etale.BaseChangeProperty (p : X ⟶ S) (q : ℤ) : Prop :=
  ∀ {T Y : Scheme.{u}} (g : T ⟶ S) (e : Y ⟶ T) (h : Y ⟶ X)
    [QuasiCompact g] [QuasiSeparated g] (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
    IsIso (Etale.baseChangeHomologyMap Λ sq q F)

/-- The base-change property `BC(p, Λ, q)` holds *universally* when it holds for every base
change `p' : X' ⟶ S'` of `p` along a morphism `a : S' ⟶ S`. This is the form of the property
in which the blueprint subsection `prose-08-06` states it. -/
def Etale.UniversalBaseChangeProperty (p : X ⟶ S) (q : ℤ) : Prop :=
  ∀ ⦃S' X' : Scheme.{u}⦄ (a : S' ⟶ S) (b : X' ⟶ X) (p' : X' ⟶ S'),
    IsPullback b p' p a → Etale.BaseChangeProperty Λ p' q

variable {Λ} {p : X ⟶ S} {q : ℤ}

lemma Etale.UniversalBaseChangeProperty.baseChangeProperty
    (h : Etale.UniversalBaseChangeProperty Λ p q) : Etale.BaseChangeProperty Λ p q :=
  h (𝟙 S) (𝟙 X) p (IsPullback.id_horiz p)

/-- A base change of a morphism satisfying the base-change property universally satisfies it
universally. -/
lemma Etale.UniversalBaseChangeProperty.of_isPullback
    (h : Etale.UniversalBaseChangeProperty Λ p q) {S' X' : Scheme.{u}} {a : S' ⟶ S}
    {b : X' ⟶ X} {p' : X' ⟶ S'} (hp : IsPullback b p' p a) :
    Etale.UniversalBaseChangeProperty Λ p' q :=
  fun _ _ a' b' p'' hp' ↦ h (a' ≫ a) (b' ≫ b) p'' (hp'.paste_horiz hp)

end AlgebraicGeometry
