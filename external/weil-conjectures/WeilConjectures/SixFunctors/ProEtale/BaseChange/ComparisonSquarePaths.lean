/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence

/-! # The two ordinary comparison paths and their common derived endpoints
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

section Paths

variable {A B B' C P Q Q' R : Type*}
  [Category A] [Category B] [Category B'] [Category C]
  [Category P] [Category Q] [Category Q'] [Category R]

/-- The comparison path passing through the first square. -/
noncomputable def comparisonSquareEtalePathOfData
    (s : ComparisonSquareData A B B' C P Q Q' R) :
    (s.L₁ ⋙ s.L₂) ⋙ s.K₂ ≅ s.K₀ ⋙ (s.R₁' ⋙ s.R₂') :=
  Functor.isoWhiskerRight s.se s.K₂ ≪≫
    Functor.isoWhiskerLeft s.L₁' s.c₂' ≪≫ Functor.isoWhiskerRight s.c₁' s.R₂'

/-- The comparison path passing through the second square. -/
noncomputable def comparisonSquareProEtalePathOfData
    (s : ComparisonSquareData A B B' C P Q Q' R) :
    (s.L₁ ⋙ s.L₂) ⋙ s.K₂ ≅ s.K₀ ⋙ (s.R₁' ⋙ s.R₂') :=
  Functor.isoWhiskerLeft s.L₁ s.c₂ ≪≫ Functor.isoWhiskerRight s.c₁ s.R₂ ≪≫
    Functor.isoWhiskerLeft s.K₀ s.sp

/-- Component coherence identifies the two specified ordinary paths.
The data `s` is a cube: the top face `se : L₁ ⋙ L₂ ≅ L₁' ⋙ L₂'`, the bottom face
`sp : R₁ ⋙ R₂ ≅ R₁' ⋙ R₂'`, and four vertical squares `c₁, c₂, c₁', c₂'`:
```
        L₁       L₂                 L₁'      L₂'
   A ────▶ B ────▶ C           A ────▶ B' ────▶ C
   │       │       │           │       │        │
 K₀│  c₁   │K₁ c₂  │K₂       K₀│  c₁'  │K₁' c₂' │K₂
   ▼       ▼       ▼           ▼       ▼        ▼
   P ────▶ Q ────▶ R           P ────▶ Q' ────▶ R
        R₁       R₂                 R₁'      R₂'
```
The two isomorphisms `(L₁ ⋙ L₂) ⋙ K₂ ≅ K₀ ⋙ (R₁' ⋙ R₂')` are `se`, then the right-hand
row of squares (`comparisonSquareEtalePathOfData`), and the left-hand row of squares, then
`sp` (`comparisonSquareProEtalePathOfData`). They agree when every component of the cube
commutes (`ComparisonSquareComponent`).
Source: extensionality of natural transformations. -/
theorem comparisonSquarePaths_eq (s : ComparisonSquareData A B B' C P Q Q' R)
    (h : ∀ F, ComparisonSquareComponent s F) :
    comparisonSquareEtalePathOfData s = comparisonSquareProEtalePathOfData s := by
  apply Iso.ext
  apply NatTrans.ext
  funext F
  simpa only [comparisonSquareEtalePathOfData, comparisonSquareProEtalePathOfData,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc] using (h F).symm

end Paths

variable (Λ : Type (u + 1)) [CommRing Λ]
  {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The ordinary path through the etale square, followed by its two comparison maps. -/
noncomputable def comparisonSquareEtalePath (cs : ChosenCartesianSquare g' f' f g) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) g ⋙
        Etale.upperStar (ModuleCat.{u + 1} Λ) f') ⋙ ν^*(X')[ModuleCat.{u + 1} Λ] ≅
      ν^*(Y)[ModuleCat.{u + 1} Λ] ⋙
        (upperStar (ModuleCat.{u + 1} Λ) f ⋙ upperStar (ModuleCat.{u + 1} Λ) g') :=
  comparisonSquareEtalePathOfData (comparisonSquareData (ModuleCat.{u + 1} Λ) g' f' f g cs)

/-- The ordinary path through the two comparison maps, followed by the pro-etale square. -/
noncomputable def comparisonSquareProEtalePath (cs : ChosenCartesianSquare g' f' f g) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) g ⋙
        Etale.upperStar (ModuleCat.{u + 1} Λ) f') ⋙ ν^*(X')[ModuleCat.{u + 1} Λ] ≅
      ν^*(Y)[ModuleCat.{u + 1} Λ] ⋙
        (upperStar (ModuleCat.{u + 1} Λ) f ⋙ upperStar (ModuleCat.{u + 1} Λ) g') :=
  comparisonSquareProEtalePathOfData (comparisonSquareData (ModuleCat.{u + 1} Λ) g' f' f g cs)

/-- The common source comparison from derivation of the ordinary triple composite.
Source: exact-functor composition comparisons. -/
noncomputable def comparisonSquareSourceIso (g : Y' ⟶ Y) (f' : X' ⟶ Y') :
    D((Etale.upperStar (ModuleCat.{u + 1} Λ) g ⋙
        Etale.upperStar (ModuleCat.{u + 1} Λ) f') ⋙ ν^*(X')[ModuleCat.{u + 1} Λ]) ≅
      D(Etale.upperStar (ModuleCat.{u + 1} Λ) g) ⋙
        D(Etale.upperStar (ModuleCat.{u + 1} Λ) f') ⋙ D(ν^*(X')[ModuleCat.{u + 1} Λ]) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso _ _).symm _

/-- The common target comparison to the two total left derived pullbacks.
Source: exact-functor composition comparisons. -/
noncomputable def comparisonSquareTargetIso (g' : X' ⟶ X) (f : X ⟶ Y) :
    D(ν^*(Y)[ModuleCat.{u + 1} Λ] ⋙
        (upperStar (ModuleCat.{u + 1} Λ) f ⋙ upperStar (ModuleCat.{u + 1} Λ) g')) ≅
      D(ν^*(Y)[ModuleCat.{u + 1} Λ]) ⋙
        L(upperStar (ModuleCat.{u + 1} Λ) f) ⋙ L(upperStar (ModuleCat.{u + 1} Λ) g') :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) f).symm _ ≪≫
        Functor.isoWhiskerLeft _
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g').symm)

/-- The exact derived image of one ordinary path with the common endpoint factors.
This is a concrete composite; its arguments retain the entire ordinary isomorphism.
Source: exact derivation. -/
noncomputable def comparisonSquareDerivedPath
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (e : (Etale.upperStar (ModuleCat.{u + 1} Λ) g ⋙
        Etale.upperStar (ModuleCat.{u + 1} Λ) f') ⋙ ν^*(X')[ModuleCat.{u + 1} Λ] ≅
      ν^*(Y)[ModuleCat.{u + 1} Λ] ⋙
        (upperStar (ModuleCat.{u + 1} Λ) f ⋙ upperStar (ModuleCat.{u + 1} Λ) g'))
    (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (DerivedCategory.Plus.ι ⋙ D(ν^*(X')[ModuleCat.{u + 1} Λ])).obj
        (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) f').obj
          (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj M)) ⟶
      L(upperStar (ModuleCat.{u + 1} Λ) g').obj
        (L(upperStar (ModuleCat.{u + 1} Λ) f).obj
          ((DerivedCategory.Plus.ι ⋙ D(ν^*(Y)[ModuleCat.{u + 1} Λ])).obj M)) :=
  (comparisonSquareSourceIso Λ g f').inv.app M.obj ≫
    (Functor.mapDerivedCategoryNatIso e).hom.app M.obj ≫
    (comparisonSquareTargetIso Λ g' f).hom.app M.obj

end AlgebraicGeometry.ProEtale
