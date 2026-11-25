/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonSquarePaths
import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonSquareComponent
import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonSquareTransport

/-! # Compatibility of canonical derived site comparisons

These statements use the defining expressions of the comparison isomorphisms of
`SixFunctors/ProEtale/BaseChange/SmoothBaseChange.lean`; they are the inputs of
`AlgebraicGeometry.ProEtale.comparison_derivedBaseChangeMap` there.
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.ComparisonCore
variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The fixed pullback comparisons commute with the fixed square isomorphisms.
Source: Stacks Project, Tag 0B65.

Proof: the underived comparison is the conjugate of the canonical comparison of
restriction functors. Both restriction composites around the square send a test object
to the same iterated fibre product, and the maps are the canonical projection maps.
Their equality follows by the pullback universal property. Conjugation transports
this equality to pullbacks. Apply the exact functors termwise to complexes; the
composition comparisons for mapDerivedCategory and the canonical identifications
with left derived pullbacks preserve this equality. Restrict the input to D+. -/
theorem comparison_square {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (DerivedCategory.Plus.ι ⋙ D(ν^*(X')[ModuleCat.{u + 1} Λ])).map
        ((Etale.pullbackSquareComparison (ModuleCat.{u + 1} Λ) sq.toCommSq).hom.app M) ≫
      (  (fun {U V : Scheme.{u}} (g : U ⟶ V) (Λ : Type (u + 1)) [CommRing Λ] ↦
    Functor.isoWhiskerRight
        (Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlusCompatibility
        D(ν^*(U)[ModuleCat.{u + 1} Λ]) ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Plus.ι
        (Functor.mapDerivedCategoryCompIso _ _ ≪≫
          Functor.mapDerivedCategoryNatIso
            (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g).symm ≪≫
          (Functor.mapDerivedCategoryCompIso _ _).symm) ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.Plus.ι ⋙ D(ν^*(V)[ModuleCat.{u + 1} Λ]))
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g).symm
) g' Λ).hom.app
        (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj M) ≫
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g').map
        ((  (fun {U V : Scheme.{u}} (g : U ⟶ V) (Λ : Type (u + 1)) [CommRing Λ] ↦
    Functor.isoWhiskerRight
        (Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlusCompatibility
        D(ν^*(U)[ModuleCat.{u + 1} Λ]) ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Plus.ι
        (Functor.mapDerivedCategoryCompIso _ _ ≪≫
          Functor.mapDerivedCategoryNatIso
            (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g).symm ≪≫
          (Functor.mapDerivedCategoryCompIso _ _).symm) ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.Plus.ι ⋙ D(ν^*(V)[ModuleCat.{u + 1} Λ]))
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g).symm
) f Λ).hom.app M) =
    (  (fun {U V : Scheme.{u}} (g : U ⟶ V) (Λ : Type (u + 1)) [CommRing Λ] ↦
    Functor.isoWhiskerRight
        (Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlusCompatibility
        D(ν^*(U)[ModuleCat.{u + 1} Λ]) ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Plus.ι
        (Functor.mapDerivedCategoryCompIso _ _ ≪≫
          Functor.mapDerivedCategoryNatIso
            (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g).symm ≪≫
          (Functor.mapDerivedCategoryCompIso _ _).symm) ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.Plus.ι ⋙ D(ν^*(V)[ModuleCat.{u + 1} Λ]))
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g).symm
) f' Λ).hom.app
        (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj M) ≫
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) f').map
        ((  (fun {U V : Scheme.{u}} (g : U ⟶ V) (Λ : Type (u + 1)) [CommRing Λ] ↦
    Functor.isoWhiskerRight
        (Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlusCompatibility
        D(ν^*(U)[ModuleCat.{u + 1} Λ]) ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Plus.ι
        (Functor.mapDerivedCategoryCompIso _ _ ≪≫
          Functor.mapDerivedCategoryNatIso
            (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g).symm ≪≫
          (Functor.mapDerivedCategoryCompIso _ _).symm) ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.Plus.ι ⋙ D(ν^*(V)[ModuleCat.{u + 1} Λ]))
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g).symm
) g Λ).hom.app M) ≫
      (leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} Λ) sq.toCommSq).hom.app
        ((DerivedCategory.Plus.ι ⋙ D(ν^*(Y)[ModuleCat.{u + 1} Λ])).obj M) := by
  let cs : ChosenCartesianSquare g' f' f g :=
    { toCommSq := sq.toCommSq
      isoPullback := sq.isoPullback
      hom_fst := sq.isoPullback_hom_fst
      hom_snd := sq.isoPullback_hom_snd }
  apply comparison_square_of_component Λ sq M
  intro F
  exact comparison_square_component_of_commRing Λ cs F

end AlgebraicGeometry.ProEtale.ComparisonCore
