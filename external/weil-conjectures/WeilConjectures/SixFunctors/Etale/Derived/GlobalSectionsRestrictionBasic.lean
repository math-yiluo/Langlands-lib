/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedUnitLerayComp
public import WeilConjectures.AlgebraicGeometry.DerivedUnitLerayId

/-!
# The restriction map on derived global sections

For a morphism of schemes `f : Y ⟶ X` and a complex `K` of étale sheaves on `X`, the
*restriction map*
```
RΓ(X, K) ⟶ RΓ(X, Rf_* f^* K) ≅ RΓ(Y, f^* K)
```
is derived global sections of the unit of the derived adjunction `f^* ⊣ Rf_*`
(`AlgebraicGeometry.Etale.mapDerivedUpperStarLowerStarAdjunction`) followed by the Leray
isomorphism (`AlgebraicGeometry.Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso`).
It is the pullback map on cohomology used throughout the blueprint (for instance in
`lemma-restriction-punctured-curve--1`: "pullback maps on cohomology are compatible with
composition").

## Main definitions

- `AlgebraicGeometry.Etale.globalSectionsRestriction f K : RΓ(X, K) ⟶ RΓ(Y, f^* K)`.

## Main results

- `AlgebraicGeometry.Etale.globalSectionsRestriction_naturality`: naturality in `K`.
- `AlgebraicGeometry.Etale.globalSectionsRestriction_comp`: restriction along `g ≫ f` is
  restriction along `f` followed by restriction along `g`.
- `AlgebraicGeometry.Etale.globalSectionsRestriction_id`: restriction along the identity is the
  identity.
- `AlgebraicGeometry.Etale.globalSectionsRestriction_comp_map_counit`: restricting `Rf_* F`
  along `f` and applying the counit `f^* Rf_* F ⟶ F` is the Leray isomorphism
  `RΓ(X, Rf_* F) ≅ RΓ(Y, F)`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The restriction map `RΓ(X, K) ⟶ RΓ(Y, f^* K)` along a morphism `f : Y ⟶ X`: derived global
sections of the unit `K ⟶ Rf_* f^* K` of the derived adjunction `f^* ⊣ Rf_*`, followed by the
Leray isomorphism `RΓ(X, Rf_* f^* K) ≅ RΓ(Y, f^* K)`.

For `A = AddCommGrpCat` this is the component at `K` of
`AlgebraicGeometry.Etale.RawRestrictedComparison.derivedSectionPullback`. -/
noncomputable def globalSectionsRestriction {X Y : Scheme.{u}} (f : Y ⟶ X)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (rightDerivedGlobalSections A X).obj K ⟶
      (rightDerivedGlobalSections A Y).obj (((f)^*[A]).mapDerivedCategory.obj K) :=
  (rightDerivedGlobalSections A X).map ((mapDerivedUpperStarLowerStarAdjunction A f).unit.app K) ≫
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A f).hom.app _

/-- The restriction map is natural in the complex. -/
@[reassoc]
lemma globalSectionsRestriction_naturality {X Y : Scheme.{u}} (f : Y ⟶ X)
    {K L : DerivedCategory (Sheaf X.smallEtaleTopology A)} (φ : K ⟶ L) :
    (rightDerivedGlobalSections A X).map φ ≫ globalSectionsRestriction f L =
      globalSectionsRestriction f K ≫
        (rightDerivedGlobalSections A Y).map ((((f)^*[A]).mapDerivedCategory).map φ) := by
  have h₁ := (mapDerivedUpperStarLowerStarAdjunction A f).unit.naturality φ
  have h₂ := (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A f).hom.naturality
    ((((f)^*[A]).mapDerivedCategory).map φ)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at h₁ h₂
  simp only [globalSectionsRestriction, Category.assoc, ← h₂, ← Functor.map_comp_assoc, h₁]

/-- Restricting `Rf_* F` along `f` and applying the counit `f^* Rf_* F ⟶ F` is the Leray
isomorphism `RΓ(X, Rf_* F) ≅ RΓ(Y, F)`: this is the triangle identity of `f^* ⊣ Rf_*`. -/
@[reassoc]
lemma globalSectionsRestriction_comp_map_counit {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    globalSectionsRestriction f (((f)_*[A]).rightDerivedFunctor.obj F) ≫
        (rightDerivedGlobalSections A Y).map
          ((mapDerivedUpperStarLowerStarAdjunction A f).counit.app F) =
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A f).hom.app F := by
  have h := (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A f).hom.naturality
    ((mapDerivedUpperStarLowerStarAdjunction A f).counit.app F)
  dsimp only [Functor.comp_map, Functor.comp_obj] at h
  rw [globalSectionsRestriction, Category.assoc, ← h, ← Functor.map_comp_assoc,
    Adjunction.right_triangle_components, CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- Restriction along a composite `g ≫ f` is restriction along `f` followed by restriction
along `g`, up to the composition isomorphism `(g ≫ f)^* ≅ g^* f^*`:
```
RΓ(X, K) ──────────────────→ RΓ(Z, (g ≫ f)^* K)
    │                                 │ ≅
    ↓                                 ↓
RΓ(Y, f^* K) ──────────────→ RΓ(Z, g^* f^* K)
```
-/
lemma globalSectionsRestriction_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    globalSectionsRestriction (g ≫ f) K ≫
        (rightDerivedGlobalSections A Z).map
          ((Functor.mapDerivedCategoryNatIso (upperStarComp A g f) ≪≫
            (Functor.mapDerivedCategoryCompIso (upperStar A f) (upperStar A g)).symm).hom.app K) =
      globalSectionsRestriction f K ≫
        globalSectionsRestriction g (((f)^*[A]).mapDerivedCategory.obj K) := by
  simpa only [globalSectionsRestriction, Category.assoc] using derivedUnitLeray_comp f g K

/-- Restriction along the identity is the identity, up to the isomorphism `(𝟙 X)^* ≅ 𝟭`. -/
lemma globalSectionsRestriction_id (X : Scheme.{u})
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    globalSectionsRestriction (𝟙 X) K ≫
        (rightDerivedGlobalSections A X).map
          ((Functor.mapDerivedCategoryNatIso (upperStarId A X) ≪≫
            Functor.mapDerivedCategoryIdIso (Sheaf X.smallEtaleTopology A)).hom.app K) =
      𝟙 _ := by
  rw [globalSectionsRestriction, Category.assoc]
  exact derivedUnitLeray_id X K

end AlgebraicGeometry.Etale
