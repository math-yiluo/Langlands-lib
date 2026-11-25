/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.SectionsRestrictionOpen
public import WeilConjectures.SixFunctors.Etale.SupportCohomologyRestriction
public import WeilConjectures.SixFunctors.Etale.Derived.Localization
public import WeilConjectures.SixFunctors.Etale.Derived.Supports

/-!

# The localization triangle on supported objects and the counit of `Ri_! ⊣ Ri^!`

Let `i : Z ⟶ X` be a closed immersion with open complement `j : U ⟶ X`. This file records three
facts about the localization triangle `RΓ_Z(X, K) ⟶ RΓ(X, K) ⟶ RΓ(U, K) ⟶ RΓ_Z(X, K)[1]`
(`AlgebraicGeometry.Etale.sectionsWithSupportTriangle`) and the counit
`ε : Ri_! Ri^! L ⟶ L` of the exceptional adjunction:

- if `K` is supported on `Z`, i.e. `j^* K = 0`, the inclusion `RΓ_Z(X, K) ⟶ RΓ(X, K)` is an
  isomorphism (`AlgebraicGeometry.Etale.isIso_sectionsWithSupportTriangle_obj_mor₁`), since
  `RΓ(U, K) ≅ RΓ(U, j^* K) = 0`;
- `RΓ_Z(X, ε)` is an isomorphism
  (`AlgebraicGeometry.Etale.isIso_rightDerivedSectionsWithSupport_map_counit`), as
  `RΓ_Z(X, -) ≅ RΓ(X, Ri_! Ri^! -)` and `Ri^! ε` is an isomorphism, `Ri_!` being fully
  faithful;
- `RΓ_Z(X, Ri_! B) ≅ RΓ(Z, B)`, naturally in `B`
  (`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompSectionsWithSupportIso`);
- `Ri_! B` is supported on `Z`, also after pulling back
  (`AlgebraicGeometry.Etale.isZero_mapDerivedCategory_upperStar_rightDerivedLowerShriek`).

-/

@[expose] public section

universe u' u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry.Etale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- For a closed immersion `i : Z ⟶ X` with open complement `j` and a bounded below complex `K`
supported on `Z` (`j^* K = 0`), the inclusion `RΓ_Z(X, K) ⟶ RΓ(X, K)` of the localization
triangle is an isomorphism: its third term `RΓ(X ∖ Z, K) ≅ RΓ(X ∖ Z, j^* K)` vanishes. -/
lemma isIso_sectionsWithSupportTriangle_obj_mor₁ {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A))
    (hK : IsZero (((i.openComplement.ι)^*[A]).mapDerivedCategory.obj K.obj)) :
    IsIso ((sectionsWithSupportTriangle A i).obj K).mor₁ := by
  refine (Triangle.isZero₃_iff_isIso₁ _ (sectionsWithSupportTriangle_obj_distinguished A i K)).1
    ?_
  have := isIso_sectionsRestriction_openComplement A i
    ((Category.id_comp _).trans (Category.id_comp _).symm) K.obj
  exact IsZero.of_iso (Functor.map_isZero _ hK) (asIso ((sectionsRestriction A
    i.openComplement.ι (V := Scheme.Etale.mk i.openComplement.ι)
    (W := Scheme.Etale.mk (𝟙 i.openComplement.toScheme)) (𝟙 _)
    ((Category.id_comp _).trans (Category.id_comp _).symm)).app K.obj))

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- For a closed immersion `i`, the exceptional inverse image `Ri^!` of the counit
`Ri_! Ri^! L ⟶ L` is an isomorphism: by a triangle identity it is the inverse of the unit,
which is an isomorphism as `Ri_!` is fully faithful. -/
lemma isIso_rightDerivedUpperShriek_map_counit {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i]
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((R(i)^![Λ]).map ((rightDerivedUpperShriekAdjunction Λ i).counit.app L)) :=
  have := isIso_rightDerivedUpperShriekAdjunction_unit_app Λ i ((R(i)^![Λ]).obj L)
  isIso_of_hom_comp_eq_id _ ((rightDerivedUpperShriekAdjunction Λ i).right_triangle_components L)

/-- For a closed immersion `i : Z ⟶ X`, the sections with support in `Z` of the counit
`Ri_! Ri^! L ⟶ L` form an isomorphism `RΓ_Z(X, Ri_! Ri^! L) ≅ RΓ_Z(X, L)`. -/
lemma isIso_rightDerivedSectionsWithSupport_map_counit {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i]
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((rightDerivedSectionsWithSupport (ModuleCat.{u + 1} Λ) i).map
      ((rightDerivedUpperShriekAdjunction Λ i).counit.app L)) := by
  rw [NatIso.isIso_map_iff (rightDerivedSectionsWithSupportIso Λ i)]
  have := isIso_rightDerivedUpperShriek_map_counit Λ i L
  dsimp
  infer_instance

/-- `RΓ_Z(X, Ri_! B) ≅ RΓ(Z, B)`, naturally in `B`, for a closed immersion `i : Z ⟶ X`: through
`RΓ_Z(X, -) ≅ RΓ(X, Ri_! Ri^! -)`, the unit `B ≅ Ri^! Ri_! B` and the Leray isomorphism
`RΓ(X, Ri_! B) ≅ RΓ(Z, B)`. -/
noncomputable def rightDerivedLowerShriekCompSectionsWithSupportIso {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    R(i)_![ModuleCat.{u + 1} Λ] ⋙ rightDerivedSectionsWithSupport (ModuleCat.{u + 1} Λ) i ≅
      rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Z :=
  have := isIso_rightDerivedUpperShriekAdjunction_unit_app Λ i
  have : IsIso (rightDerivedUpperShriekAdjunction Λ i).unit := NatIso.isIso_of_isIso_app _
  Functor.isoWhiskerLeft _ (rightDerivedSectionsWithSupportIso Λ i) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (rightDerivedUpperShriekAdjunction Λ i).unit).symm _ ≪≫
    Functor.leftUnitor _ ≪≫
    Functor.isoWhiskerRight
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) i) _ ≪≫
    rightDerivedLowerStarCompRightDerivedGlobalSectionsIso (ModuleCat.{u + 1} Λ) i

/-- For a closed immersion `i : Z ⟶ X` and a morphism `h : W ⟶ X` landing in the open complement
of `Z`, the pullback `h^* Ri_! B` vanishes. -/
lemma isZero_mapDerivedCategory_upperStar_rightDerivedLowerShriek {Z X W : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (h : W ⟶ X)
    (hh : Set.range h ⊆ Set.range i.openComplement.ι)
    (B : DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    IsZero (((h)^*[A]).mapDerivedCategory.obj ((R(i)_![A]).obj B)) :=
  (isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint A i i.openComplement.ι
    (disjoint_range_openComplement_ι_of_subset i i subset_rfl) h hh B).of_iso
    ((leftDerivedUpperStarIsoMapDerivedCategory A h).app _).symm

/-- For a closed immersion `i : Z ⟶ X` and morphisms `h : W ⟶ V`, `g : V ⟶ X` whose composite
lands in the open complement of `Z`, the iterated pullback `h^* g^* Ri_! B` vanishes. -/
lemma isZero_mapDerivedCategory_upperStar_upperStar_rightDerivedLowerShriek
    {Z X V W : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (h : W ⟶ V) (g : V ⟶ X)
    (hh : Set.range (h ≫ g) ⊆ Set.range i.openComplement.ι)
    (B : DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    IsZero (((h)^*[A]).mapDerivedCategory.obj
      (((g)^*[A]).mapDerivedCategory.obj ((R(i)_![A]).obj B))) :=
  (isZero_mapDerivedCategory_upperStar_rightDerivedLowerShriek A i (h ≫ g) hh B).of_iso
    ((Functor.mapDerivedCategoryNatIso (upperStarComp A h g) ≪≫
      (Functor.mapDerivedCategoryCompIso (upperStar A g) (upperStar A h)).symm).app _).symm

end AlgebraicGeometry.Etale
