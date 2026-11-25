/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.RestrictScalars
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-!
# Pullback of étale sheaves commutes with restriction of scalars

Let `ρ : Λ →+* Λ'` be a morphism of commutative rings and `g : Y ⟶ Z` a morphism of schemes.
Restriction of scalars along `ρ` commutes with the pullback `g^*` of étale sheaves of modules:
the canonical isomorphism `g^* (Res F) ≅ Res (g^* F)` for sheaves `F` of `Λ'`-modules on `Z` is
`AlgebraicGeometry.Etale.upperStarRestrictScalarsIso ρ g`, conjugate, for the adjunctions
`Res ⊣ Coext` and `g^* ⊣ g_*`, to the identity `g_* ∘ Coext = Coext ∘ g_*`. This isomorphism is
compatible with the composition,
identity and congruence isomorphisms of the pullbacks, and passes to the derived categories,
where it is compatible with the corresponding isomorphisms of derived pullbacks.

This is the compatibility of pullback with the change of the finite coefficients, used to make
the systems of derived pullbacks of the `ℓ`-adic coefficient stages into morphisms of adic
systems, for the compatible systems of Frobenius coefficient morphisms. It is the étale
counterpart of `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars`,
whose general pasting lemmas on derived categories it reuses.

## Main definitions

- `AlgebraicGeometry.Etale.leftDerivedUpperStarRestrictScalarsIso ρ g` :
  `Res ⋙ Lg^* ≅ Lg^* ⋙ Res` on the derived categories.

## Main results

- `AlgebraicGeometry.Etale.upperStarRestrictScalarsIso_comp_hom`,
  `AlgebraicGeometry.Etale.upperStarRestrictScalarsIso_id_hom`,
  `AlgebraicGeometry.Etale.upperStarRestrictScalarsIso_congr_hom` : the compatibilities of
  `upperStarRestrictScalarsIso` with `Etale.upperStarComp`, `Etale.upperStarId` and the
  transport along an equality of morphisms.
- `AlgebraicGeometry.Etale.leftDerivedUpperStarRestrictScalarsIso_comp_hom_app`,
  `AlgebraicGeometry.Etale.leftDerivedUpperStarRestrictScalarsIso_id_hom_app`,
  `AlgebraicGeometry.Etale.leftDerivedUpperStarRestrictScalarsIso_congr_hom_app` : the
  derived versions, with `Etale.leftDerivedUpperStarComp`, `Etale.leftDerivedUpperStarId` and
  the transport along an equality of morphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

section Coherence

/-- Compatibility of `AlgebraicGeometry.Etale.upperStarRestrictScalarsIso` with the
composition isomorphisms `(g₁ ≫ g₂)^* ≅ g₂^* ⋙ g₁^*`: the isomorphism for `g₁ ≫ g₂` is the
pasting of those for `g₂` and `g₁`. -/
lemma upperStarRestrictScalarsIso_comp_hom {T S R : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ R) :
    (upperStarRestrictScalarsIso ρ (g₁ ≫ g₂)).hom ≫
        Functor.whiskerRight (upperStarComp _ g₁ g₂).hom (Sheaf.restrictScalars _ ρ) =
      Functor.whiskerLeft (Sheaf.restrictScalars _ ρ) (upperStarComp _ g₁ g₂).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (upperStarRestrictScalarsIso ρ g₂).hom _ ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ (upperStarRestrictScalarsIso ρ g₁).hom ≫
        (Functor.associator _ _ _).inv := by
  have hc (Γ : Type (u + 1)) [CommRing Γ] :
      conjugateEquiv ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Γ) g₂).comp
          (upperStarLowerStarAdjunction _ g₁)) (upperStarLowerStarAdjunction _ (g₁ ≫ g₂))
        (upperStarComp _ g₁ g₂).hom = (lowerStarComp (ModuleCat.{u + 1} Γ) g₁ g₂).hom :=
    congrArg Iso.hom (conjugateIsoEquiv_upperStarComp _ g₁ g₂)
  apply (conjugateEquiv
    (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') g₂).comp
      (upperStarLowerStarAdjunction _ g₁)).comp (Sheaf.restrictCoextendScalarsAdj _ ρ))
    ((Sheaf.restrictCoextendScalarsAdj _ ρ).comp
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (g₁ ≫ g₂)))).injective
  rw [← conjugateEquiv_comp _
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') (g₁ ≫ g₂)).comp
      (Sheaf.restrictCoextendScalarsAdj _ ρ)) _,
    conjugateEquiv_whiskerRight, hc Λ',
    ← conjugateEquiv_comp _
      ((Sheaf.restrictCoextendScalarsAdj _ ρ).comp
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g₂).comp
          (upperStarLowerStarAdjunction _ g₁))) _,
    ← conjugateEquiv_comp _
      (((Sheaf.restrictCoextendScalarsAdj _ ρ).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g₂)).comp
          (upperStarLowerStarAdjunction _ g₁)) _,
    ← conjugateEquiv_comp _
      (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') g₂).comp
        (Sheaf.restrictCoextendScalarsAdj _ ρ)).comp
          (upperStarLowerStarAdjunction _ g₁)) _,
    ← conjugateEquiv_comp _
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') g₂).comp
        ((Sheaf.restrictCoextendScalarsAdj _ ρ).comp
          (upperStarLowerStarAdjunction _ g₁))) _,
    ← conjugateEquiv_comp _
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') g₂).comp
        ((upperStarLowerStarAdjunction _ g₁).comp
          (Sheaf.restrictCoextendScalarsAdj _ ρ))) _]
  simp only [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight, hc Λ,
    conjugateEquiv_associator_inv, conjugateEquiv_associator_hom]
  ext F : 2
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app, Category.id_comp, Category.comp_id,
    conjugateEquiv_upperStarRestrictScalarsIso_hom_app]
  ext V : 3
  rfl

/-- Compatibility of `AlgebraicGeometry.Etale.upperStarRestrictScalarsIso` with the identity
isomorphisms `(𝟙 X)^* ≅ 𝟭`. -/
lemma upperStarRestrictScalarsIso_id_hom (X : Scheme.{u}) :
    (upperStarRestrictScalarsIso ρ (𝟙 X)).hom ≫
        Functor.whiskerRight (upperStarId _ X).hom (Sheaf.restrictScalars _ ρ) =
      Functor.whiskerLeft (Sheaf.restrictScalars _ ρ) (upperStarId _ X).hom ≫
        (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv := by
  have hc (Γ : Type (u + 1)) [CommRing Γ] :
      conjugateEquiv Adjunction.id (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Γ) (𝟙 X))
        (upperStarId _ X).hom = (lowerStarId (ModuleCat.{u + 1} Γ) X).inv :=
    congrArg Iso.hom (conjugateIsoEquiv_upperStarId _ X)
  apply (conjugateEquiv (Adjunction.id.comp (Sheaf.restrictCoextendScalarsAdj _ ρ))
    ((Sheaf.restrictCoextendScalarsAdj _ ρ).comp
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X)))).injective
  rw [← conjugateEquiv_comp _
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') (𝟙 X)).comp
      (Sheaf.restrictCoextendScalarsAdj _ ρ)) _,
    ← conjugateEquiv_comp _
      ((Sheaf.restrictCoextendScalarsAdj _ ρ).comp Adjunction.id) _,
    ← conjugateEquiv_comp _ (Sheaf.restrictCoextendScalarsAdj _ ρ) _]
  simp only [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight, hc Λ, hc Λ',
    conjugateEquiv_leftUnitor_inv, conjugateEquiv_rightUnitor_hom]
  ext F : 2
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, Category.comp_id,
    conjugateEquiv_upperStarRestrictScalarsIso_hom_app]
  ext V : 3
  rfl

/-- Compatibility of `AlgebraicGeometry.Etale.upperStarRestrictScalarsIso` with the transport
`f^* = g^*` along an equality `f = g` of morphisms. -/
lemma upperStarRestrictScalarsIso_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (upperStarRestrictScalarsIso ρ f).hom ≫
        Functor.whiskerRight (eqToHom (congrArg (fun k ↦ (k)^*[ModuleCat.{u + 1} Λ']) h))
          (Sheaf.restrictScalars _ ρ) =
      Functor.whiskerLeft (Sheaf.restrictScalars _ ρ)
          (eqToHom (congrArg (fun k ↦ (k)^*[ModuleCat.{u + 1} Λ]) h)) ≫
        (upperStarRestrictScalarsIso ρ g).hom := by
  subst h
  simp

end Coherence

section Derived

/-- The components of the composition isomorphism `L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*` of derived
pullbacks, in terms of the functors induced levelwise by the exact pullbacks. -/
lemma leftDerivedUpperStarComp_hom_app (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {T S R : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ R)
    (K : DerivedCategory (Sheaf R.smallEtaleTopology A)) :
    (leftDerivedUpperStarComp A g₁ g₂).hom.app K =
      (leftDerivedUpperStarIsoMapDerivedCategory A (g₁ ≫ g₂)).hom.app K ≫
        (Functor.mapDerivedCategoryTriangleIso (upperStarComp A g₁ g₂)).hom.app K ≫
        ((g₁)^*[A]).mapDerivedCategory.map
          ((leftDerivedUpperStarIsoMapDerivedCategory A g₂).inv.app K) ≫
        (leftDerivedUpperStarIsoMapDerivedCategory A g₁).inv.app
          (((g₂)^*[A]).leftDerivedFunctor.obj K) := by
  simp [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, leftDerivedUpperStarIsoMapDerivedCategory]

/-- The components of the identity isomorphism `L(𝟙 X)^* ≅ 𝟭` of the derived pullback, in terms
of the functor induced levelwise by the exact pullback. -/
lemma leftDerivedUpperStarId_hom_app (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (leftDerivedUpperStarId A X).hom.app K =
      (leftDerivedUpperStarIsoMapDerivedCategory A (𝟙 X)).hom.app K ≫
        (Functor.mapDerivedCategoryNatIso (upperStarId A X) ≪≫
          Functor.mapDerivedCategoryIdIso _).hom.app K := by
  simp [leftDerivedUpperStarId, Functor.leftDerivedFunctorNatIso,
    leftDerivedUpperStarIsoMapDerivedCategory]

variable {Y Z : Scheme.{u}} (g : Y ⟶ Z)

/-- The derived pullback commutes with restriction of scalars: for `ρ : Λ →+* Λ'` and a
morphism of schemes `g : Y ⟶ Z`, the canonical isomorphism `Lg^* (Res K) ≅ Res (Lg^* K)` for `K`
in the derived category of étale sheaves of `Λ'`-modules on `Z`. Both derived pullbacks are
computed levelwise (`AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory`), and
the isomorphism is induced by `AlgebraicGeometry.Etale.upperStarRestrictScalarsIso`. It is used
for the compatible systems of Frobenius coefficient morphisms. -/
noncomputable def leftDerivedUpperStarRestrictScalarsIso :
    Sheaf.derivedRestrictScalars Z.smallEtaleTopology ρ ⋙
        L((g)^*[ModuleCat.{u + 1} Λ]) ≅
      L((g)^*[ModuleCat.{u + 1} Λ']) ⋙
        Sheaf.derivedRestrictScalars Y.smallEtaleTopology ρ :=
  Functor.isoWhiskerLeft (Sheaf.derivedRestrictScalars Z.smallEtaleTopology ρ)
      (leftDerivedUpperStarIsoMapDerivedCategory _ g) ≪≫
    Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso ρ g) ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory _ g).symm
      (Sheaf.derivedRestrictScalars Y.smallEtaleTopology ρ)

/-- The components of `AlgebraicGeometry.Etale.leftDerivedUpperStarRestrictScalarsIso`. -/
lemma leftDerivedUpperStarRestrictScalarsIso_hom_app
    (K : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    (leftDerivedUpperStarRestrictScalarsIso ρ g).hom.app K =
      (leftDerivedUpperStarIsoMapDerivedCategory _ g).hom.app
          ((Sheaf.derivedRestrictScalars _ ρ).obj K) ≫
        (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso ρ g)).hom.app K ≫
        (Sheaf.derivedRestrictScalars _ ρ).map
          ((leftDerivedUpperStarIsoMapDerivedCategory _ g).inv.app K) :=
  rfl

/-- Compatibility of `AlgebraicGeometry.Etale.leftDerivedUpperStarRestrictScalarsIso` with
the composition isomorphisms `L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*` (over `Λ'` on the left, over `Λ` on
the right). -/
lemma leftDerivedUpperStarRestrictScalarsIso_comp_hom_app {T S R : Scheme.{u}} (g₁ : T ⟶ S)
    (g₂ : S ⟶ R) (K : DerivedCategory (Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    (leftDerivedUpperStarRestrictScalarsIso ρ (g₁ ≫ g₂)).hom.app K ≫
        (Sheaf.derivedRestrictScalars _ ρ).map ((leftDerivedUpperStarComp _ g₁ g₂).hom.app K) =
      (leftDerivedUpperStarComp _ g₁ g₂).hom.app ((Sheaf.derivedRestrictScalars _ ρ).obj K) ≫
        (L((g₁)^*[ModuleCat.{u + 1} Λ])).map
          ((leftDerivedUpperStarRestrictScalarsIso ρ g₂).hom.app K) ≫
        (leftDerivedUpperStarRestrictScalarsIso ρ g₁).hom.app
          ((L((g₂)^*[ModuleCat.{u + 1} Λ'])).obj K) := by
  have H := Functor.mapDerivedCategorySquareIso_hom_app_comp
    (upperStarRestrictScalarsIso ρ g₂) (upperStarRestrictScalarsIso ρ g₁)
    (upperStarRestrictScalarsIso ρ (g₁ ≫ g₂)) (upperStarComp _ g₁ g₂) (upperStarComp _ g₁ g₂)
    (fun X ↦ by simpa using congr_app (upperStarRestrictScalarsIso_comp_hom ρ g₁ g₂) X) K
  have hnat :=
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso ρ g₁)).hom.naturality
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ') g₂).inv.app K)
  simp only [Functor.comp_map] at hnat
  rw [leftDerivedUpperStarComp_hom_app, leftDerivedUpperStarComp_hom_app,
    leftDerivedUpperStarRestrictScalarsIso_hom_app,
    leftDerivedUpperStarRestrictScalarsIso_hom_app,
    leftDerivedUpperStarRestrictScalarsIso_hom_app]
  simp only [Category.assoc]
  -- `erw`: the instance arguments of the derived pullbacks are found along different paths
  erw [NatIso.naturality_1_assoc]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id_app_assoc]
  simp only [Functor.map_comp, Category.assoc]
  -- `erw`: `Sheaf.derivedRestrictScalars` is the reducible `mapDerivedCategory` of `H`
  erw [reassoc_of% hnat, reassoc_of% H]

/-- Compatibility of `AlgebraicGeometry.Etale.leftDerivedUpperStarRestrictScalarsIso` with
the identity isomorphisms `L(𝟙 X)^* ≅ 𝟭`. -/
lemma leftDerivedUpperStarRestrictScalarsIso_id_hom_app (X : Scheme.{u})
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    (leftDerivedUpperStarRestrictScalarsIso ρ (𝟙 X)).hom.app K ≫
        (Sheaf.derivedRestrictScalars _ ρ).map ((leftDerivedUpperStarId _ X).hom.app K) =
      (leftDerivedUpperStarId _ X).hom.app ((Sheaf.derivedRestrictScalars _ ρ).obj K) := by
  have H := Functor.mapDerivedCategorySquareIso_hom_app_id (upperStarRestrictScalarsIso ρ (𝟙 X))
    (upperStarId _ X) (upperStarId _ X)
    (fun Y ↦ by simpa using congr_app (upperStarRestrictScalarsIso_id_hom ρ X) Y) K
  rw [leftDerivedUpperStarRestrictScalarsIso_hom_app, leftDerivedUpperStarId_hom_app,
    leftDerivedUpperStarId_hom_app]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app_assoc]
  -- `erw`: `Sheaf.derivedRestrictScalars` is the reducible `mapDerivedCategory` of `H`
  erw [H]

/-- Compatibility of `AlgebraicGeometry.Etale.leftDerivedUpperStarRestrictScalarsIso` with
the transport `Lf^* = Lg^*` along an equality `f = g` of morphisms. -/
lemma leftDerivedUpperStarRestrictScalarsIso_congr_hom_app {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    (leftDerivedUpperStarRestrictScalarsIso ρ f).hom.app K ≫
        (Sheaf.derivedRestrictScalars _ ρ).map
          ((eqToHom (congrArg (fun k ↦ L((k)^*[ModuleCat.{u + 1} Λ'])) h)).app K) =
      (eqToHom (congrArg (fun k ↦ L((k)^*[ModuleCat.{u + 1} Λ])) h)).app
          ((Sheaf.derivedRestrictScalars _ ρ).obj K) ≫
        (leftDerivedUpperStarRestrictScalarsIso ρ g).hom.app K := by
  subst h
  simp

end Derived

end AlgebraicGeometry.Etale
