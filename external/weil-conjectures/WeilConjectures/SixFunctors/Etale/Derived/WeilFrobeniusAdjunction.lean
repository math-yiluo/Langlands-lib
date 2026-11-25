/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.CompUnit
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit
public import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCoefficient

/-!
# Frobenius operators and the adjunction `La^* ⊣ Ra_*`

Let `g ≫ a = a ≫ h` be a commutative square, `a : X ⟶ Y`, and `ψ : Lg^* M ⟶ M` a Weil datum on
`M ∈ D(X_ét, Λ)`. The identification `Hom(Λ_X, M) ≅ Hom(Λ_Y, Ra_* M)` given by the adjunction
`La^* ⊣ Ra_*` and `La^* Λ_Y ≅ Λ_X` intertwines the Frobenius operator of `ψ` with the Frobenius
operator of the induced datum on `Ra_* M`
(`AlgebraicGeometry.Etale.frobeniusOperator_lowerStarWeilDatum_homEquiv`). The key input is the
compatibility of the canonical isomorphisms `Lf^* Λ ≅ Λ` with the composition of derived
pullbacks (`AlgebraicGeometry.Etale.derivedSquareUpperStarIso_hom_app_unit`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The canonical isomorphism `Lg^* Λ_Y ≅ Λ_Z` is the counit `η` of the oplax monoidal derived
pullback. -/
lemma leftDerivedUpperStarUnitIso_hom_eq_η {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    letI := leftDerivedUpperStarOplaxMonoidal (ModuleCat.{u + 1} Λ) g
    (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) g).hom =
      Functor.OplaxMonoidal.η (L((g)^*[ModuleCat.{u + 1} Λ])) := by
  have h := leftDerivedUpperStarUnitIso_hom_comp_ε (ModuleCat.{u + 1} Λ) g
  rw [leftDerivedUpperStar_η_eq]
  simp only [← Category.assoc]
  rw [IsIso.eq_comp_inv, h]
  simp only [Category.assoc]
  rfl

variable {X Y : Scheme.{u}} {a : X ⟶ Y} {g : X ⟶ X} {h : Y ⟶ Y}

/-- The canonical isomorphisms `Lf^* Λ ≅ Λ` are compatible with the square isomorphism
`La^* Lh^* ≅ Lg^* La^*` of a commutative square `g ≫ a = a ≫ h`. -/
lemma derivedSquareUpperStarIso_hom_app_unit (sq : CommSq g a a h) :
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app (𝟙_ _) ≫
        (L((g)^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarUnitIso _ a).hom ≫
          (leftDerivedUpperStarUnitIso _ g).hom =
      (L((a)^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarUnitIso _ h).hom ≫
        (leftDerivedUpperStarUnitIso _ a).hom := by
  rw [leftDerivedUpperStarUnitIso_hom_eq_η, leftDerivedUpperStarUnitIso_hom_eq_η,
    leftDerivedUpperStarUnitIso_hom_eq_η, derivedSquareUpperStarIso, Iso.trans_hom,
    NatTrans.comp_app, Category.assoc, leftDerivedUpperStarComp_hom_app_unit, Iso.symm_hom,
    ← leftDerivedUpperStarComp_hom_app_unit _ a h (g ≫ a) sq.w, Iso.inv_hom_id_app_assoc]

/-- **Frobenius operators and the adjunction `La^* ⊣ Ra_*`.** For a commutative square
`g ≫ a = a ≫ h` and a Weil datum `ψ` on `M`, the identification `Hom(Λ_X, M) ≅ Hom(Λ_Y, Ra_* M)`
intertwines the Frobenius operator of `ψ` with that of the induced datum on `Ra_* M`. -/
theorem frobeniusOperator_lowerStarWeilDatum_homEquiv (sq : CommSq g a a h)
    {M : DerivedCategoryModule Λ X} (ψ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ M)
    (x : 𝟙_ (DerivedCategoryModule Λ X) ⟶ M) :
    frobeniusOperator h (lowerStarWeilDatum sq ψ)
        ((derivedUpperStarLowerStarAdjunction _ a).homEquiv _ _
          ((leftDerivedUpperStarUnitIso _ a).hom ≫ x)) =
      (derivedUpperStarLowerStarAdjunction _ a).homEquiv _ _
        ((leftDerivedUpperStarUnitIso _ a).hom ≫ frobeniusOperator g ψ x) := by
  have hK := derivedSquareUpperStarIso_hom_app_unit (Λ := Λ) sq
  have hBC := (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).naturality
    ((leftDerivedUpperStarUnitIso _ a).hom ≫ x)
  simp only [Functor.comp_map] at hBC
  rw [frobeniusOperator_apply, frobeniusOperator_apply, Adjunction.homEquiv_unit,
    Adjunction.homEquiv_unit, lowerStarWeilDatum, Functor.map_comp, Category.assoc,
    reassoc_of% hBC, map_unit_derivedBaseChangeMap_app_assoc,
    ← (derivedUpperStarLowerStarAdjunction _ a).unit_naturality_assoc]
  simp only [← Functor.map_comp]
  congr 2
  have hK' : (L((a)^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarUnitIso _ h).inv ≫
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app (𝟙_ _) ≫
        (L((g)^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarUnitIso _ a).hom =
      (leftDerivedUpperStarUnitIso _ a).hom ≫ (leftDerivedUpperStarUnitIso _ g).inv := by
    rw [← cancel_mono (leftDerivedUpperStarUnitIso _ g).hom, Category.assoc, Category.assoc, hK,
      Category.assoc, Iso.inv_hom_id, Category.comp_id, ← Functor.map_comp_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  rw [Functor.map_comp, Category.assoc, reassoc_of% hK']

/-- The inverse of an isomorphism of Weil objects is a morphism of Weil objects. -/
lemma IsWeilMorphism.of_iso_inv {N P : DerivedCategoryModule Λ Y}
    {ψN : (L((h)^*[ModuleCat.{u + 1} Λ])).obj N ⟶ N}
    {ψP : (L((h)^*[ModuleCat.{u + 1} Λ])).obj P ⟶ P} (e : N ≅ P)
    (he : IsWeilMorphism h ψP ψN e.inv) : IsWeilMorphism h ψN ψP e.hom := by
  unfold IsWeilMorphism at *
  rw [← cancel_mono e.inv, Category.assoc, ← he, ← Functor.map_comp_assoc, e.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc, e.hom_inv_id,
    Category.comp_id]

/-- The shift compatibility `(Ra_* K)[n] ≅ Ra_*(K[n])` is a morphism of Weil objects, for the
data `(Ra_* φ)[n]` and `Ra_*(φ[n])`: the exchange map `Ex_*` commutes with the shifts. -/
lemma isWeilMorphism_rightDerivedLowerStar_commShiftIso_inv (sq : CommSq g a a h)
    {K : DerivedCategoryModule Λ X} (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K) (n : ℤ) :
    IsWeilMorphism h (shiftWeilDatum h (lowerStarWeilDatum sq φ) n)
      (lowerStarWeilDatum sq (shiftWeilDatum g φ n))
      (((R((a)_*[ModuleCat.{u + 1} Λ])).commShiftIso n).inv.app K) := by
  have hEx := NatTrans.shift_app_comm (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq) n K
  simp only [Functor.comp_obj, Functor.commShiftIso_comp_hom_app, Category.assoc] at hEx
  have h' := ((R((a)_*[ModuleCat.{u + 1} Λ])).commShiftIso n).inv.naturality φ
  dsimp at h'
  unfold IsWeilMorphism shiftWeilDatum lowerStarWeilDatum
  rw [← cancel_epi ((L((h)^*[ModuleCat.{u + 1} Λ])).map
    (((R((a)_*[ModuleCat.{u + 1} Λ])).commShiftIso n).hom.app K))]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hEx, h', Iso.hom_inv_id_app_assoc]

variable (Λ) in
/-- `Hⁿ(X, Λ) = Hom(Λ_X, Λ_X[n]) ≅ Hom(Λ_Y, (Ra_* Λ_X)[n])`, through the adjunction
`La^* ⊣ Ra_*` and `La^* Λ_Y ≅ Λ_X`. -/
noncomputable def unitShiftAddEquivLowerStar (a : X ⟶ Y) (n : ℤ) :
    (𝟙_ (DerivedCategoryModule Λ X) ⟶ (𝟙_ (DerivedCategoryModule Λ X))⟦n⟧) ≃+
      (𝟙_ (DerivedCategoryModule Λ Y) ⟶
        ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (𝟙_ (DerivedCategoryModule Λ X)))⟦n⟧) where
  toFun x := (derivedUpperStarLowerStarAdjunction _ a).homEquiv _ _
      ((leftDerivedUpperStarUnitIso _ a).hom ≫ x) ≫
    ((R((a)_*[ModuleCat.{u + 1} Λ])).commShiftIso n).hom.app _
  invFun z := (leftDerivedUpperStarUnitIso _ a).inv ≫
    ((derivedUpperStarLowerStarAdjunction _ a).homEquiv _ _).symm
      (z ≫ ((R((a)_*[ModuleCat.{u + 1} Λ])).commShiftIso n).inv.app _)
  left_inv x := by simp
  right_inv z := by simp
  map_add' x x' := by
    simp [Adjunction.homEquiv_unit, Preadditive.comp_add, Preadditive.add_comp]

/-- **Frobenius operators on `Hⁿ(X, Λ)` and on `Hⁿ(Y, Ra_* Λ)`.** For a commutative square
`g ≫ a = a ≫ h`, the identification `Hom(Λ_X, Λ_X[n]) ≅ Hom(Λ_Y, (Ra_* Λ_X)[n])` intertwines the
Frobenius operators of the canonical Weil data, `Ra_*` carrying the induced datum. -/
theorem frobeniusOperator_unitShiftAddEquivLowerStar (sq : CommSq g a a h) (n : ℤ)
    (x : 𝟙_ (DerivedCategoryModule Λ X) ⟶ (𝟙_ (DerivedCategoryModule Λ X))⟦n⟧) :
    frobeniusOperator h (shiftWeilDatum h
        (lowerStarWeilDatum sq (leftDerivedUpperStarUnitIso _ g).hom) n)
      (unitShiftAddEquivLowerStar Λ a n x) =
      unitShiftAddEquivLowerStar Λ a n (frobeniusOperator g
        (shiftWeilDatum g (leftDerivedUpperStarUnitIso _ g).hom n) x) := by
  have hc := IsWeilMorphism.of_iso_inv (((R((a)_*[ModuleCat.{u + 1} Λ])).commShiftIso n).app _)
    (isWeilMorphism_rightDerivedLowerStar_commShiftIso_inv sq
      (leftDerivedUpperStarUnitIso _ g).hom n)
  exact (hc.frobeniusOperator_comp _).trans
    (congrArg (· ≫ _) (frobeniusOperator_lowerStarWeilDatum_homEquiv sq _ x))

end AlgebraicGeometry.Etale
