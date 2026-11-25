/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections

/-!
# Vanishing of derived global sections of units along composites

For a morphism `f : X' ⟶ X` of schemes and `K ∈ D(X_ét)`, write `η_f(K) : K ⟶ Rf_* f^* K` for
the unit of the derived adjunction `f^* ⊣ Rf_*`
(`AlgebraicGeometry.Etale.mapDerivedUpperStarLowerStarAdjunction`). For a composite `g ≫ f`, the
unit `η_{g ≫ f}` is, up to the composition isomorphisms, the composite of `η_f` and of
`Rf_*(η_g)` (`AlgebraicGeometry.Etale.mapDerivedUpperStarLowerStarAdjunction_unit_comp`).
Consequently:

* if `RΓ(X, η_f(K)) = 0`, then `RΓ(X, η_{g ≫ f}(K)) = 0`
  (`AlgebraicGeometry.Etale.rightDerivedGlobalSections_map_unit_comp_eq_zero`);
* if `RΓ(X, η_{g ≫ f}(K)) = 0` and `RΓ(X', η_g(f^* K))` is an isomorphism, then
  `RΓ(X, η_f(K)) = 0`
  (`AlgebraicGeometry.Etale.rightDerivedGlobalSections_map_unit_eq_zero_of_comp`).

The comparison between `RΓ(X, Rf_* -)` and `RΓ(X', -)` used here is the Leray isomorphism
`AlgebraicGeometry.Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- **The derived unit along a composite.** For `g : Z ⟶ Y` and `f : Y ⟶ X`, the unit
`K ⟶ R(g ≫ f)_* (g ≫ f)^* K`, followed by the composition isomorphism
`(g ≫ f)^* K ≅ g^* f^* K`, is the unit `K ⟶ Rf_* f^* K` followed by `Rf_*` of the unit
`f^* K ⟶ Rg_* g^* f^* K` and the composition isomorphism `Rf_* Rg_* ≅ R(g ≫ f)_*`. -/
theorem mapDerivedUpperStarLowerStarAdjunction_unit_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X)
    (g : Z ⟶ Y) (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (mapDerivedUpperStarLowerStarAdjunction A (g ≫ f)).unit.app K ≫
      R((g ≫ f)_*[A]).map
        ((Functor.mapDerivedCategoryNatIso (Etale.upperStarComp A g f) ≪≫
          (Functor.mapDerivedCategoryCompIso ((f)^*[A]) ((g)^*[A])).symm).hom.app K) =
    (mapDerivedUpperStarLowerStarAdjunction A f).unit.app K ≫
      R((f)_*[A]).map
        ((mapDerivedUpperStarLowerStarAdjunction A g).unit.app (D((f)^*[A]).obj K)) ≫
      (rightDerivedLowerStarComp A g f).hom.app
        (D((g)^*[A]).obj (D((f)^*[A]).obj K)) := by
  simpa only [rightDerivedLowerStarComp, Iso.symm_hom, conjugateIsoEquiv_apply_inv,
    Iso.symm_inv, Adjunction.comp_unit_app, Category.assoc, Functor.comp_obj] using
    (unit_conjugateEquiv
      ((mapDerivedUpperStarLowerStarAdjunction A f).comp
        (mapDerivedUpperStarLowerStarAdjunction A g))
      (mapDerivedUpperStarLowerStarAdjunction A (g ≫ f))
      (Functor.mapDerivedCategoryNatIso (Etale.upperStarComp A g f) ≪≫
        (Functor.mapDerivedCategoryCompIso ((f)^*[A]) ((g)^*[A])).symm).hom K).symm

/-- Naturality of the Leray isomorphism: `RΓ(X, Rf_* φ)` corresponds to `RΓ(X', φ)`. -/
lemma rightDerivedGlobalSections_map_rightDerivedLowerStar_map {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M M' : DerivedCategory (Sheaf Y.smallEtaleTopology A)} (φ : M ⟶ M') :
    (rightDerivedGlobalSections A X).map (R((f)_*[A]).map φ) =
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A f).hom.app M ≫
        (rightDerivedGlobalSections A Y).map φ ≫
        (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A f).inv.app M' := by
  have h := (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A f).hom.naturality φ
  dsimp only [Functor.comp_map] at h
  rw [← reassoc_of% h, Iso.hom_inv_id_app]
  exact (Category.comp_id _).symm

/-- If `RΓ(X, η_f(K))` vanishes, then so does `RΓ(X, η_{g ≫ f}(K))`. -/
theorem rightDerivedGlobalSections_map_unit_comp_eq_zero {X Y Z : Scheme.{u}} (f : Y ⟶ X)
    (g : Z ⟶ Y) (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (h : (rightDerivedGlobalSections A X).map
      ((mapDerivedUpperStarLowerStarAdjunction A f).unit.app K) = 0) :
    (rightDerivedGlobalSections A X).map
      ((mapDerivedUpperStarLowerStarAdjunction A (g ≫ f)).unit.app K) = 0 := by
  have hc := congrArg (rightDerivedGlobalSections A X).map
    (mapDerivedUpperStarLowerStarAdjunction_unit_comp A f g K)
  rw [Functor.map_comp, Functor.map_comp, h, zero_comp] at hc
  rw [← cancel_mono ((rightDerivedGlobalSections A X).map (R((g ≫ f)_*[A]).map
    ((Functor.mapDerivedCategoryNatIso (Etale.upperStarComp A g f) ≪≫
      (Functor.mapDerivedCategoryCompIso ((f)^*[A]) ((g)^*[A])).symm).hom.app K))), hc, zero_comp]

/-- If `RΓ(X, η_{g ≫ f}(K))` vanishes and `RΓ(Y, η_g(f^* K))` is an isomorphism, then
`RΓ(X, η_f(K))` vanishes. -/
theorem rightDerivedGlobalSections_map_unit_eq_zero_of_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X)
    (g : Z ⟶ Y) (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (h : (rightDerivedGlobalSections A X).map
      ((mapDerivedUpperStarLowerStarAdjunction A (g ≫ f)).unit.app K) = 0)
    (hg : IsIso ((rightDerivedGlobalSections A Y).map
      ((mapDerivedUpperStarLowerStarAdjunction A g).unit.app (D((f)^*[A]).obj K)))) :
    (rightDerivedGlobalSections A X).map
      ((mapDerivedUpperStarLowerStarAdjunction A f).unit.app K) = 0 := by
  have hc := congrArg (rightDerivedGlobalSections A X).map
    (mapDerivedUpperStarLowerStarAdjunction_unit_comp A f g K)
  rw [Functor.map_comp, h, zero_comp, Functor.map_comp, Functor.map_comp] at hc
  have : IsIso ((rightDerivedGlobalSections A X).map
      (R((f)_*[A]).map ((mapDerivedUpperStarLowerStarAdjunction A g).unit.app
        (D((f)^*[A]).obj K)))) := by
    rw [rightDerivedGlobalSections_map_rightDerivedLowerStar_map]
    infer_instance
  rw [← cancel_mono ((rightDerivedGlobalSections A X).map
      (R((f)_*[A]).map ((mapDerivedUpperStarLowerStarAdjunction A g).unit.app
        (D((f)^*[A]).obj K))) ≫
      (rightDerivedGlobalSections A X).map ((rightDerivedLowerStarComp A g f).hom.app
        (D((g)^*[A]).obj (D((f)^*[A]).obj K)))), zero_comp, hc]

end AlgebraicGeometry.Etale
