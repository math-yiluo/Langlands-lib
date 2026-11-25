/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ContinuousSheafPullback
public import WeilConjectures.SixFunctors.ProEtale.Adic.GlobalSectionsExt

/-!
# The two isomorphisms `ℤ ≅ (e⁻¹)_* ℤ` agree

For an isomorphism `e : X ≅ Y`, the isomorphism `ℤ_X ≅ (e⁻¹)_* ℤ_Y` through the sheaves of
continuous functions (`AlgebraicGeometry.ProEtale.constantIntIsoLowerStar`) is the map
restricting the global section `1` (`AlgebraicGeometry.ProEtale.constantIntSheafToLowerStar`):
both send `1` to the constant function `1`
(`AlgebraicGeometry.ProEtale.constantIntSheafToLowerStar_eq_constantIntIsoLowerStar_hom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- The global section `1` of `ℤ_X` is the constant function `1` in `C(X, ℤ)`. -/
lemma constantSheafIsoContinuousSheaf_hom_app_one (X : Scheme.{u}) :
    (constantSheafIsoContinuousSheaf X ℤ).hom.hom.app (op (Scheme.ProEt.mk (𝟙 X)))
        (constantIntSheafHomAddEquiv _ (𝟙 _)) =
      ULift.up (ContinuousMap.const _ (1 : ℤ)) := by
  have h := toSheafify_constantSheafToContinuousSheaf X ℤ
  simp only [constantIntSheafHomAddEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply,
    constantSheafAdj, Adjunction.comp_homEquiv]
  have h' := ConcreteCategory.congr_hom
    (NatTrans.congr_app h (op (Scheme.ProEt.mk (𝟙 X)))) (ULift.up 1)
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h'
  exact h'

/-- The isomorphism `ℤ_X ≅ (e⁻¹)_* ℤ_Y` through the sheaves of continuous functions is the map
restricting the global section `1`. -/
lemma constantIntSheafToLowerStar_eq_constantIntIsoLowerStar_hom {X Y : Scheme.{u}} (e : X ≅ Y) :
    constantIntSheafToLowerStar e.inv = (constantIntIsoLowerStar e).hom := by
  rw [← cancel_mono ((e.inv)_*[AddCommGrpCat.{u + 1}].map
    (constantSheafIsoContinuousSheaf Y ℤ).hom)]
  have h : (constantIntIsoLowerStar e).hom ≫ (e.inv)_*[AddCommGrpCat.{u + 1}].map
      (constantSheafIsoContinuousSheaf Y ℤ).hom =
      (constantSheafIsoContinuousSheaf X ℤ).hom ≫ (continuousSheafIsoLowerStar e ℤ).hom := by
    simp [constantIntIsoLowerStar, ← Functor.map_comp]
  rw [h]
  apply (constantIntSheafHomAddEquiv _).injective
  rw [constantIntSheafHomAddEquiv_comp, constantIntSheafHomAddEquiv_comp,
    ← Category.id_comp (constantSheafIsoContinuousSheaf X ℤ).hom, constantIntSheafHomAddEquiv_comp,
    constantSheafIsoContinuousSheaf_hom_app_one, constantIntSheafToLowerStar,
    AddEquiv.apply_symm_apply]
  have hn := ConcreteCategory.congr_hom ((constantSheafIsoContinuousSheaf Y ℤ).hom.hom.naturality
    (overPullbackObjMkIdIso e.inv).hom.op) (constantIntSheafHomAddEquiv _ (𝟙 _))
  simp only [ConcreteCategory.comp_apply] at hn
  refine hn.trans ?_
  rw [constantSheafIsoContinuousSheaf_hom_app_one]
  rfl

end AlgebraicGeometry.ProEtale
