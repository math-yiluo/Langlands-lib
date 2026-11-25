/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.UnitSection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Restriction

/-!
# The canonical morphisms `g^* ℚ̄_ℓ ⟶ ℚ̄_ℓ`

For a morphism of schemes `g : W ⟶ V` the canonical morphism
`g^* ℚ̄_ℓ,V ⟶ ℚ̄_ℓ,W` (`AlgebraicGeometry.ProEtale.upperStarAdicConstantSheafHom`) is adjoint to
the pullback of functions `ℚ̄_ℓ,V ⟶ g_* ℚ̄_ℓ,W`. These morphisms satisfy the cocycle condition
for composites (`AlgebraicGeometry.ProEtale.upperStarAdicConstantSheafHom_comp`), and for an
isomorphism `e` the canonical morphism is the identification `e^* ≅ (e⁻¹)_*` followed by
`(e⁻¹)_* ℚ̄_ℓ ≅ ℚ̄_ℓ`
(`upperStarIsoLowerStarInv_hom_app_comp_adicConstantSheafLowerStarIso_hom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

variable (l) in
/-- The canonical morphism `g^* ℚ̄_ℓ ⟶ ℚ̄_ℓ` is adjoint to the pullback of functions. -/
lemma unit_app_comp_lowerStar_map_upperStarAdicConstantSheafHom {V W : Scheme.{u}}
    (g : W ⟶ V) :
    (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g).unit.app _ ≫
        (g)_*[WeilCoefficients.{u} l].map (upperStarAdicConstantSheafHom l g) =
      adicConstantSheafToLowerStar l g := by
  exact (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

variable (l) in
/-- **Cocycle condition** for the canonical morphisms `g^* ℚ̄_ℓ ⟶ ℚ̄_ℓ`: for `h₁ : T ⟶ S` and
`h₂ : S ⟶ R`, the composite `(h₁ ≫ h₂)^* ℚ̄_ℓ ≅ h₁^* h₂^* ℚ̄_ℓ ⟶ h₁^* ℚ̄_ℓ ⟶ ℚ̄_ℓ` is the canonical
morphism. Both are adjoint to the pullback of functions along `h₁ ≫ h₂`. -/
lemma upperStarAdicConstantSheafHom_comp {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) :
    (upperStarComp (WeilCoefficients.{u} l) h₁ h₂).hom.app (adicConstantSheaf l R) ≫
        (h₁)^*[WeilCoefficients.{u} l].map (upperStarAdicConstantSheafHom l h₂) ≫
        upperStarAdicConstantSheafHom l h₁ =
      upperStarAdicConstantSheafHom l (h₁ ≫ h₂) := by
  apply ((upperStarLowerStarAdjunction (WeilCoefficients.{u} l) (h₁ ≫ h₂)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    unit_app_comp_lowerStar_map_upperStarAdicConstantSheafHom, Functor.map_comp,
    ← upperStarFactor_rfl,
    reassoc_of% upperStarLowerStarAdjunction_unit_app_comp_map_upperStarFactor]
  have n₁ := (lowerStarFactor (WeilCoefficients.{u} l) (rfl : h₁ ≫ h₂ = h₁ ≫ h₂)).hom.naturality
    ((h₁)^*[WeilCoefficients.{u} l].map (upperStarAdicConstantSheafHom l h₂) ≫
      upperStarAdicConstantSheafHom l h₁)
  simp only [Functor.comp_map] at n₁
  have key : (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) h₁).unit.app _ ≫
      (h₁)_*[WeilCoefficients.{u} l].map
        ((h₁)^*[WeilCoefficients.{u} l].map (upperStarAdicConstantSheafHom l h₂) ≫
          upperStarAdicConstantSheafHom l h₁) =
      upperStarAdicConstantSheafHom l h₂ ≫ adicConstantSheafToLowerStar l h₁ := by
    rw [Functor.map_comp]
    erw [(upperStarLowerStarAdjunction _ h₁).unit_naturality_assoc]
    rw [unit_app_comp_lowerStar_map_upperStarAdicConstantSheafHom]
  rw [← n₁]
  rw [← Functor.map_comp_assoc, key, Functor.map_comp, Category.assoc,
    reassoc_of% unit_app_comp_lowerStar_map_upperStarAdicConstantSheafHom,
    ← adicConstantSheafToLowerStar_comp, ← lowerStarComp_trans_lowerStarCongr, lowerStarCongr_rfl,
    Iso.trans_refl]

variable (l) in
/-- For an isomorphism `e : X ≅ Y`, the canonical morphism `e^* ℚ̄_ℓ ⟶ ℚ̄_ℓ` is the identification
`e^* ≅ (e⁻¹)_*` followed by `(e⁻¹)_* ℚ̄_ℓ ≅ ℚ̄_ℓ`. -/
lemma upperStarIsoLowerStarInv_hom_app_comp_adicConstantSheafLowerStarIso_hom {X Y : Scheme.{u}}
    (e : X ≅ Y) :
    (upperStarIsoLowerStarInv (WeilCoefficients.{u} l) e).hom.app (adicConstantSheaf l Y) ≫
        (adicConstantSheafLowerStarIso l e.symm).hom =
      upperStarAdicConstantSheafHom l e.hom := by
  apply ((upperStarLowerStarAdjunction (WeilCoefficients.{u} l) e.hom).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    unit_app_comp_lowerStar_map_upperStarAdicConstantSheafHom, Functor.map_comp,
    reassoc_of% upperStarLowerStarAdjunction_unit_app_comp_map_upperStarIsoLowerStarInv]
  ext V : 3
  ext x
  refine adicConstantSheaf_ext fun y ↦ ?_
  simp only [lowerStarUnit, Iso.trans_inv, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, lowerStarFactor_inv_app_hom_app,
    lowerStarId_inv_app_hom_app, lowerStar_map_hom_app', adicConstantSheafLowerStarIso_hom_hom_app]
  simp only [adicConstantSheaf_obj_map, ← Functor.map_comp, ← op_comp]
  refine congrArg (fun φ : ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ e.hom).obj
    V.unop).left ⟶ V.unop.left ↦ x.down.1 (φ.base y)) (?_ : _ = pullback.fst _ e.hom)
  simp only [Functor.id_obj, Functor.comp_obj, Functor.const_obj_obj, Iso.symm_hom,
    MorphismProperty.Over.pullback_obj_hom, Iso.symm_inv, Quiver.Hom.unop_op,
    MorphismProperty.Over.pullbackComp_inv_app_left, op_unop,
    MorphismProperty.Over.pullbackId_hom_app_left, Category.assoc, limit.lift_π,
    PullbackCone.mk_π_app, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]
  erw [pullback.lift_fst_assoc]
  exact Category.id_comp _

end AlgebraicGeometry.ProEtale
