/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Germ
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.SectionsMonoidal

/-!
# Germs and the monoidal structures

For sheaves of `ℚ̄_ℓ`-modules on the small pro-étale site of `Y` and a morphism `g : Z ⟶ Y`, the
functor `P ↦ Γ(Z, g^* P)` is lax monoidal, as the composite of the monoidal pullback `g^*` and
the lax monoidal global sections. Its tensor comparison sends the tensor product of the germs of
two sections `σ`, `τ` over `V` along a lift `t` to the germ of the section `σ ⊗ τ` of `P ⊗ Q`
(`AlgebraicGeometry.ProEtale.germ_tensor`), and its unit is the germ of the unit section
(`AlgebraicGeometry.ProEtale.germ_unit`). Both follow from the monoidality of the adjunction
`g^* ⊣ g_*`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal Opposite Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {l : ℕ} [Fact l.Prime] {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The unit of `g^* ⊣ g_*` at a tensor product, on sections over `V`. -/
@[reassoc]
lemma μ_app_comp_unit_app_tensor_hom_app (P Q : Sheaf (ProEt.topology Y) (WeilCoefficients.{u} l))
    (V : Y.ProEt) :
    (μ (sheafToPresheaf (ProEt.topology Y) (WeilCoefficients.{u} l)) P Q).app (op V) ≫
        ((upperStarLowerStarAdjunction _ g).unit.app (P ⊗ Q)).hom.app (op V) =
      (((upperStarLowerStarAdjunction _ g).unit.app P).hom.app (op V) ⊗ₘ
          ((upperStarLowerStarAdjunction _ g).unit.app Q).hom.app (op V)) ≫
        (μ (sheafToPresheaf (ProEt.topology Z) (WeilCoefficients.{u} l)) ((g)^*[_].obj P)
          ((g)^*[_].obj Q)).app (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V)) ≫
        (μ (g)^*[WeilCoefficients.{u} l] P Q).hom.app
          (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V)) := by
  have h := (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g).unit_app_tensor_comp_map_δ
    P Q
  have h₁ : (upperStarLowerStarAdjunction _ g).unit.app (P ⊗ Q) =
      ((upperStarLowerStarAdjunction _ g).unit.app P ⊗ₘ
        (upperStarLowerStarAdjunction _ g).unit.app Q) ≫
        μ (g)_*[WeilCoefficients.{u} l] _ _ ≫ (g)_*[_].map (μ (g)^*[_] P Q) := by
    rw [← Category.assoc, ← h, Category.assoc, ← Functor.map_comp]
    erw [Functor.Monoidal.δ_μ]
    rw [CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).symm
  have h₂ := congr_app (μ_natural (sheafToPresheaf (ProEt.topology Y) (WeilCoefficients.{u} l))
    ((upperStarLowerStarAdjunction _ g).unit.app P)
    ((upperStarLowerStarAdjunction _ g).unit.app Q)) (op V)
  simp only [NatTrans.comp_app, Monoidal.tensorHom_app, ObjectProperty.ι_map,
    Functor.comp_obj, Functor.id_obj] at h₂
  rw [h₁]
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  erw [← reassoc_of% h₂]
  rw [μ_sheafToPresheaf_app_comp_μ_lowerStar_app_assoc]
  rfl

/-- The unit of `g^* ⊣ g_*` at the unit object, on sections over `V`. -/
@[reassoc]
lemma ε_app_comp_unit_app_tensorUnit_hom_app (V : Y.ProEt) :
    (ε (sheafToPresheaf (ProEt.topology Y) (WeilCoefficients.{u} l))).app (op V) ≫
        ((upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g).unit.app (𝟙_ _)).hom.app
          (op V) =
      (ε (sheafToPresheaf (ProEt.topology Z) (WeilCoefficients.{u} l))).app
          (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V)) ≫
        (ε (g)^*[WeilCoefficients.{u} l]).hom.app
          (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V)) := by
  have h := (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g).unit_app_unit_comp_map_η
  have h₁ : (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g).unit.app (𝟙_ _) =
      ε (g)_*[WeilCoefficients.{u} l] ≫ (g)_*[_].map (ε (g)^*[_]) := by
    rw [← h, Category.assoc, ← Functor.map_comp]
    erw [Functor.Monoidal.η_ε]
    rw [CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).symm
  rw [h₁]
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  rw [ε_sheafToPresheaf_app_comp_ε_lowerStar_app_assoc g (op V)]
  rfl

variable {g}

/-- **Germs of tensor products.** The tensor comparison of the lax monoidal functor
`Γ(Z, g^* -)` sends the tensor product of the germs of `σ` and `τ` to the germ of `σ ⊗ τ`. -/
@[reassoc]
lemma germ_tensor (P Q : Sheaf (ProEt.topology Y) (WeilCoefficients.{u} l)) {V : Y.ProEt}
    (t : ProEt.mk (𝟙 Z) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V) :
    (germ _ g P t ⊗ₘ germ _ g Q t) ≫ μ ((g)^*[_] ⋙ Sheaf.Γ _ _) P Q =
      (μ (sheafToPresheaf _ _) P Q).app (op V) ≫ germ _ g (P ⊗ Q) t := by
  have n₁ := (μ (sheafToPresheaf (ProEt.topology Z) (WeilCoefficients.{u} l)) ((g)^*[_].obj P)
    ((g)^*[_].obj Q)).naturality t.op
  have n₂ := (μ (g)^*[WeilCoefficients.{u} l] P Q).hom.naturality t.op
  have n₃ := (Sheaf.ΓNatIsoSheafSections _ (WeilCoefficients.{u} l)
    (ProEt.isTerminalMkId Z)).inv.naturality (μ (g)^*[WeilCoefficients.{u} l] P Q)
  simp only [Monoidal.tensorObj_map] at n₁
  rw [Functor.LaxMonoidal.comp_μ, μ_Γ, germ, germ, germ,
    μ_app_comp_unit_app_tensor_hom_app_assoc]
  simp only [Category.assoc, tensorHom_comp_tensorHom_assoc, Iso.inv_hom_id_app]
  rw [← tensorHom_comp_tensorHom_assoc]
  congr 1
  erw [reassoc_of% n₁]
  congr 1
  erw [← n₃, reassoc_of% n₂]

/-- **The germ of the unit section.** The unit of the lax monoidal functor `Γ(Z, g^* -)` is the
germ of the unit section. -/
lemma germ_unit {V : Y.ProEt}
    (t : ProEt.mk (𝟙 Z) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V) :
    ε ((g)^*[WeilCoefficients.{u} l] ⋙ Sheaf.Γ _ _) =
      (ε (sheafToPresheaf _ _)).app (op V) ≫ germ _ g (𝟙_ _) t := by
  have n₁ := (ε (sheafToPresheaf (ProEt.topology Z) (WeilCoefficients.{u} l))).naturality t.op
  have n₂ := (ε (g)^*[WeilCoefficients.{u} l]).hom.naturality t.op
  have n₃ := (Sheaf.ΓNatIsoSheafSections _ (WeilCoefficients.{u} l)
    (ProEt.isTerminalMkId Z)).inv.naturality (ε (g)^*[WeilCoefficients.{u} l])
  rw [Functor.LaxMonoidal.comp_ε, ε_Γ, germ, ε_app_comp_unit_app_tensorUnit_hom_app_assoc]
  simp only [Category.assoc]
  erw [← n₃, ← reassoc_of% n₂, ← reassoc_of% n₁]
  simp only [Monoidal.tensorUnit_map]
  rfl

variable (g) in
/-- The lax monoidal functor `Γ(Z, g^* -)` is compatible with the braidings: `g^*` is braided,
being the strong monoidal left adjoint of the lax braided `g_*`, and taking sections is lax
braided. -/
lemma μ_comp_map_braiding_upperStar_comp_Γ
    (P Q : Sheaf (ProEt.topology Y) (WeilCoefficients.{u} l)) :
    μ ((g)^*[_] ⋙ Sheaf.Γ _ _) P Q ≫ ((g)^*[_] ⋙ Sheaf.Γ _ _).map (β_ P Q).hom =
      (β_ _ _).hom ≫ μ ((g)^*[_] ⋙ Sheaf.Γ _ _) Q P := by
  have : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g)
      Functor.Monoidal.toOplaxMonoidal _ :=
    isMonoidal_upperStarLowerStarAdjunction _ _
  have h₁ := Adjunction.μ_comp_map_braiding
    (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g) P Q
  have h₂ := congr_app (Functor.LaxBraided.braided
    (F := sheafToPresheaf (ProEt.topology Z) (WeilCoefficients.{u} l))
    ((g)^*[_].obj P) ((g)^*[_].obj Q)) (op (ProEt.mk (𝟙 Z)))
  simp only [NatTrans.comp_app] at h₂
  have n := (Sheaf.ΓNatIsoSheafSections _ (WeilCoefficients.{u} l)
    (ProEt.isTerminalMkId Z)).inv.naturality (β_ ((g)^*[_].obj P) ((g)^*[_].obj Q)).hom
  rw [Functor.LaxMonoidal.comp_μ, Functor.LaxMonoidal.comp_μ, Functor.comp_map, Category.assoc,
    ← Functor.map_comp, h₁, Functor.map_comp, μ_Γ, μ_Γ]
  simp only [Category.assoc]
  rw [← reassoc_of% n]
  erw [reassoc_of% h₂]
  exact BraidedCategory.braiding_naturality_assoc _ _ _

end AlgebraicGeometry.ProEtale
