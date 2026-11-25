/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ContinuousSheafPullback
public import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorConj
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantCohomologyBaseChange

/-!
# Pullback of the cohomology `Hⁿ(S, ℚ̄_ℓ)` along an isomorphism

For an isomorphism of schemes `e : X ≅ Y`, the pullback `e^* = (e⁻¹)_*` of pro-étale sheaves and
the canonical isomorphism `(e⁻¹)_* ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,X`
(`AlgebraicGeometry.ProEtale.adicConstantSheafLowerStarIso`, which defines the Weil structure of
the constant Weil sheaf) induce the `ℚ̄_ℓ`-linear pullback
`e^* : Hⁿ(Y, ℚ̄_ℓ) ⟶ Hⁿ(X, ℚ̄_ℓ)` (`AlgebraicGeometry.ProEtale.adicConstantHPullback`). It extends
the pullback of the integral cohomology `Hⁿ(-, ℤ_ℓ)`
(`AlgebraicGeometry.ProEtale.adicConstantHPullback_integralToAdicConstantH`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Abelian

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (e : X ≅ Y)

/-- The isomorphism `(e⁻¹)_* ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,X` of underlying abelian sheaves. -/
noncomputable def adicConstantSheafAbLowerStarIso :
    (ProEtale.lowerStar AddCommGrpCat.{u + 1} e.inv).obj (adicConstantSheafAb l Y) ≅
      adicConstantSheafAb l X :=
  (sheafForget₂ (ULift.{u + 1} (PadicAlgCl l)) X).mapIso (adicConstantSheafLowerStarIso l e.symm)

lemma adicConstantSheafAbLowerStarIso_hom_hom_app (V : X.ProEtᵒᵖ) :
    (adicConstantSheafAbLowerStarIso l e).hom.hom.app V =
      (forget₂ _ AddCommGrpCat.{u + 1}).map ((adicFunctionsPresheaf l).map
        (pullback.lift (𝟙 V.unop.left) (V.unop.hom ≫ e.hom) (by simp)).op) :=
  congrArg (forget₂ _ AddCommGrpCat.{u + 1}).map
    (adicConstantSheafLowerStarIso_hom_hom_app l e.symm V)

/-- The pullback is compatible with the scalars of `ℚ̄_ℓ`. -/
lemma lowerStar_map_adicScalar_comp_adicConstantSheafAbLowerStarIso (c : PadicAlgCl l) :
    (ProEtale.lowerStar AddCommGrpCat.{u + 1} e.inv).map (adicScalar l Y c) ≫
        (adicConstantSheafAbLowerStarIso l e).hom =
      (adicConstantSheafAbLowerStarIso l e).hom ≫ adicScalar l X c := by
  ext V f
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, NatTrans.comp_app, adicConstantSheafAbLowerStarIso_hom_hom_app]
  rfl

/-- The pullback is compatible with the inclusion `C(-, ℤ_ℓ) ⊆ ℚ̄_ℓ`. -/
lemma lowerStar_map_continuousSheafToAdicConstantSheaf_comp :
    (ProEtale.lowerStar AddCommGrpCat.{u + 1} e.inv).map (continuousSheafToAdicConstantSheaf l Y) ≫
        (adicConstantSheafAbLowerStarIso l e).hom =
      (continuousSheafIsoLowerStar e ℤ_[l]).inv ≫ continuousSheafToAdicConstantSheaf l X := by
  rw [Iso.eq_inv_comp]
  ext V f
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, NatTrans.comp_app, adicConstantSheafAbLowerStarIso_hom_hom_app]
  let g : C(V.unop.left, ℤ_[l]) := f.down
  refine congrArg ULift.up (Subtype.ext (ContinuousMap.ext fun t ↦ ?_))
  have ht := congrArg (fun φ : V.unop.left ⟶ V.unop.left ↦ φ.base t)
    (pullback.lift_fst (f := V.unop.hom) (g := e.inv) (𝟙 V.unop.left) (V.unop.hom ≫ e.hom)
      (by simp))
  simp only [Scheme.Hom.comp_base, TopCat.comp_app, Scheme.Hom.id_base, TopCat.id_app] at ht
  exact congrArg (fun s ↦ algebraMap ℤ_[l] (PadicAlgCl l) (g s)) ht

/-- The pullback `e^* : Hⁿ(Y, ℚ̄_ℓ) ⟶ Hⁿ(X, ℚ̄_ℓ)` along an isomorphism `e : X ≅ Y`: an `Ext`-class
is pushed forward along the exact functor `e^* = (e⁻¹)_*` and read through `ℤ ≅ (e⁻¹)_* ℤ` and
`(e⁻¹)_* ℚ̄_ℓ ≅ ℚ̄_ℓ`. -/
noncomputable def adicConstantHPullback (n : ℕ) :
    AdicConstantH l Y n →ₗ[PadicAlgCl l] AdicConstantH l X n where
  toFun x := Ext.mk₀CompMk₀ (constantIntIsoLowerStar e).hom
    (Ext.mapExactFunctor (ProEtale.lowerStar AddCommGrpCat.{u + 1} e.inv)
      (x : Sheaf.H (adicConstantSheafAb l Y) n))
    (adicConstantSheafAbLowerStarIso l e).hom
  map_add' x y := (congrArg (fun z ↦ Ext.mk₀CompMk₀ _ z _)
    (Ext.mapExactFunctor_add _ _ _ _ x y)).trans
    (Ext.mk₀CompMk₀_add _ _ _ _)
  map_smul' c x := by
    change Ext.mk₀CompMk₀ _ (Ext.mapExactFunctor _ (Ext.comp x
        (Ext.mk₀ (adicScalarRingHom l Y c).asHom) (add_zero n))) _ =
      (Ext.mk₀CompMk₀ _ (Ext.mapExactFunctor _ x) _).comp (Ext.mk₀ (adicScalarRingHom l X c).asHom)
        (add_zero n)
    rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mk₀CompMk₀_comp_mk₀_right,
      Ext.mk₀CompMk₀_comp_mk₀]
    exact congrArg _ (lowerStar_map_adicScalar_comp_adicConstantSheafAbLowerStarIso l e c)

lemma adicConstantHPullback_apply (n : ℕ) (x : AdicConstantH l Y n) :
    adicConstantHPullback l e n x = Ext.mk₀CompMk₀ (constantIntIsoLowerStar e).hom
      (Ext.mapExactFunctor (ProEtale.lowerStar AddCommGrpCat.{u + 1} e.inv)
        (x : Sheaf.H (adicConstantSheafAb l Y) n))
      (adicConstantSheafAbLowerStarIso l e).hom :=
  rfl

/-- The pullback on `Hⁿ(-, ℚ̄_ℓ)` extends the pullback on `Hⁿ(-, ℤ_ℓ)`. -/
lemma adicConstantHPullback_integralToAdicConstantH (n : ℕ) (a : IntegralAdicH Y l n) :
    adicConstantHPullback l e n (integralToAdicConstantH l Y n a) =
      integralToAdicConstantH l X n (integralAdicHPullback e l n a) := by
  have h₁ : integralToAdicConstantH l Y n a = Ext.comp (a : Sheaf.H (continuousSheaf Y ℤ_[l]) n)
      (Ext.mk₀ (continuousSheafToAdicConstantSheaf l Y)) (add_zero n) := rfl
  have h₂ : integralToAdicConstantH l X n (integralAdicHPullback e l n a) =
      Ext.comp (continuousSheafHPullback e ℤ_[l] n a)
        (Ext.mk₀ (continuousSheafToAdicConstantSheaf l X)) (add_zero n) := rfl
  rw [h₁, h₂, adicConstantHPullback_apply, continuousSheafHPullback_apply, Ext.mk₀_comp_comp_mk₀,
    Ext.mk₀CompMk₀_comp_mk₀, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.mk₀CompMk₀_comp_mk₀_right, lowerStar_map_continuousSheafToAdicConstantSheaf_comp]

end AlgebraicGeometry.ProEtale
