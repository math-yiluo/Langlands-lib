/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.CategoryTheory.ExactDerivedSquare.DerivedExactSquareCoherence
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition

/-! # Composition of compact-support coefficient restrictions

Source: Stacks Project, Tags 03DA, 0D6E and 07A6
(blueprint: lem-pur-compact-support-integral-coefficient-comparison).

Successive coefficient restrictions of the compact-support functor compose to the
restriction along the composite coefficient change. On the ordinary level all comparison
maps are identity on sections; the derived statement follows from the mate calculus and
the unit normalization of derived direct images.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

section VComp

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄} {E : Type u₅} {F : Type u₆}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  [Category.{v₅} E] [Category.{v₆} F]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C} {L₃ : E ⥤ F} {R₃ : F ⥤ E}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
  {G₁ : A ⥤ C} {G₂ : C ⥤ E} {G₁₂ : A ⥤ E} {H₁ : B ⥤ D} {H₂ : D ⥤ F} {H₁₂ : B ⥤ F}

/-- Vertical pasting of inverse mates along composite vertical functors. -/
theorem mateEquiv_symm_app_vcomp (cG : G₁ ⋙ G₂ ≅ G₁₂) (cH : H₁ ⋙ H₂ ≅ H₁₂)
    (β₁ : R₁ ⋙ G₁ ⟶ H₁ ⋙ R₂) (β₂ : R₂ ⋙ G₂ ⟶ H₂ ⋙ R₃) (β₁₂ : R₁ ⋙ G₁₂ ⟶ H₁₂ ⋙ R₃)
    (hβ : ∀ b : B, β₁₂.app b = cG.inv.app (R₁.obj b) ≫ G₂.map (β₁.app b) ≫
      β₂.app (H₁.obj b) ≫ R₃.map (cH.hom.app b)) (a : A) :
    ((mateEquiv adj₁ adj₃).symm (TwoSquare.mk _ _ _ _ β₁₂)).app a =
      L₃.map (cG.inv.app a) ≫
        ((mateEquiv adj₂ adj₃).symm (TwoSquare.mk _ _ _ _ β₂)).app (G₁.obj a) ≫
        H₂.map (((mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _ β₁)).app a) ≫
        cH.hom.app (L₁.obj a) := by
  apply (adj₃.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have h₁₂ := unit_mateEquiv_symm adj₁ adj₃ (TwoSquare.mk _ _ _ _ β₁₂) a
  have h₂ := unit_mateEquiv_symm adj₂ adj₃ (TwoSquare.mk _ _ _ _ β₂) (G₁.obj a)
  have h₁ := unit_mateEquiv_symm adj₁ adj₂ (TwoSquare.mk _ _ _ _ β₁) a
  dsimp only [TwoSquare.mk, Functor.id_obj] at h₁₂ h₂ h₁
  dsimp only [TwoSquare.mk]
  rw [← h₁₂, hβ]
  simp only [Functor.map_comp]
  rw [adj₃.unit_naturality_assoc]
  erw [← reassoc_of% h₂]
  erw [← β₂.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← G₂.map_comp_assoc]
  erw [← h₁]
  erw [cG.inv.naturality_assoc]
  simp

end VComp

section HComp

variable {CRX : Type u₁} {CSX : Type u₂} {CTX : Type u₃} {CRY : Type u₄} {CSY : Type u₅}
  {CTY : Type u₆} [Category.{v₁} CRX] [Category.{v₂} CSX] [Category.{v₃} CTX]
  [Category.{v₄} CRY] [Category.{v₅} CSY] [Category.{v₆} CTY]
  (FR : CRX ⥤ CRY) (FS : CSX ⥤ CSY) (FT : CTX ⥤ CTY)
  {EaX : CRX ⥤ CSX} {RaX : CSX ⥤ CRX} (aX : EaX ⊣ RaX)
  {EbX : CSX ⥤ CTX} {RbX : CTX ⥤ CSX} (bX : EbX ⊣ RbX)
  {EdX : CRX ⥤ CTX} {RdX : CTX ⥤ CRX} (dX : EdX ⊣ RdX)
  {EaY : CRY ⥤ CSY} {RaY : CSY ⥤ CRY} (aY : EaY ⊣ RaY)
  {EbY : CSY ⥤ CTY} {RbY : CTY ⥤ CSY} (bY : EbY ⊣ RbY)
  {EdY : CRY ⥤ CTY} {RdY : CTY ⥤ CRY} (dY : EdY ⊣ RdY)

/-- Inverse mates for composite scalar adjunctions are compatible with the induced
left-adjoint composition comparisons. -/
theorem mateEquiv_symm_app_comp_leftAdjointUniq
    (κX : RbX ⋙ RaX ≅ RdX) (κY : RbY ⋙ RaY ≅ RdY)
    (ra : RaX ⋙ FR ⟶ FS ⋙ RaY) (rb : RbX ⋙ FS ⟶ FT ⋙ RbY) (rd : RdX ⋙ FR ⟶ FT ⋙ RdY)
    (h : ∀ N : CTX, rd.app N = FR.map (κX.inv.app N) ≫ ra.app (RbX.obj N) ≫
      RaY.map (rb.app N) ≫ κY.hom.app (FT.obj N)) (M : CRX) :
    EbY.map (((mateEquiv aX aY).symm (TwoSquare.mk _ _ _ _ ra)).app M) ≫
      ((mateEquiv bX bY).symm (TwoSquare.mk _ _ _ _ rb)).app (EaX.obj M) ≫
      FT.map ((((aX.comp bX).ofNatIsoRight κX).leftAdjointUniq dX).hom.app M) =
    (((aY.comp bY).ofNatIsoRight κY).leftAdjointUniq dY).hom.app (FR.obj M) ≫
      ((mateEquiv dX dY).symm (TwoSquare.mk _ _ _ _ rd)).app M := by
  let tc := ((aX.comp bX).ofNatIsoRight κX).leftAdjointUniq dX
  have key : aX.unit.app M ≫ RaX.map (bX.unit.app (EaX.obj M) ≫ RbX.map (tc.hom.app M)) =
      dX.unit.app M ≫ κX.inv.app (EdX.obj M) := by
    have hu := Adjunction.unit_leftAdjointUniq_hom_app ((aX.comp bX).ofNatIsoRight κX) dX M
    simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
      Adjunction.comp_unit_app, Category.assoc] at hu
    rw [← hu]
    have hn := κX.hom.naturality (tc.hom.app M)
    simp only [Functor.comp_map] at hn
    simp only [Functor.map_comp, Category.assoc]
    erw [← reassoc_of% hn]
    simp
  apply (((aY.comp bY).ofNatIsoRight κY).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  conv_rhs => rw [Functor.map_comp, Adjunction.unit_leftAdjointUniq_hom_app_assoc]
  have hd := unit_mateEquiv_symm dX dY (TwoSquare.mk _ _ _ _ rd) M
  have ha := unit_mateEquiv_symm aX aY (TwoSquare.mk _ _ _ _ ra) M
  have hb := unit_mateEquiv_symm bX bY (TwoSquare.mk _ _ _ _ rb) (EaX.obj M)
  dsimp only [TwoSquare.mk, Functor.id_obj] at hd ha hb
  dsimp only [TwoSquare.mk]
  rw [← hd, h]
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Adjunction.comp_unit_app, Category.assoc]
  have hn := κY.hom.naturality (EbY.map (((mateEquiv aX aY).symm ra).app M) ≫
    ((mateEquiv bX bY).symm rb).app (EaX.obj M) ≫ FT.map (tc.hom.app M))
  simp only [Functor.comp_map] at hn
  erw [← hn]
  have inner : bY.unit.app (EaY.obj (FR.obj M)) ≫
      RbY.map (EbY.map (((mateEquiv aX aY).symm ra).app M) ≫
        ((mateEquiv bX bY).symm rb).app (EaX.obj M) ≫ FT.map (tc.hom.app M)) =
      ((mateEquiv aX aY).symm ra).app M ≫
        FS.map (bX.unit.app (EaX.obj M) ≫ RbX.map (tc.hom.app M)) ≫ rb.app (EdX.obj M) := by
    rw [Functor.map_comp, Functor.map_comp]
    erw [bY.unit_naturality_assoc, ← reassoc_of% hb]
    rw [Functor.map_comp, Category.assoc]
    congr 2
    exact (rb.naturality (tc.hom.app M)).symm
  rw [← RaY.map_comp_assoc]
  erw [inner]
  rw [RaY.map_comp, RaY.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% ha]
  erw [← ra.naturality_assoc]
  erw [← FR.map_comp_assoc, key, FR.map_comp, Category.assoc]

end HComp

end CategoryTheory

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.PurCompactSupport

variable {R S T : Coefficients.{u}} (a : Change R S) (b : Change S T) (d : Change R T)
  (h : ∀ W : Scheme.{u}, a.map W ≫ b.map W = d.map W)

attribute [local instance] proEtaleRingRestrictionPullbackInv_isIso

private theorem restrictComp_inv_val {W : Scheme.{u}}
    {R₀ S₀ T₀ : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (φ : R₀ ⟶ S₀) (ψ : S₀ ⟶ T₀) (χ : R₀ ⟶ T₀) (hχ : φ ≫ ψ = χ)
    (M : pbcModules W T₀) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcRestrictComp φ ψ χ hχ).inv.app M).val.app U x = x := by
  have hs := (pbcRestrictComp_exists φ ψ χ hχ).exists.choose_spec M U
    (((pbcRestrictComp φ ψ χ hχ).inv.app M).val.app U x)
  change ((pbcRestrictComp φ ψ χ hχ).hom.app M).val.app U
    (((pbcRestrictComp φ ψ χ hχ).inv.app M).val.app U x) = _ at hs
  rw [← hs]
  change (((pbcRestrictComp φ ψ χ hχ).inv.app M ≫
    (pbcRestrictComp φ ψ χ hχ).hom.app M).val.app U x) = x
  rw [Iso.inv_hom_id_app]
  rfl

private theorem restrictComp_hom_val {W : Scheme.{u}}
    {R₀ S₀ T₀ : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (φ : R₀ ⟶ S₀) (ψ : S₀ ⟶ T₀) (χ : R₀ ⟶ T₀) (hχ : φ ≫ ψ = χ)
    (M : pbcModules W T₀) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcRestrictComp φ ψ χ hχ).hom.app M).val.app U x = x :=
  (pbcRestrictComp_exists φ ψ χ hχ).exists.choose_spec M U x

private theorem restrictComp_inv_val' {W : Scheme.{u}}
    {R₀ S₀ T₀ : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (φ : R₀ ⟶ S₀) (ψ : S₀ ⟶ T₀) (χ : R₀ ⟶ T₀) (hχ : φ ≫ ψ = χ)
    (M : proEtaleRingModules W T₀) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcRestrictComp φ ψ χ hχ).inv.app M).val.app U x = x :=
  restrictComp_inv_val φ ψ χ hχ M U x

private theorem restrictComp_hom_val' {W : Scheme.{u}}
    {R₀ S₀ T₀ : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (φ : R₀ ⟶ S₀) (ψ : S₀ ⟶ T₀) (χ : R₀ ⟶ T₀) (hχ : φ ≫ ψ = χ)
    (M : proEtaleRingModules W T₀) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcRestrictComp φ ψ χ hχ).hom.app M).val.app U x = x :=
  restrictComp_hom_val φ ψ χ hχ M U x

private theorem restrictionDirectImage_val {U V : Scheme.{u}} (g : U ⟶ V)
    (RV SV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RU SU : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (aV : RV ⟶ SV) (aU : RU ⟶ SU)
    (cR : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj RV ≅ RU)
    (cS : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj SV ≅ SU)
    (comm : cR.hom ≫ aU = (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map aV ≫ cS.hom)
    (N : proEtaleRingModules U SU) (W : V.ProEtᵒᵖ)
    (n : N.val.obj ((proEtaleBaseChange g).op.obj W)) :
    ((proEtaleRingRestrictionDirectImage g RV SV RU SU aV aU cR cS comm).hom.app N).val.app W n =
      n :=
  (Classical.choose_spec (proEtaleRingRestrictionDirectImage_existsUnique
    g RV SV RU SU aV aU cR cS comm)).1 N W n

/-- Ordinary restriction/direct-image comparisons compose, since all are identity on sections. -/
theorem restrictionDirectImage_comp {U V : Scheme.{u}} (g : U ⟶ V)
    (N : pbcModules U (T.ring U)) :
    (proEtaleRingRestrictionDirectImage g (R.ring V) (T.ring V) (R.ring U) (T.ring U)
        (d.map V) (d.map U) (R.pull g) (T.pull g) (d.square g)).hom.app N =
      (pbcRestrictComp (a.map V) (b.map V) (d.map V) (h V)).inv.app
          ((proEtaleRingModuleDirectImage g (T.ring V) (T.ring U) (T.pull g)).obj N) ≫
        (pbcRestrict (a.map V)).map
          ((proEtaleRingRestrictionDirectImage g (S.ring V) (T.ring V) (S.ring U) (T.ring U)
            (b.map V) (b.map U) (S.pull g) (T.pull g) (b.square g)).hom.app N) ≫
        (proEtaleRingRestrictionDirectImage g (R.ring V) (S.ring V) (R.ring U) (S.ring U)
            (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)).hom.app
          ((pbcRestrict (b.map U)).obj N) ≫
        (proEtaleRingModuleDirectImage g (R.ring V) (R.ring U) (R.pull g)).map
          ((pbcRestrictComp (a.map U) (b.map U) (d.map U) (h U)).hom.app N) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext n
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  rw [restrictionDirectImage_val]
  have e1 := restrictComp_inv_val' (a.map V) (b.map V) (d.map V) (h V)
    ((proEtaleRingModuleDirectImage g (T.ring V) (T.ring U) (T.pull g)).obj N) W n
  have e2 := restrictionDirectImage_val g (S.ring V) (T.ring V) (S.ring U) (T.ring U)
    (b.map V) (b.map U) (S.pull g) (T.pull g) (b.square g) N W n
  have e3 := restrictionDirectImage_val g (R.ring V) (S.ring V) (R.ring U) (S.ring U)
    (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g) ((pbcRestrict (b.map U)).obj N) W n
  have e4 := restrictComp_hom_val' (a.map U) (b.map U) (d.map U) (h U) N _ n
  exact e4.symm.trans (congrArg _ (e3.symm.trans (congrArg _ (e2.symm.trans
    (congrArg _ e1.symm)))))
private theorem pullbackInv_eq_mate {U V : Scheme.{u}} (g : U ⟶ V)
    (RV SV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RU SU : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (aV : RV ⟶ SV) (aU : RU ⟶ SU)
    (cR : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj RV ≅ RU)
    (cS : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj SV ≅ SU)
    (comm : cR.hom ≫ aU = (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map aV ≫ cS.hom) :
    proEtaleRingRestrictionPullbackInv g RV SV RU SU aV aU cR cS comm =
      ((mateEquiv (proEtaleRingModuleAdjunction g SV SU cS)
        (proEtaleRingModuleAdjunction g RV RU cR)).symm
          (TwoSquare.mk _ _ _ _
            (proEtaleRingRestrictionDirectImage g RV SV RU SU aV aU cR cS comm).hom)) := by
  ext M : 2
  simp only [mateEquiv_symm_apply, TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_obj, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Category.id_comp]
  dsimp only [Functor.comp_map]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- Ordinary inverse-image coefficient comparisons compose. -/
theorem pullbackInv_comp {U V : Scheme.{u}} (g : U ⟶ V) (x : pbcModules V (T.ring V)) :
    (proEtaleRingRestrictionPullbackInv g (R.ring V) (T.ring V) (R.ring U) (T.ring U)
        (d.map V) (d.map U) (R.pull g) (T.pull g) (d.square g)).app x =
      (proEtaleRingModulePullback g (R.ring V) (R.ring U) (R.pull g)).map
          ((pbcRestrictComp (a.map V) (b.map V) (d.map V) (h V)).inv.app x) ≫
        (proEtaleRingRestrictionPullbackInv g (R.ring V) (S.ring V) (R.ring U) (S.ring U)
          (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)).app
            ((pbcRestrict (b.map V)).obj x) ≫
        (pbcRestrict (a.map U)).map
          ((proEtaleRingRestrictionPullbackInv g (S.ring V) (T.ring V) (S.ring U) (T.ring U)
            (b.map V) (b.map U) (S.pull g) (T.pull g) (b.square g)).app x) ≫
        (pbcRestrictComp (a.map U) (b.map U) (d.map U) (h U)).hom.app
          ((proEtaleRingModulePullback g (T.ring V) (T.ring U) (T.pull g)).obj x) := by
  rw [pullbackInv_eq_mate, pullbackInv_eq_mate, pullbackInv_eq_mate]
  exact CategoryTheory.mateEquiv_symm_app_vcomp
    (proEtaleRingModuleAdjunction g (T.ring V) (T.ring U) (T.pull g))
    (proEtaleRingModuleAdjunction g (S.ring V) (S.ring U) (S.pull g))
    (proEtaleRingModuleAdjunction g (R.ring V) (R.ring U) (R.pull g))
    (pbcRestrictComp (a.map V) (b.map V) (d.map V) (h V))
    (pbcRestrictComp (a.map U) (b.map U) (d.map U) (h U))
    _ _ _ (fun y ↦ restrictionDirectImage_comp a b d h g y) x

/-- The inverse ordinary inverse-image comparisons compose. -/
theorem pullbackInv_inv_comp {U V : Scheme.{u}} (g : U ⟶ V) (x : pbcModules V (T.ring V)) :
    inv ((proEtaleRingRestrictionPullbackInv g (R.ring V) (T.ring V) (R.ring U) (T.ring U)
        (d.map V) (d.map U) (R.pull g) (T.pull g) (d.square g)).app x) =
      (pbcRestrictComp (a.map U) (b.map U) (d.map U) (h U)).inv.app
          ((proEtaleRingModulePullback g (T.ring V) (T.ring U) (T.pull g)).obj x) ≫
        (pbcRestrict (a.map U)).map
          (inv ((proEtaleRingRestrictionPullbackInv g (S.ring V) (T.ring V) (S.ring U) (T.ring U)
            (b.map V) (b.map U) (S.pull g) (T.pull g) (b.square g)).app x)) ≫
        inv ((proEtaleRingRestrictionPullbackInv g (R.ring V) (S.ring V) (R.ring U) (S.ring U)
          (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)).app
            ((pbcRestrict (b.map V)).obj x)) ≫
        (proEtaleRingModulePullback g (R.ring V) (R.ring U) (R.pull g)).map
          ((pbcRestrictComp (a.map V) (b.map V) (d.map V) (h V)).hom.app x) := by
  apply IsIso.inv_eq_of_hom_inv_id
  rw [pullbackInv_comp a b d h g x]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp_assoc (pbcRestrict (a.map U)), IsIso.hom_inv_id]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, IsIso.hom_inv_id_assoc]
  rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  rfl

/-- The ordinary open coefficient comparisons compose. -/
theorem openRestrictionMap_comp {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]
    (x : pbcModules U (T.ring U)) :
    (openRestrictionMap d j).app x =
      (openExtension R j).map ((pbcRestrictComp (a.map U) (b.map U) (d.map U) (h U)).inv.app x) ≫
        (openRestrictionMap a j).app ((pbcRestrict (b.map U)).obj x) ≫
        (pbcRestrict (a.map V)).map ((openRestrictionMap b j).app x) ≫
        (pbcRestrictComp (a.map V) (b.map V) (d.map V) (h V)).hom.app
          ((openExtension T j).obj x) := by
  have := proEtaleRingRestrictionPullbackInv_isIso
    j (R.ring V) (S.ring V) (R.ring U) (S.ring U)
      (a.map V) (a.map U) (R.pull j) (S.pull j) (a.square j)
  have := proEtaleRingRestrictionPullbackInv_isIso
    j (S.ring V) (T.ring V) (S.ring U) (T.ring U)
      (b.map V) (b.map U) (S.pull j) (T.pull j) (b.square j)
  have := proEtaleRingRestrictionPullbackInv_isIso
    j (R.ring V) (T.ring V) (R.ring U) (T.ring U)
      (d.map V) (d.map U) (R.pull j) (T.pull j) (d.square j)
  unfold openRestrictionMap
  refine CategoryTheory.mateEquiv_symm_app_vcomp (openAdjunction T j) (openAdjunction S j)
    (openAdjunction R j) (pbcRestrictComp (a.map U) (b.map U) (d.map U) (h U))
    (pbcRestrictComp (a.map V) (b.map V) (d.map V) (h V)) _ _ _ (fun y ↦ ?_) x
  simp only [NatIso.isIso_inv_app]
  exact pullbackInv_inv_comp a b d h j y

private theorem derivedRestrictComp_symm {W : Scheme.{u}}
    {R₀ S₀ T₀ : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (φ : R₀ ⟶ S₀) (ψ : S₀ ⟶ T₀) (χ : R₀ ⟶ T₀) (hχ : φ ≫ ψ = χ) :
    Functor.mapDerivedCategoryNatIso (pbcRestrictComp φ ψ χ hχ).symm ≪≫
        (Functor.mapDerivedCategoryCompIso (pbcRestrict ψ) (pbcRestrict φ)).symm =
      (pbcDerivedRestrictComp φ ψ χ hχ).symm := by
  apply Iso.ext
  rw [Iso.trans_hom, Functor.mapDerivedCategoryNatIso_symm]
  rfl

/-- The exact derived open coefficient comparisons compose. -/
theorem openRestriction_comp {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]
    (N : DerivedCategory (pbcModules U (T.ring U))) :
    (openRestriction d j).hom.app N =
      (openExtension R j).mapDerivedCategory.map
          ((pbcDerivedRestrictComp (a.map U) (b.map U) (d.map U) (h U)).inv.app N) ≫
        (openRestriction a j).hom.app ((pbcDerivedRestrict (b.map U)).obj N) ≫
        (pbcDerivedRestrict (a.map V)).map ((openRestriction b j).hom.app N) ≫
        (pbcDerivedRestrictComp (a.map V) (b.map V) (d.map V) (h V)).hom.app
          ((openExtension T j).mapDerivedCategory.obj N) := by
  have hq : ∀ x : pbcModules U (T.ring U),
      (openExtension R j).map
          ((pbcRestrictComp (a.map U) (b.map U) (d.map U) (h U)).symm.hom.app x) ≫
        (asIso (openRestrictionMap a j)).hom.app ((pbcRestrict (b.map U)).obj x) ≫
        (pbcRestrict (a.map V)).map ((asIso (openRestrictionMap b j)).hom.app x) =
      (asIso (openRestrictionMap d j)).hom.app x ≫
        (pbcRestrictComp (a.map V) (b.map V) (d.map V) (h V)).symm.hom.app
          ((openExtension T j).obj x) := by
    intro x
    simp only [asIso_hom, Iso.symm_hom]
    rw [openRestrictionMap_comp a b d h j x]
    simp
  have hc := Functor.exactSquare_comp_forward
    (pbcRestrict (b.map U)) (pbcRestrict (a.map U)) (pbcRestrict (d.map U))
    (pbcRestrict (b.map V)) (pbcRestrict (a.map V)) (pbcRestrict (d.map V))
    (openExtension T j) (openExtension S j) (openExtension R j)
    (asIso (openRestrictionMap b j)) (asIso (openRestrictionMap a j))
    (asIso (openRestrictionMap d j))
    (pbcRestrictComp (a.map U) (b.map U) (d.map U) (h U)).symm
    (pbcRestrictComp (a.map V) (b.map V) (d.map V) (h V)).symm hq N
  rw [derivedRestrictComp_symm, derivedRestrictComp_symm] at hc
  unfold openRestriction
  erw [reassoc_of% hc]
  simp only [Iso.symm_hom, Iso.inv_hom_id_app, Category.comp_id]
private theorem derivedDirectImage_normalized {U V : Scheme.{u}} (g : U ⟶ V)
    (RV SV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RU SU : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (aV : RV ⟶ SV) (aU : RU ⟶ SU)
    (cR : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj RV ≅ RU)
    (cS : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj SV ≅ SU)
    (comm : cR.hom ≫ aU = (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map aV ≫ cS.hom) :
    CategoryTheory.ExactDerivedSquare.unitNormalized
      (proEtaleRingModuleDirectImage g SV SU cS) (proEtaleRingModuleDirectImage g RV RU cR)
      (pbcRestrict aU) (pbcRestrict aV)
      (pbcRestrict aU).mapDerivedCategory (pbcRestrict aV).mapDerivedCategory
      (pbcRestrict aU).mapDerivedCategoryFactors (pbcRestrict aV).mapDerivedCategoryFactors
      (proEtaleRingRestrictionDirectImage g RV SV RU SU aV aU cR cS comm).hom
      (proEtaleRingRestrictionDerivedDirectImage g RV SV RU SU aV aU cR cS comm).hom := by
  intro C
  exact (proEtaleRingRestrictionDerivedDirectImage_existsUnique
    g RV SV RU SU aV aU cR cS comm).choose_spec.1 C

private theorem derivedRestrictComp_factors {W : Scheme.{u}}
    {R₀ S₀ T₀ : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (φ : R₀ ⟶ S₀) (ψ : S₀ ⟶ T₀) (χ : R₀ ⟶ T₀) (hχ : φ ≫ ψ = χ)
    (I : CochainComplex (pbcModules W T₀) ℤ) :
    (pbcDerivedRestrictComp φ ψ χ hχ).hom.app (DerivedCategory.Q.obj I) ≫
        (pbcRestrict χ).mapDerivedCategoryFactors.hom.app I =
      ((Functor.isoWhiskerRight (pbcRestrict ψ).mapDerivedCategoryFactors
          (pbcRestrict φ).mapDerivedCategory ≪≫
        Functor.isoWhiskerLeft ((pbcRestrict ψ).mapHomologicalComplex (.up ℤ))
          (pbcRestrict φ).mapDerivedCategoryFactors).hom.app I) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (pbcRestrictComp φ ψ χ hχ).hom (.up ℤ)).app I) := by
  have hf := Functor.mapDerivedCategoryCompIso_hom_app_factors
    (pbcRestrict ψ) (pbcRestrict φ) I
  simp only [pbcDerivedRestrictComp, Iso.trans_hom, NatTrans.comp_app,
    Category.assoc, Functor.mapDerivedCategoryNatIso_fac, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [← hf]
  simp

/-- The derived restriction/direct-image comparisons compose. -/
theorem derivedDirectImage_comp {U V : Scheme.{u}} (g : U ⟶ V)
    (K : DerivedCategory (pbcModules U (T.ring U))) :
    (pbcDerivedRestrictComp (a.map V) (b.map V) (d.map V) (h V)).hom.app
        ((proEtaleRingDerivedDirectImage g (T.ring V) (T.ring U) (T.pull g)).obj K) ≫
      (proEtaleRingRestrictionDerivedDirectImage g (R.ring V) (T.ring V) (R.ring U) (T.ring U)
        (d.map V) (d.map U) (R.pull g) (T.pull g) (d.square g)).hom.app K =
    (pbcDerivedRestrict (a.map V)).map
        ((proEtaleRingRestrictionDerivedDirectImage g (S.ring V) (T.ring V) (S.ring U) (T.ring U)
          (b.map V) (b.map U) (S.pull g) (T.pull g) (b.square g)).hom.app K) ≫
      (proEtaleRingRestrictionDerivedDirectImage g (R.ring V) (S.ring V) (R.ring U) (S.ring U)
        (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)).hom.app
          ((pbcDerivedRestrict (b.map U)).obj K) ≫
      (proEtaleRingDerivedDirectImage g (R.ring V) (R.ring U) (R.pull g)).map
        ((pbcDerivedRestrictComp (a.map U) (b.map U) (d.map U) (h U)).hom.app K) := by
  have hn := CategoryTheory.ExactDerivedSquare.normalized_comp
    (proEtaleRingModuleDirectImage g (T.ring V) (T.ring U) (T.pull g))
    (proEtaleRingModuleDirectImage g (S.ring V) (S.ring U) (S.pull g))
    (pbcRestrict (b.map U)) (pbcRestrict (b.map V))
    (proEtaleRingModuleDirectImage g (R.ring V) (R.ring U) (R.pull g))
    (pbcRestrict (a.map U)) (pbcRestrict (a.map V))
    (proEtaleRingRestrictionDirectImage g (S.ring V) (T.ring V) (S.ring U) (T.ring U)
      (b.map V) (b.map U) (S.pull g) (T.pull g) (b.square g))
    (proEtaleRingRestrictionDirectImage g (R.ring V) (S.ring V) (R.ring U) (S.ring U)
      (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g))
    (proEtaleRingRestrictionDerivedDirectImage g (S.ring V) (T.ring V) (S.ring U) (T.ring U)
      (b.map V) (b.map U) (S.pull g) (T.pull g) (b.square g))
    (proEtaleRingRestrictionDerivedDirectImage g (R.ring V) (S.ring V) (R.ring U) (S.ring U)
      (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g))
    (derivedDirectImage_normalized g _ _ _ _ _ _ _ _ _)
    (derivedDirectImage_normalized g _ _ _ _ _ _ _ _ _)
  have hn' := derivedDirectImage_normalized g (R.ring V) (T.ring V) (R.ring U) (T.ring U)
    (d.map V) (d.map U) (R.pull g) (T.pull g) (d.square g)
  have h2 := CategoryTheory.ExactDerivedSquare.normalized_naturality
    (proEtaleRingModuleDirectImage g (T.ring V) (T.ring U) (T.pull g))
    (proEtaleRingModuleDirectImage g (R.ring V) (R.ring U) (R.pull g))
    (pbcRestrict (b.map U) ⋙ pbcRestrict (a.map U))
    (pbcRestrict (b.map V) ⋙ pbcRestrict (a.map V))
    (pbcRestrict (d.map U)) (pbcRestrict (d.map V)) _ _ _ _ _ _ _ _ _ _ _ _ hn hn'
    (pbcRestrictComp (a.map U) (b.map U) (d.map U) (h U)).hom
    (pbcRestrictComp (a.map V) (b.map V) (d.map V) (h V)).hom
    (pbcDerivedRestrictComp (a.map U) (b.map U) (d.map U) (h U)).hom
    (pbcDerivedRestrictComp (a.map V) (b.map V) (d.map V) (h V)).hom
    (derivedRestrictComp_factors _ _ _ _) (derivedRestrictComp_factors _ _ _ _) (fun M ↦ by
      rw [restrictionDirectImage_comp a b d h g M]
      simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Category.assoc, Iso.hom_inv_id_app_assoc])
  have hK := NatTrans.congr_app h2 K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc] at hK
  exact hK
/-- Compact-support coefficient restrictions compose. -/
theorem restriction_comp {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (N : DerivedCategory (pbcModules X (T.ring X))) :
    (restriction d c).hom.app N =
      (image R c).map ((pbcDerivedRestrictComp (a.map X) (b.map X) (d.map X) (h X)).inv.app N) ≫
        (restriction a c).hom.app ((pbcDerivedRestrict (b.map X)).obj N) ≫
        (pbcDerivedRestrict (a.map Y)).map ((restriction b c).hom.app N) ≫
        (pbcDerivedRestrictComp (a.map Y) (b.map Y) (d.map Y) (h Y)).hom.app
          ((image T c).obj N) := by
  have hP (K : DerivedCategory (pbcModules c.Z (T.ring c.Z))) :
      (proEtaleRingRestrictionDerivedDirectImage c.g (R.ring Y) (T.ring Y) (R.ring c.Z)
          (T.ring c.Z) (d.map Y) (d.map c.Z) (R.pull c.g) (T.pull c.g) (d.square c.g)).inv.app K =
        (proEtaleRingDerivedDirectImage c.g (R.ring Y) (R.ring c.Z) (R.pull c.g)).map
            ((pbcDerivedRestrictComp (a.map c.Z) (b.map c.Z) (d.map c.Z) (h c.Z)).inv.app K) ≫
          (proEtaleRingRestrictionDerivedDirectImage c.g (R.ring Y) (S.ring Y) (R.ring c.Z)
            (S.ring c.Z) (a.map Y) (a.map c.Z) (R.pull c.g) (S.pull c.g) (a.square c.g)).inv.app
              ((pbcDerivedRestrict (b.map c.Z)).obj K) ≫
          (pbcDerivedRestrict (a.map Y)).map
            ((proEtaleRingRestrictionDerivedDirectImage c.g (S.ring Y) (T.ring Y) (S.ring c.Z)
              (T.ring c.Z) (b.map Y) (b.map c.Z) (S.pull c.g) (T.pull c.g)
              (b.square c.g)).inv.app K) ≫
          (pbcDerivedRestrictComp (a.map Y) (b.map Y) (d.map Y) (h Y)).hom.app
            ((proEtaleRingDerivedDirectImage c.g (T.ring Y) (T.ring c.Z) (T.pull c.g)).obj K) := by
    have e := derivedDirectImage_comp a b d h c.g K
    rw [← Iso.app_inv]
    apply Iso.inv_ext
    rw [Iso.app_hom, ← cancel_epi ((pbcDerivedRestrictComp (a.map Y) (b.map Y) (d.map Y)
      (h Y)).hom.app ((proEtaleRingDerivedDirectImage c.g (T.ring Y) (T.ring c.Z)
        (T.pull c.g)).obj K)), reassoc_of% e]
    erw [Category.comp_id]
    erw [← Functor.map_comp_assoc (proEtaleRingDerivedDirectImage c.g (R.ring Y) (R.ring c.Z)
      (R.pull c.g)), Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
      Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hcancel : (proEtaleRingDerivedDirectImage c.g (R.ring Y) (R.ring c.Z) (R.pull c.g)).map
        ((pbcDerivedRestrictComp (a.map c.Z) (b.map c.Z) (d.map c.Z) (h c.Z)).hom.app
          ((openExtension T c.i).mapDerivedCategory.obj N)) ≫
      (proEtaleRingDerivedDirectImage c.g (R.ring Y) (R.ring c.Z) (R.pull c.g)).map
        ((pbcDerivedRestrictComp (a.map c.Z) (b.map c.Z) (d.map c.Z) (h c.Z)).inv.app
          ((openExtension T c.i).mapDerivedCategory.obj N)) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  simp only [restriction, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  rw [openRestriction_comp a b d h c.i N, hP]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hcancel]
  erw [(proEtaleRingRestrictionDerivedDirectImage c.g (R.ring Y) (S.ring Y) (R.ring c.Z)
    (S.ring c.Z) (a.map Y) (a.map c.Z) (R.pull c.g) (S.pull c.g)
    (a.square c.g)).inv.naturality_assoc]
  rfl

end WeilConjectures.PurCompactSupport
