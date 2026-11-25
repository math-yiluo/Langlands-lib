/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Isotypic
public import WeilConjectures.WeilSheaf.LowerStarComp
public import WeilConjectures.WeilSheaf.StalkConstantSheaf
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunctionWeil
public import WeilConjectures.WeilSheaf.UpperStarConstant

/-!
# Pullbacks of isotypic components along morphisms of torsors

Let `π₁ : W₁ ⟶ Z₁` and `π : W ⟶ X` be torsors (under `G₁` and `G`) and `(h, s)` a morphism of
torsors: `s ≫ π₁ = π ≫ h`, with `τ_g ≫ s = s ≫ τ₁_{c(g)}` for a map `c : G → G₁`. A morphism
of pro-étale Weil sheaves `ι : N ⟶ π₁_* ℚ̄_ℓ` on which `G₁` acts through a character `χ`, whose
adjoint `π₁^* N ⟶ ℚ̄_ℓ` is an isomorphism, induces a morphism `h^* N ⟶ π_* ℚ̄_ℓ` on which `G` acts
through `χ ∘ c` and whose adjoint `π^* h^* N ⟶ ℚ̄_ℓ` is an isomorphism
(`AlgebraicGeometry.ProEtaleWeilSheaf.isotypicPullback`): the adjoint of
`N ⟶ π₁_* ℚ̄_ℓ ⟶ π₁_* s_* ℚ̄_ℓ ≅ h_* π_* ℚ̄_ℓ`.

Applied to the Artin–Schreier covering of the affine line and the Artin–Schreier coverings of
the plane, this describes the Artin–Schreier sheaves `ℒ_{ψ,f}` of functions as isotypic
components (blueprint `lemma-artin-schreier-character-sheaf`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory
open scoped Obj

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {X W Z₁ W₁ : Scheme.{u}} (π : W ⟶ X) (π₁ : W₁ ⟶ Z₁)
  (h : X ⟶ Z₁) (s : W ⟶ W₁) (hs : s ≫ π₁ = π ≫ h) {G G₁ : Type u}
  (τ : G → (W ≅ W)) (hτ : ∀ g, (τ g).hom ≫ π = π)
  (τ₁ : G₁ → (W₁ ≅ W₁)) (hτ₁ : ∀ g, (τ₁ g).hom ≫ π₁ = π₁)

/-- Pulling back functions along a morphism of torsors intertwines the translations. -/
lemma lowerStar_map_adicConstantSheafToLowerStar_comp_torsorTranslation (g : G) (g₁ : G₁)
    (hτs : (τ g).hom ≫ s = s ≫ (τ₁ g₁).hom) :
    (π₁)_*[WeilCoefficients.{u} l].map (adicConstantSheafToLowerStar l s) ≫
      (lowerStarComp (WeilCoefficients.{u} l) s π₁).hom.app _ ≫
      (lowerStarCongr (WeilCoefficients.{u} l) hs).hom.app _ ≫
      (lowerStarComp (WeilCoefficients.{u} l) π h).inv.app _ ≫
      (h)_*[WeilCoefficients.{u} l].map (torsorTranslation l π τ hτ g).hom =
    (torsorTranslation l π₁ τ₁ hτ₁ g₁).hom ≫
      (π₁)_*[WeilCoefficients.{u} l].map (adicConstantSheafToLowerStar l s) ≫
      (lowerStarComp (WeilCoefficients.{u} l) s π₁).hom.app _ ≫
      (lowerStarCongr (WeilCoefficients.{u} l) hs).hom.app _ ≫
      (lowerStarComp (WeilCoefficients.{u} l) π h).inv.app _ := by
  ext ⟨U⟩ : 3
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    lowerStar_map_hom_app', lowerStarComp_hom_app_hom_app, lowerStarCongr_hom_app_hom_app,
    lowerStarComp_inv_app_hom_app, torsorTranslation_hom_app, adicConstantSheafToLowerStar_hom_app,
    adicConstantSheaf_obj_map]
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  apply pullback.hom_ext
  · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullbackComp,
      MorphismProperty.Over.pullback, MorphismProperty.Over.mk]
  · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullbackComp,
      MorphismProperty.Over.pullback, MorphismProperty.Over.mk, hτs]

/-- Pulling back functions along `s` commutes with pulling back along automorphisms `e_W`,
`e_{W₁}` with `s ≫ e_{W₁} = e_W ≫ s`. -/
lemma adicConstantSheafToLowerStar_lowerStarExchange (eW : W ⟶ W) (eW₁ : W₁ ⟶ W₁)
    (hc : s ≫ eW₁ = eW ≫ s) :
    adicConstantSheafToLowerStar l eW₁ ≫
      (eW₁)_*[WeilCoefficients.{u} l].map (adicConstantSheafToLowerStar l s) ≫
      (lowerStarComp (WeilCoefficients.{u} l) s eW₁).hom.app _ ≫
      (lowerStarCongr (WeilCoefficients.{u} l) hc).hom.app _ ≫
      (lowerStarComp (WeilCoefficients.{u} l) eW s).inv.app _ =
    adicConstantSheafToLowerStar l s ≫
      (s)_*[WeilCoefficients.{u} l].map (adicConstantSheafToLowerStar l eW) := by
  ext ⟨U⟩ : 3
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    lowerStar_map_hom_app', lowerStarComp_hom_app_hom_app, lowerStarCongr_hom_app_hom_app,
    lowerStarComp_inv_app_hom_app, adicConstantSheafToLowerStar_hom_app,
    adicConstantSheaf_obj_map]
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullbackComp,
      MorphismProperty.Over.pullback, MorphismProperty.Over.mk]

/-- The pullback of functions along `s` is compatible with the structure isomorphisms
`(e_W⁻¹)_* ℚ̄_ℓ ≅ ℚ̄_ℓ` and `(e_{W₁}⁻¹)_* ℚ̄_ℓ ≅ ℚ̄_ℓ` for automorphisms with
`s ≫ e_{W₁}⁻¹ = e_W⁻¹ ≫ s` (the form of the Weil structures of pushforwards). -/
lemma adicConstantSheafToLowerStar_lowerStarExchange_iso (eW : W ≅ W) (eW₁ : W₁ ≅ W₁)
    (hc : s ≫ eW₁.inv = eW.inv ≫ s) :
    (eW₁.inv)_*[WeilCoefficients.{u} l].map (adicConstantSheafToLowerStar l s) ≫
      (lowerStarComp (WeilCoefficients.{u} l) s eW₁.inv).hom.app _ ≫
      (lowerStarCongr (WeilCoefficients.{u} l) hc).hom.app _ ≫
      (lowerStarComp (WeilCoefficients.{u} l) eW.inv s).inv.app _ ≫
      (s)_*[WeilCoefficients.{u} l].map (adicConstantSheafLowerStarIso l eW.symm).hom =
    (adicConstantSheafLowerStarIso l eW₁.symm).hom ≫ adicConstantSheafToLowerStar l s := by
  have h := adicConstantSheafToLowerStar_lowerStarExchange (l := l) s eW.inv eW₁.inv hc
  rw [← Iso.inv_comp_eq]
  change adicConstantSheafToLowerStar l eW₁.inv ≫ _ = _
  simp only [← Category.assoc] at h ⊢
  rw [h, Category.assoc, ← CategoryTheory.Functor.map_comp]
  change _ ≫ (s)_*[WeilCoefficients.{u} l].map
    ((adicConstantSheafLowerStarIso l eW.symm).inv ≫
      (adicConstantSheafLowerStarIso l eW.symm).hom) =
      _
  rw [Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]

variable (l) in
/-- The morphism `ℚ̄_ℓ ⟶ s_* ℚ̄_ℓ` of sheaves of `ℚ̄_ℓ`-modules pulling back functions along
`s`. -/
noncomputable def adicUnitToLowerStar :
    AdicSheaf.unit l W₁ ⟶ (s)_*ᵃ[l].obj (AdicSheaf.unit l W) :=
  Mod.homMk (adicConstantSheafToLowerStar l s) (by
    change MonObj.mul ≫ adicConstantSheafToLowerStar l s = _ ◁ adicConstantSheafToLowerStar l s ≫
      adicConstantSheafToLowerStar l s ▷ _ ≫ MonObj.mul
    rw [IsMonHom.mul_hom, tensorHom_def', Category.assoc])

/-- The underlying sheaf morphism of `AlgebraicGeometry.ProEtale.adicUnitToLowerStar`
(blueprint `lemma-artin-schreier-character-sheaf`). -/
@[simp]
lemma adicUnitToLowerStar_hom :
    (adicUnitToLowerStar l s).hom = adicConstantSheafToLowerStar l s :=
  rfl

/-- The adjoint `s^* ℚ̄_ℓ ⟶ ℚ̄_ℓ` of the unit `ℚ̄_ℓ ⟶ s_* ℚ̄_ℓ` is invertible
(blueprint `lemma-artin-schreier-character-sheaf`). -/
instance : IsIso ((adicUpperStarLowerStarAdjunction l s).homEquiv _ _ |>.symm
    (adicUnitToLowerStar l s)) := by
  have : IsIso ((adicUpperStarLowerStarAdjunction l s).homEquiv _ _ |>.symm
      (adicUnitToLowerStar l s)).hom := by
    rw [Adjunction.homEquiv_counit, Mod.comp_hom', adicUpperStar_map_hom,
      adicUpperStarLowerStarAdjunction_counit_app_hom_eq]
    have : IsIso (((upperStarLowerStarAdjunction (WeilCoefficients.{u} l) s).homEquiv
        (adicConstantSheaf l W₁) (adicConstantSheaf l W)).symm
          (adicConstantSheafToLowerStar l s)) := inferInstance
    rwa [Adjunction.homEquiv_counit] at this
  have : IsIso ((Mod.forget _).map ((adicUpperStarLowerStarAdjunction l s).homEquiv _ _ |>.symm
      (adicUnitToLowerStar l s))) := this
  exact isIso_of_reflects_iso _ (Mod.forget _)

/-- Composition of congruence isomorphisms of pushforwards. -/
@[reassoc]
lemma lowerStarCongr_hom_app_comp_lowerStarCongr_hom_app {Y₁ Y₂ : Scheme.{u}}
    {f₁ f₂ f₃ : Y₁ ⟶ Y₂} (h₁ : f₁ = f₂) (h₂ : f₂ = f₃) (M) :
    (lowerStarCongr (WeilCoefficients.{u} l) h₁).hom.app M ≫
      (lowerStarCongr (WeilCoefficients.{u} l) h₂).hom.app M =
    (lowerStarCongr (WeilCoefficients.{u} l) (h₁.trans h₂)).hom.app M := by
  subst h₁ h₂
  simp

/-- The inverse of a congruence isomorphism of pushforwards. -/
lemma lowerStarCongr_inv_app_eq {Y₁ Y₂ : Scheme.{u}} {f₁ f₂ : Y₁ ⟶ Y₂} (h₁ : f₁ = f₂) (M) :
    (lowerStarCongr (WeilCoefficients.{u} l) h₁).inv.app M =
      (lowerStarCongr (WeilCoefficients.{u} l) h₁.symm).hom.app M := by
  subst h₁
  simp

/-- `lowerStar_map_adicConstantSheafToLowerStar_comp_torsorTranslation` with the constant sheaf
written as the underlying sheaf of `AdicSheaf.unit`. -/
lemma lowerStar_map_adicConstantSheafToLowerStar_comp_torsorTranslation_unit
    (hs : s ≫ π₁ = π ≫ h) (g : G) (g₁ : G₁)
    (hτs : (τ g).hom ≫ s = s ≫ (τ₁ g₁).hom) :
    (π₁)_*[WeilCoefficients.{u} l].map (adicConstantSheafToLowerStar l s) ≫
      (lowerStarComp (WeilCoefficients.{u} l) s π₁).hom.app (AdicSheaf.unit l W).X ≫
      (lowerStarCongr (WeilCoefficients.{u} l) hs).hom.app (AdicSheaf.unit l W).X ≫
      (lowerStarComp (WeilCoefficients.{u} l) π h).inv.app (AdicSheaf.unit l W).X ≫
      (h)_*[WeilCoefficients.{u} l].map (torsorTranslation l π τ hτ g).hom =
    (torsorTranslation l π₁ τ₁ hτ₁ g₁).hom ≫
      (π₁)_*[WeilCoefficients.{u} l].map (adicConstantSheafToLowerStar l s) ≫
      (lowerStarComp (WeilCoefficients.{u} l) s π₁).hom.app (AdicSheaf.unit l W).X ≫
      (lowerStarCongr (WeilCoefficients.{u} l) hs).hom.app (AdicSheaf.unit l W).X ≫
      (lowerStarComp (WeilCoefficients.{u} l) π h).inv.app (AdicSheaf.unit l W).X := by
  have hW : ∀ {U V : W.ProEtᵒᵖ} (f : U ⟶ V),
      (AdicSheaf.unit l W).X.obj.map f = (adicFunctionsPresheaf l).map f.unop.left.op :=
    fun _ ↦ rfl
  ext ⟨U⟩ : 3
  simp only [hW, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    lowerStar_map_hom_app', lowerStarComp_hom_app_hom_app, lowerStarCongr_hom_app_hom_app,
    lowerStarComp_inv_app_hom_app, torsorTranslation_hom_app,
    adicConstantSheafToLowerStar_hom_app]
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  apply pullback.hom_ext
  · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullbackComp,
      MorphismProperty.Over.pullback, MorphismProperty.Over.mk]
  · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullbackComp,
      MorphismProperty.Over.pullback, MorphismProperty.Over.mk, hτs]

/-- `ProEtale.lowerStar_map_adicConstantSheafToLowerStar_comp_torsorTranslation` for sheaves of
modules, with the isomorphism `π₁_* s_* ≅ h_* π_*` written through an intermediate morphism. -/
lemma adicLowerStar_map_adicUnitToLowerStar_comp_torsorTranslation {m m' : W ⟶ Z₁}
    (e₁ : s ≫ π₁ = m) (e₂ : m = m') (e₃ : π ≫ h = m') (g : G) (g₁ : G₁)
    (hτs : (τ g).hom ≫ s = s ≫ (τ₁ g₁).hom) :
    (π₁)_*ᵃ[l].map (adicUnitToLowerStar l s) ≫
      (adicLowerStarComp l s π₁).hom.app (AdicSheaf.unit l W) ≫
      (adicLowerStarCongr l e₁).hom.app _ ≫ (adicLowerStarCongr l e₂).hom.app _ ≫
      (adicLowerStarCongr l e₃).inv.app _ ≫ (adicLowerStarComp l π h).inv.app _ ≫
      (h)_*ᵃ[l].map (torsorTranslation l π τ hτ g) =
    torsorTranslation l π₁ τ₁ hτ₁ g₁ ≫ (π₁)_*ᵃ[l].map (adicUnitToLowerStar l s) ≫
      (adicLowerStarComp l s π₁).hom.app (AdicSheaf.unit l W) ≫
      (adicLowerStarCongr l e₁).hom.app _ ≫ (adicLowerStarCongr l e₂).hom.app _ ≫
      (adicLowerStarCongr l e₃).inv.app _ ≫ (adicLowerStarComp l π h).inv.app _ := by
  subst e₁ e₂
  refine Mod.hom_ext _ _ ?_
  have hW : ∀ {U V : W.ProEtᵒᵖ} (f : U ⟶ V),
      (AdicSheaf.unit l W).X.obj.map f = (adicFunctionsPresheaf l).map f.unop.left.op :=
    fun _ ↦ rfl
  have hW₁ : ∀ {U V : W₁.ProEtᵒᵖ} (f : U ⟶ V),
      (AdicSheaf.unit l W₁).X.obj.map f = (adicFunctionsPresheaf l).map f.unop.left.op :=
    fun _ ↦ rfl
  have a9 : ∀ {M N P : AdicSheaf l Z₁} (f : M ⟶ N) (g : N ⟶ P), (f ≫ g).hom = f.hom ≫ g.hom :=
    fun f g ↦ Mod.comp_hom' f g
  have a1 : ∀ {Y₁ Y₂ : Scheme.{u}} (q : Y₁ ⟶ Y₂) {M N : AdicSheaf l Y₁} (f : M ⟶ N),
      ((q)_*ᵃ[l].map f).hom = (q)_*[WeilCoefficients.{u} l].map f.hom :=
    fun q _ _ f ↦ adicLowerStar_map_hom q f
  have a2 : ∀ {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) (M : AdicSheaf l T),
      ((adicLowerStarComp l h₁ h₂).hom.app M).hom =
        (lowerStarComp (WeilCoefficients.{u} l) h₁ h₂).hom.app M.X :=
    fun h₁ h₂ M ↦ adicLowerStarComp_hom_app_hom h₁ h₂ M
  have a3 : ∀ {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) (M : AdicSheaf l T),
      ((adicLowerStarComp l h₁ h₂).inv.app M).hom =
        (lowerStarComp (WeilCoefficients.{u} l) h₁ h₂).inv.app M.X :=
    fun h₁ h₂ M ↦ adicLowerStarComp_inv_app_hom h₁ h₂ M
  have a4 : ∀ {Y₁ Y₂ : Scheme.{u}} {q q' : Y₁ ⟶ Y₂} (e : q = q') (M : AdicSheaf l Y₁),
      ((adicLowerStarCongr l e).hom.app M).hom =
        (lowerStarCongr (WeilCoefficients.{u} l) e).hom.app M.X :=
    fun e M ↦ adicLowerStarCongr_hom_app_hom e M
  have a5 : ∀ {Y₁ Y₂ : Scheme.{u}} {q q' : Y₁ ⟶ Y₂} (e : q = q') (M : AdicSheaf l Y₁),
      ((adicLowerStarCongr l e).inv.app M).hom =
        (lowerStarCongr (WeilCoefficients.{u} l) e).inv.app M.X :=
    fun e M ↦ adicLowerStarCongr_inv_app_hom e M
  have a6 : (adicUnitToLowerStar l s).hom = adicConstantSheafToLowerStar l s :=
    adicUnitToLowerStar_hom s
  simp only [a9, a1, a2, a3, a4, a5, a6]
  simp only [lowerStarCongr_inv_app_eq, lowerStarCongr_hom_app_comp_lowerStarCongr_hom_app_assoc]
  exact lowerStar_map_adicConstantSheafToLowerStar_comp_torsorTranslation_unit π π₁ h s τ hτ τ₁ hτ₁
    _ g g₁ hτs

/-- Pulling back functions along equal morphisms. -/
lemma adicConstantSheafToLowerStar_comp_lowerStarCongr {f f' : W ⟶ X} (e : f = f') :
    adicConstantSheafToLowerStar l f ≫
      (lowerStarCongr (WeilCoefficients.{u} l) e).hom.app (adicConstantSheaf l W) =
      adicConstantSheafToLowerStar l f' := by
  subst e
  simp

/-- The translations fix the constant functions. -/
lemma adicUnitToLowerStar_comp_torsorTranslation (g : G) :
    adicUnitToLowerStar l π ≫ torsorTranslation l π τ hτ g = adicUnitToLowerStar l π := by
  refine Mod.hom_ext _ _ ?_
  have a9 : ∀ {M N P : AdicSheaf l X} (f : M ⟶ N) (g : N ⟶ P), (f ≫ g).hom = f.hom ≫ g.hom :=
    fun f g ↦ Mod.comp_hom' f g
  have a6 : (adicUnitToLowerStar l π).hom = adicConstantSheafToLowerStar l π :=
    adicUnitToLowerStar_hom π
  have a7 : ∀ {Y₁ Y₂ : Scheme.{u}} (e : Y₁ ≅ Y₂), (adicConstantSheafLowerStarIso l e).inv =
      adicConstantSheafToLowerStar l e.hom := fun _ ↦ rfl
  rw [a9, a6, torsorTranslation_hom, a7, ← Category.assoc, ← Category.assoc,
    Category.assoc (adicConstantSheafToLowerStar l π), adicConstantSheafToLowerStar_comp,
    adicConstantSheafToLowerStar_comp_lowerStarCongr]

end AlgebraicGeometry.ProEtale

namespace CategoryTheory.Adjunction

variable {C D D' E : Type*} [Category* C] [Category* D] [Category* D'] [Category* E]

/-- Transposing along an adjunction commutes with a natural isomorphism of right adjoints, up to
the conjugate isomorphism of left adjoints. -/
lemma homEquiv_symm_comp_app {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (A : L₁ ⊣ R₁) (B : L₂ ⊣ R₂)
    (α : R₁ ⟶ R₂) {X : C} {Y : D} (y : X ⟶ R₁.obj Y) :
    (B.homEquiv _ _).symm (y ≫ α.app Y) =
      ((conjugateEquiv A B).symm α).app X ≫ (A.homEquiv _ _).symm y := by
  have h := conjugateEquiv_counit A B ((conjugateEquiv A B).symm α) Y
  rw [Equiv.apply_symm_apply] at h
  rw [homEquiv_counit, homEquiv_counit, L₂.map_comp, Category.assoc, h,
    ← NatTrans.naturality_assoc]

/-- The transpose along a composite adjunction `L₁ ⋙ L₂ ⊣ R₂ ⋙ R₁` of `ι ≫ R₃ u ≫ λ` is an
isomorphism when `λ : R₄ ⋙ R₃ ≅ R₂ ⋙ R₁` is and the transposes of `ι` and `u` along
`L₃ ⊣ R₃` and `L₄ ⊣ R₄` are. -/
lemma isIso_homEquiv_symm_homEquiv_symm {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
    {L₃ : C ⥤ D'} {R₃ : D' ⥤ C} {L₄ : D' ⥤ E} {R₄ : E ⥤ D'} (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (a₃ : L₃ ⊣ R₃) (a₄ : L₄ ⊣ R₄) (lam : R₄ ⋙ R₃ ≅ R₂ ⋙ R₁) {N : C} {Q : D'} {R : E}
    (ι : N ⟶ R₃.obj Q) (u : Q ⟶ R₄.obj R) [IsIso ((a₃.homEquiv _ _).symm ι)]
    [IsIso ((a₄.homEquiv _ _).symm u)] :
    IsIso ((a₂.homEquiv _ _).symm ((a₁.homEquiv _ _).symm (ι ≫ R₃.map u ≫ lam.hom.app R))) := by
  have e₁ : (a₂.homEquiv _ _).symm ((a₁.homEquiv _ _).symm (ι ≫ R₃.map u ≫ lam.hom.app R)) =
      ((a₁.comp a₂).homEquiv _ _).symm ((ι ≫ R₃.map u) ≫ lam.hom.app R) := by
    rw [Category.assoc, comp_homEquiv]
    rfl
  have e₂ : ((a₃.comp a₄).homEquiv _ _).symm (ι ≫ R₃.map u) =
      L₄.map ((a₃.homEquiv _ _).symm ι) ≫ (a₄.homEquiv _ _).symm u := by
    rw [comp_homEquiv]
    change (a₄.homEquiv _ _).symm ((a₃.homEquiv _ _).symm (ι ≫ R₃.map u)) = _
    rw [homEquiv_naturality_right_symm, homEquiv_naturality_left_symm]
  rw [e₁, homEquiv_symm_comp_app (a₃.comp a₄) (a₁.comp a₂), e₂]
  have : IsIso ((conjugateEquiv (a₃.comp a₄) (a₁.comp a₂)).symm lam.hom) := by
    rw [← conjugateIsoEquiv_symm_apply_hom]
    infer_instance
  infer_instance

end CategoryTheory.Adjunction

namespace CategoryTheory.Adjunction

variable {C D D' E : Type*} [Category* C] [Category* D] [Category* D'] [Category* E]

/-- The transpose along `L₁ ⊣ R₁` of `ι ≫ R₃ u ≫ lam : N ⟶ R₁ R₂ R`, for a natural isomorphism
`lam : R₄ ⋙ R₃ ≅ R₂ ⋙ R₁` (a square of right adjoints). -/
def squareTranspose {L₁ : C ⥤ D} {R₁ : D ⥤ C} {R₂ : E ⥤ D} {R₃ : D' ⥤ C} {R₄ : E ⥤ D'}
    (a₁ : L₁ ⊣ R₁) (lam : R₄ ⋙ R₃ ≅ R₂ ⋙ R₁) {N : C} {Q : D'} {R : E}
    (ι : N ⟶ R₃.obj Q) (u : Q ⟶ R₄.obj R) : L₁.obj N ⟶ R₂.obj R :=
  (a₁.homEquiv _ _).symm (ι ≫ R₃.map u ≫ lam.hom.app R)

/-- The transpose of `squareTranspose` along `L₂ ⊣ R₂` is an isomorphism when the transposes of
`ι` and `u` are. -/
lemma isIso_homEquiv_symm_squareTranspose {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : D ⥤ E}
    {R₂ : E ⥤ D} {L₃ : C ⥤ D'} {R₃ : D' ⥤ C} {L₄ : D' ⥤ E} {R₄ : E ⥤ D'} (a₁ : L₁ ⊣ R₁)
    (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (a₄ : L₄ ⊣ R₄) (lam : R₄ ⋙ R₃ ≅ R₂ ⋙ R₁) {N : C} {Q : D'}
    {R : E} (ι : N ⟶ R₃.obj Q) (u : Q ⟶ R₄.obj R) [IsIso ((a₃.homEquiv _ _).symm ι)]
    [IsIso ((a₄.homEquiv _ _).symm u)] :
    IsIso ((a₂.homEquiv _ _).symm (squareTranspose a₁ lam ι u)) :=
  isIso_homEquiv_symm_homEquiv_symm a₁ a₂ a₃ a₄ lam ι u

/-- Equivariance of `squareTranspose`. -/
lemma squareTranspose_comp {L₁ : C ⥤ D} {R₁ : D ⥤ C} {R₂ : E ⥤ D} {R₃ : D' ⥤ C}
    {R₄ : E ⥤ D'} (a₁ : L₁ ⊣ R₁) (lam : R₄ ⋙ R₃ ≅ R₂ ⋙ R₁) {N : C} {Q : D'} {R : E}
    (ι : N ⟶ R₃.obj Q) (u : Q ⟶ R₄.obj R) (σ : R₂.obj R ⟶ R₂.obj R) (σ₁ : R₃.obj Q ⟶ R₃.obj Q)
    (sN : N ⟶ N) (hι : ι ≫ σ₁ = sN ≫ ι)
    (key : R₃.map u ≫ lam.hom.app R ≫ R₁.map σ = σ₁ ≫ R₃.map u ≫ lam.hom.app R) :
    squareTranspose a₁ lam ι u ≫ σ = L₁.map sN ≫ squareTranspose a₁ lam ι u := by
  rw [squareTranspose, ← homEquiv_naturality_right_symm, ← homEquiv_naturality_left_symm]
  congr 1
  simp only [Category.assoc] at key ⊢
  rw [key, reassoc_of% hι]

end CategoryTheory.Adjunction

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {E : Type*} [Category* E]
  {F : C ⥤ C} {G : D ⥤ D} {H : E ⥤ E}

/-- The components of `mapOfNatIsoCompIso ≪≫ mapOfNatIsoIsoOfIso α` on underlying objects. -/
lemma mapOfNatIsoCompIso_trans_mapOfNatIsoIsoOfIso_hom_app_hom_f {L₁ : C ⥤ D} {L₂ : D ⥤ E}
    {L : C ⥤ E} (e₁ : L₁ ⋙ G ≅ F ⋙ L₁) (e₂ : L₂ ⋙ H ≅ G ⋙ L₂) {e : L ⋙ H ≅ F ⋙ L}
    (α : L₁ ⋙ L₂ ≅ L)
    (hα : Functor.whiskerRight α.hom H ≫ e.hom =
      (compCommIso e₁ e₂).hom ≫ Functor.whiskerLeft F α.hom) (K : IsoAlgebra F) :
    ((mapOfNatIsoCompIso e₁ e₂ ≪≫ mapOfNatIsoIsoOfIso α hα).hom.app K).hom.f =
      α.hom.app K.carrier :=
  Category.id_comp _

/-- The inverse components of `mapOfNatIsoCompIso ≪≫ mapOfNatIsoIsoOfIso α`. -/
lemma mapOfNatIsoCompIso_trans_mapOfNatIsoIsoOfIso_inv_app_hom_f {L₁ : C ⥤ D} {L₂ : D ⥤ E}
    {L : C ⥤ E} (e₁ : L₁ ⋙ G ≅ F ⋙ L₁) (e₂ : L₂ ⋙ H ≅ G ⋙ L₂) {e : L ⋙ H ≅ F ⋙ L}
    (α : L₁ ⋙ L₂ ≅ L)
    (hα : Functor.whiskerRight α.hom H ≫ e.hom =
      (compCommIso e₁ e₂).hom ≫ Functor.whiskerLeft F α.hom) (K : IsoAlgebra F) :
    ((mapOfNatIsoCompIso e₁ e₂ ≪≫ mapOfNatIsoIsoOfIso α hα).inv.app K).hom.f =
      α.inv.app K.carrier :=
  Category.comp_id _

end CategoryTheory.Endofunctor.IsoAlgebra
namespace AlgebraicGeometry

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

variable {W W₁ : Scheme.{u}} [W.Over (Spec (CommRingCat.of k₀))]
  [W₁.Over (Spec (CommRingCat.of k₀))] (s : W ⟶ W₁) [s.IsOver (Spec (CommRingCat.of k₀))]

local notation "s̄" => Scheme.Hom.geometricFiberMap s (comp_over s (Spec (CommRingCat.of k₀)))

/-- A morphism of iso-algebras whose underlying morphism is invertible is invertible
(blueprint `lemma-artin-schreier-character-sheaf`). -/
lemma Endofunctor.IsoAlgebra.isIso_of_isIso_hom_f' {C : Type*} [Category C] {F : C ⥤ C}
    {K K' : Endofunctor.IsoAlgebra F} (f : K ⟶ K') [IsIso f.hom.f] : IsIso f := by
  have : f = (Endofunctor.IsoAlgebra.isoMk (asIso f.hom.f) f.hom.h).hom :=
    Endofunctor.IsoAlgebra.hom_ext rfl
  rw [this]
  infer_instance

/-- The unit `ℚ̄_ℓ ⟶ s̄_* ℚ̄_ℓ` commutes with the Weil structures
(blueprint `lemma-artin-schreier-character-sheaf`). -/
lemma ProEtaleWeilSheaf.unitToLowerStar_comm :
    (WeilSheaf.frobeniusPullback k₀ l W₁).map (adicUnitToLowerStar l s̄) ≫
      (ProEtaleWeilSheaf.torsorPushforward k₀ l s).str.hom =
    (ProEtaleWeilSheaf.adicConstant k₀ l W₁).str.hom ≫ adicUnitToLowerStar l s̄ := by
  refine Mod.hom_ext _ _ ?_
  rw [Mod.comp_hom', Mod.comp_hom', adicLowerStar_map_hom, adicUnitToLowerStar_hom,
    ProEtaleWeilSheaf.torsorPushforward_str_hom_hom, ProEtaleWeilSheaf.adicConstant_str_hom_hom]
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, NatTrans.comp_app, Functor.mapIso_hom,
    Category.assoc]
  exact adicConstantSheafToLowerStar_lowerStarExchange_iso s̄
    (W ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso
    (W₁ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv _ _)

variable (k₀ l) in
/-- The morphism `ℚ̄_ℓ ⟶ s_* ℚ̄_ℓ` of pro-étale Weil sheaves pulling back functions along `s`. -/
noncomputable def ProEtaleWeilSheaf.unitToLowerStar :
    ProEtaleWeilSheaf.adicConstant k₀ l W₁ ⟶ ProEtaleWeilSheaf.torsorPushforward k₀ l s :=
  ObjectProperty.homMk ⟨adicUnitToLowerStar l s̄, ProEtaleWeilSheaf.unitToLowerStar_comm s⟩

/-- The underlying morphism of `AlgebraicGeometry.ProEtaleWeilSheaf.unitToLowerStar`
(blueprint `lemma-artin-schreier-character-sheaf`). -/
lemma ProEtaleWeilSheaf.unitToLowerStar_hom_f :
    (ProEtaleWeilSheaf.unitToLowerStar k₀ l s).hom.f = adicUnitToLowerStar l s̄ :=
  rfl

/-- The translations of a torsor fix the constant functions. -/
lemma ProEtaleWeilSheaf.unitToLowerStar_comp_torsorTranslation {G : Type u} (τ : G → (W ≅ W))
    [∀ g, (τ g).hom.IsOver (Spec (CommRingCat.of k₀))] (hτ : ∀ g, (τ g).hom ≫ s = s) (g : G) :
    ProEtaleWeilSheaf.unitToLowerStar k₀ l s ≫ ProEtaleWeilSheaf.torsorTranslation s τ hτ g =
      ProEtaleWeilSheaf.unitToLowerStar k₀ l s :=
  Endofunctor.IsoAlgebra.hom_ext (ProEtale.adicUnitToLowerStar_comp_torsorTranslation _ _ _ g)

/-- The adjoint `s^* ℚ̄_ℓ ⟶ ℚ̄_ℓ` of the unit `ℚ̄_ℓ ⟶ s_* ℚ̄_ℓ` of pro-étale Weil sheaves is
invertible (blueprint `lemma-artin-schreier-character-sheaf`). -/
instance ProEtaleWeilSheaf.isIso_homEquiv_symm_unitToLowerStar :
    IsIso (((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l s).homEquiv _ _).symm
      (ProEtaleWeilSheaf.unitToLowerStar k₀ l s)) := by
  have : IsIso (((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l s).homEquiv _ _).symm
      (ProEtaleWeilSheaf.unitToLowerStar k₀ l s)).hom.f := by
    rw [Adjunction.homEquiv_counit, Endofunctor.IsoAlgebra.comp_hom_f,
      ProEtaleWeilSheaf.upperStarLowerStarAdjunction_counit_app_hom_f]
    have h : IsIso (((adicUpperStarLowerStarAdjunction l s̄).homEquiv (AdicSheaf.unit l _)
        (AdicSheaf.unit l _)).symm (adicUnitToLowerStar l s̄)) := inferInstance
    rw [Adjunction.homEquiv_counit] at h
    exact h
  exact Endofunctor.IsoAlgebra.isIso_of_isIso_hom_f' _

variable {X Z₁ : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Z₁.Over (Spec (CommRingCat.of k₀))]
  (π : W ⟶ X) (π₁ : W₁ ⟶ Z₁) (h : X ⟶ Z₁)
  [π.IsOver (Spec (CommRingCat.of k₀))] [π₁.IsOver (Spec (CommRingCat.of k₀))]
  [h.IsOver (Spec (CommRingCat.of k₀))]

variable {π π₁ h s} in
variable (k₀ l) in
/-- The isomorphism `π₁_* s_* ≅ h_* π_*` of pushforwards of pro-étale Weil sheaves along a
commutative square `s ≫ π₁ = π ≫ h`. -/
noncomputable def ProEtaleWeilSheaf.lowerStarSquareIso (hs : s ≫ π₁ = π ≫ h) :
    ProEtaleWeilSheaf.lowerStar k₀ l s ⋙ ProEtaleWeilSheaf.lowerStar k₀ l π₁ ≅
      ProEtaleWeilSheaf.lowerStar k₀ l π ⋙ ProEtaleWeilSheaf.lowerStar k₀ l h :=
  ProEtaleWeilSheaf.lowerStarCompIso k₀ l s π₁ ≪≫ ProEtaleWeilSheaf.lowerStarCongr k₀ l hs ≪≫
    (ProEtaleWeilSheaf.lowerStarCompIso k₀ l π h).symm

variable {π π₁ h s} in
/-- The morphism `h^* N ⟶ π_* ℚ̄_ℓ` induced by `ι : N ⟶ π₁_* ℚ̄_ℓ` along a morphism of
torsors: the adjoint of `N ⟶ π₁_* ℚ̄_ℓ ⟶ π₁_* s_* ℚ̄_ℓ ≅ h_* π_* ℚ̄_ℓ`. -/
noncomputable def ProEtaleWeilSheaf.isotypicPullback (hs : s ≫ π₁ = π ≫ h)
    {N : ProEtaleWeilSheaf k₀ l Z₁} (ι : N ⟶ ProEtaleWeilSheaf.torsorPushforward k₀ l π₁) :
    (ProEtaleWeilSheaf.upperStar k₀ l h).obj N ⟶ ProEtaleWeilSheaf.torsorPushforward k₀ l π :=
  Adjunction.squareTranspose (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l h)
    (ProEtaleWeilSheaf.lowerStarSquareIso k₀ l hs) ι (ProEtaleWeilSheaf.unitToLowerStar k₀ l s)

variable {π π₁ h s} in
/-- The adjoint of `isotypicPullback ι` is an isomorphism if that of `ι` is. -/
lemma ProEtaleWeilSheaf.isIso_homEquiv_symm_isotypicPullback (hs : s ≫ π₁ = π ≫ h)
    {N : ProEtaleWeilSheaf k₀ l Z₁} (ι : N ⟶ ProEtaleWeilSheaf.torsorPushforward k₀ l π₁)
    [IsIso (((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l π₁).homEquiv _ _).symm ι)] :
    IsIso (((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l π).homEquiv _ _).symm
      (ProEtaleWeilSheaf.isotypicPullback hs ι)) :=
  Adjunction.isIso_homEquiv_symm_squareTranspose
    (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l h)
    (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l π)
    (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l π₁)
    (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l s)
    (ProEtaleWeilSheaf.lowerStarSquareIso k₀ l hs) ι (ProEtaleWeilSheaf.unitToLowerStar k₀ l s)

/-- The underlying morphism of the composition isomorphism of pushforwards
(blueprint `lemma-artin-schreier-character-sheaf`). -/
lemma ProEtaleWeilSheaf.lowerStarCompIso_hom_app_hom_f {Y₁ Y₂ Y₃ : Scheme.{u}}
    [Y₁.Over (Spec (CommRingCat.of k₀))] [Y₂.Over (Spec (CommRingCat.of k₀))]
    [Y₃.Over (Spec (CommRingCat.of k₀))] (φ : Y₁ ⟶ Y₂) (ψ : Y₂ ⟶ Y₃)
    [φ.IsOver (Spec (CommRingCat.of k₀))] [ψ.IsOver (Spec (CommRingCat.of k₀))]
    (K : ProEtaleWeilSheaf k₀ l Y₁) :
    ((ProEtaleWeilSheaf.lowerStarCompIso k₀ l φ ψ).hom.app K).hom.f =
      (adicLowerStarComp l _ _ ≪≫ adicLowerStarCongr l
        (Scheme.Hom.geometricFiberMap_comp φ ψ (comp_over φ _) (comp_over ψ _)).symm).hom.app
          K.carrier := by
  rw [ProEtaleWeilSheaf.lowerStarCompIso]
  exact Endofunctor.IsoAlgebra.mapOfNatIsoCompIso_trans_mapOfNatIsoIsoOfIso_hom_app_hom_f _ _ _ _ K

/-- The underlying morphism of the inverse composition isomorphism of pushforwards
(blueprint `lemma-artin-schreier-character-sheaf`). -/
lemma ProEtaleWeilSheaf.lowerStarCompIso_inv_app_hom_f {Y₁ Y₂ Y₃ : Scheme.{u}}
    [Y₁.Over (Spec (CommRingCat.of k₀))] [Y₂.Over (Spec (CommRingCat.of k₀))]
    [Y₃.Over (Spec (CommRingCat.of k₀))] (φ : Y₁ ⟶ Y₂) (ψ : Y₂ ⟶ Y₃)
    [φ.IsOver (Spec (CommRingCat.of k₀))] [ψ.IsOver (Spec (CommRingCat.of k₀))]
    (K : ProEtaleWeilSheaf k₀ l Y₁) :
    ((ProEtaleWeilSheaf.lowerStarCompIso k₀ l φ ψ).inv.app K).hom.f =
      (adicLowerStarComp l _ _ ≪≫ adicLowerStarCongr l
        (Scheme.Hom.geometricFiberMap_comp φ ψ (comp_over φ _) (comp_over ψ _)).symm).inv.app
          K.carrier := by
  rw [ProEtaleWeilSheaf.lowerStarCompIso]
  exact Endofunctor.IsoAlgebra.mapOfNatIsoCompIso_trans_mapOfNatIsoIsoOfIso_inv_app_hom_f _ _ _ _ K

/-- The underlying morphism of the isomorphism of pushforwards along equal morphisms
(blueprint `lemma-artin-schreier-character-sheaf`). -/
lemma ProEtaleWeilSheaf.lowerStarCongr_hom_app_hom_f {Y₁ Y₂ : Scheme.{u}}
    [Y₁.Over (Spec (CommRingCat.of k₀))] [Y₂.Over (Spec (CommRingCat.of k₀))] {φ φ' : Y₁ ⟶ Y₂}
    [φ.IsOver (Spec (CommRingCat.of k₀))] [φ'.IsOver (Spec (CommRingCat.of k₀))] (e : φ = φ')
    (K : ProEtaleWeilSheaf k₀ l Y₁) :
    ((ProEtaleWeilSheaf.lowerStarCongr k₀ l e).hom.app K).hom.f =
      (adicLowerStarCongr l (show Scheme.Hom.geometricFiberMap φ (comp_over φ _) =
        Scheme.Hom.geometricFiberMap φ' (comp_over φ' _) by subst e; rfl)).hom.app K.carrier := by
  subst e
  refine Mod.hom_ext _ _ ?_
  rfl

/-- The underlying morphism of the pushforward of a morphism of pro-étale Weil sheaves
(blueprint `lemma-artin-schreier-character-sheaf`). -/
lemma ProEtaleWeilSheaf.lowerStar_map_hom_f {Y₁ Y₂ : Scheme.{u}}
    [Y₁.Over (Spec (CommRingCat.of k₀))] [Y₂.Over (Spec (CommRingCat.of k₀))] (φ : Y₁ ⟶ Y₂)
    [φ.IsOver (Spec (CommRingCat.of k₀))] {K K' : ProEtaleWeilSheaf k₀ l Y₁} (f : K ⟶ K') :
    ((ProEtaleWeilSheaf.lowerStar k₀ l φ).map f).hom.f =
      (Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*ᵃ[l].map f.hom.f :=
  rfl

variable {G G₁ : Type u} (τ : G → (W ≅ W)) [∀ g, (τ g).hom.IsOver (Spec (CommRingCat.of k₀))]
  (hτ : ∀ g, (τ g).hom ≫ π = π) (τ₁ : G₁ → (W₁ ≅ W₁))
  [∀ g, (τ₁ g).hom.IsOver (Spec (CommRingCat.of k₀))] (hτ₁ : ∀ g, (τ₁ g).hom ≫ π₁ = π₁)

variable {π π₁ h s} in
/-- The key identity for the equivariance of `isotypicPullback`. -/
lemma ProEtaleWeilSheaf.isotypicPullback_key (hs : s ≫ π₁ = π ≫ h) (g : G) (g₁ : G₁)
    (hτs : (τ g).hom ≫ s = s ≫ (τ₁ g₁).hom) :
    (ProEtaleWeilSheaf.lowerStar k₀ l π₁).map (ProEtaleWeilSheaf.unitToLowerStar k₀ l s) ≫
      (ProEtaleWeilSheaf.lowerStarSquareIso k₀ l hs).hom.app
        (ProEtaleWeilSheaf.adicConstant k₀ l W) ≫
      (ProEtaleWeilSheaf.lowerStar k₀ l h).map (ProEtaleWeilSheaf.torsorTranslation π τ hτ g) =
    ProEtaleWeilSheaf.torsorTranslation π₁ τ₁ hτ₁ g₁ ≫
      (ProEtaleWeilSheaf.lowerStar k₀ l π₁).map (ProEtaleWeilSheaf.unitToLowerStar k₀ l s) ≫
      (ProEtaleWeilSheaf.lowerStarSquareIso k₀ l hs).hom.app
        (ProEtaleWeilSheaf.adicConstant k₀ l W) := by
  apply Endofunctor.IsoAlgebra.hom_ext
  simp only [Endofunctor.IsoAlgebra.comp_hom_f, ProEtaleWeilSheaf.lowerStar_map_hom_f,
    ProEtaleWeilSheaf.lowerStarSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    ProEtaleWeilSheaf.lowerStarCompIso_hom_app_hom_f,
    ProEtaleWeilSheaf.lowerStarCongr_hom_app_hom_f,
    ProEtaleWeilSheaf.lowerStarCompIso_inv_app_hom_f, ProEtaleWeilSheaf.unitToLowerStar_hom_f,
    ProEtaleWeilSheaf.torsorTranslation_hom_f]
  simp only [Iso.trans_inv, NatTrans.comp_app, Category.assoc]
  have hτs' : (geometricTorsorAut k₀ τ g).hom ≫ Scheme.Hom.geometricFiberMap s (comp_over s _) =
      Scheme.Hom.geometricFiberMap s (comp_over s _) ≫ (geometricTorsorAut k₀ τ₁ g₁).hom := by
    simp only [Scheme.Hom.geometricFiberMapIso_hom]
    rw [← Scheme.Hom.geometricFiberMap_comp, ← Scheme.Hom.geometricFiberMap_comp]
    exact Scheme.Hom.geometricFiberMap_congr hτs _ _
  exact adicLowerStar_map_adicUnitToLowerStar_comp_torsorTranslation _ _ _ _
    (geometricTorsorAut k₀ τ) (geometricTorsorAut_comp k₀ π τ hτ)
    (geometricTorsorAut k₀ τ₁) (geometricTorsorAut_comp k₀ π₁ τ₁ hτ₁) _ _ _ g g₁ hτs'

/-- The pullback commutes with multiplication by a scalar. -/
lemma ProEtaleWeilSheaf.upperStar_map_smulEnd {Y₁ Y₂ : Scheme.{u}}
    [Y₁.Over (Spec (CommRingCat.of k₀))] [Y₂.Over (Spec (CommRingCat.of k₀))] (φ : Y₁ ⟶ Y₂)
    [φ.IsOver (Spec (CommRingCat.of k₀))] (b : PadicAlgCl l) (N : ProEtaleWeilSheaf k₀ l Y₂) :
    (ProEtaleWeilSheaf.upperStar k₀ l φ).map (ProEtaleWeilSheaf.smulEnd b N) =
      ProEtaleWeilSheaf.smulEnd b ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj N) :=
  Endofunctor.IsoAlgebra.hom_ext (AdicSheaf.adicUpperStar_map_smul _ _ _)

variable {π π₁ h s} in
/-- **Equivariance of `isotypicPullback`.** If `G₁` acts on `ι` through `χ` and
`τ_g ≫ s = s ≫ τ₁_{c g}`, then `G` acts on `isotypicPullback ι` through `χ ∘ c`. -/
lemma ProEtaleWeilSheaf.isotypicPullback_comp_torsorTranslation (hs : s ≫ π₁ = π ≫ h)
    {N : ProEtaleWeilSheaf k₀ l Z₁} (ι : N ⟶ ProEtaleWeilSheaf.torsorPushforward k₀ l π₁)
    (χ : G₁ → PadicAlgCl l)
    (hι : ∀ g₁, ι ≫ ProEtaleWeilSheaf.torsorTranslation π₁ τ₁ hτ₁ g₁ =
      ProEtaleWeilSheaf.smulEnd (χ g₁) N ≫ ι)
    (c : G → G₁) (hτs : ∀ g, (τ g).hom ≫ s = s ≫ (τ₁ (c g)).hom) (g : G) :
    ProEtaleWeilSheaf.isotypicPullback hs ι ≫ ProEtaleWeilSheaf.torsorTranslation π τ hτ g =
      ProEtaleWeilSheaf.smulEnd (χ (c g)) _ ≫ ProEtaleWeilSheaf.isotypicPullback hs ι := by
  rw [← ProEtaleWeilSheaf.upperStar_map_smulEnd]
  exact Adjunction.squareTranspose_comp _ _ ι _ _ _ _ (hι (c g))
    (ProEtaleWeilSheaf.isotypicPullback_key τ hτ τ₁ hτ₁ hs g (c g) (hτs g))

/-- The underlying morphism of a transpose along `φ^* ⊣ φ_*`. -/
lemma ProEtaleWeilSheaf.homEquiv_symm_hom_f {Y₁ Y₂ : Scheme.{u}}
    [Y₁.Over (Spec (CommRingCat.of k₀))] [Y₂.Over (Spec (CommRingCat.of k₀))] (φ : Y₁ ⟶ Y₂)
    [φ.IsOver (Spec (CommRingCat.of k₀))] {M : ProEtaleWeilSheaf k₀ l Y₂}
    {N : ProEtaleWeilSheaf k₀ l Y₁}
    (f : M ⟶ (ProEtaleWeilSheaf.lowerStar k₀ l φ).obj N) :
    (((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l φ).homEquiv _ _).symm f).hom.f =
      (Scheme.Hom.geometricFiberMap φ (comp_over φ _))^*ᵃ[l].map f.hom.f ≫
        (adicUpperStarLowerStarAdjunction l
          (Scheme.Hom.geometricFiberMap φ (comp_over φ _))).counit.app N.carrier := by
  rw [Adjunction.homEquiv_counit, Endofunctor.IsoAlgebra.comp_hom_f,
    ProEtaleWeilSheaf.upperStarLowerStarAdjunction_counit_app_hom_f]
  rfl

end AlgebraicGeometry
