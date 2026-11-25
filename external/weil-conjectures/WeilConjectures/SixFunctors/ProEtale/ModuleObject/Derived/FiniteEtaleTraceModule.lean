/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteEtaleTracePadicAlgCl
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteEtaleTraceProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange

/-!
# The trace of a locally split cover on module objects

Let `g : Y ⟶ X` be weakly étale and pro-étale locally split into `d` sheets
(`AlgebraicGeometry.ProEtale.IsLocallySplit`). The trace `T : j_g^* ⋙ g_* ⟶ 𝟭` on abelian
sheaves (`AlgebraicGeometry.ProEtale.splitTrace`) is linear over every condensed ring `Λ`, by
its projection formula (`AlgebraicGeometry.ProEtale.splitTrace_projection`). Transported along
the identification of `g^*` with the restriction `j_g^*`, it gives a trace
`g^* ⋙ g_* ⟶ 𝟭` on module objects over `Λ`
(`AlgebraicGeometry.ProEtale.CondensedRing.splitTraceModule`), whose composite with the unit of
`g^* ⊣ g_*` is multiplication by `d`
(`AlgebraicGeometry.ProEtale.CondensedRing.unit_comp_splitTraceModule`).

For `ℚ̲̄_ℓ`-coefficients and `d ≠ 0`, the unit of the derived adjunction `Lg^* ⊣ Rg_*` along a
finite `g` of finite presentation is thus a split monomorphism at every complex
(`isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_of_isLocallySplit`).

The linearity is first proved in an abstract setting
(`CategoryTheory.comp_trace_eq_of_projection`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal

open scoped CategoryTheory.Obj

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  {L₁ L₂ : C ⥤ D} {G : D ⥤ C} [L₁.LaxMonoidal] [L₂.LaxMonoidal] [G.LaxMonoidal]

/-- **Linearity of a trace satisfying the projection formula**, abstractly. Let `L₁` and `L₂`
be lax monoidal functors related by a monoidal transformation `e`, `G` a lax monoidal functor,
`η₁ : 𝟭 ⟶ L₁ ⋙ G` and `η₂ : 𝟭 ⟶ L₂ ⋙ G` compatible with `e`, and `T : L₂ ⋙ G ⟶ 𝟭` satisfying
the projection formula `(η₂ ▷ _) ≫ μ ≫ T = _ ◁ T`. Let `γM : R ⊗ M ⟶ M` and `γP : S ⊗ P ⟶ P`
be actions and `u : L₁ M ⟶ P` an isomorphism, linear along `α : L₁ R ⟶ S`. Then the map
`G P ⟶ G L₁ M ⟶ G L₂ M ⟶ M` is linear for the action of `R` on `G P` through `η₁` and `α`. -/
theorem comp_trace_eq_of_projection (e : L₁ ⟶ L₂) [NatTrans.IsMonoidal e]
    (η₁ : 𝟭 C ⟶ L₁ ⋙ G) (η₂ : 𝟭 C ⟶ L₂ ⋙ G)
    (hη : ∀ X, η₁.app X ≫ G.map (e.app X) = η₂.app X) (T : L₂ ⋙ G ⟶ 𝟭 C)
    (hT : ∀ P Q, η₂.app P ▷ _ ≫ μ (L₂ ⋙ G) P Q ≫ T.app (P ⊗ Q) = P ◁ T.app Q)
    {R M : C} {S P : D} (γM : R ⊗ M ⟶ M) (γP : S ⊗ P ⟶ P) (α : L₁.obj R ⟶ S)
    (u : L₁.obj M ⟶ P) [IsIso u]
    (hu : μ L₁ R M ≫ L₁.map γM ≫ u = L₁.obj R ◁ u ≫ α ▷ P ≫ γP) :
    ((η₁.app R ≫ G.map α) ▷ G.obj P ≫ μ G S P ≫ G.map γP) ≫
        G.map (inv u ≫ e.app M) ≫ T.app M =
      R ◁ (G.map (inv u ≫ e.app M) ≫ T.app M) ≫ γM := by
  have hu' : α ▷ P ≫ γP ≫ inv u = L₁.obj R ◁ inv u ≫ μ L₁ R M ≫ L₁.map γM := by
    rw [← cancel_epi (L₁.obj R ◁ u), ← MonoidalCategory.whiskerLeft_comp_assoc,
      IsIso.hom_inv_id, MonoidalCategory.whiskerLeft_id, Category.id_comp,
      reassoc_of% hu.symm, IsIso.hom_inv_id, Category.comp_id]
  have hT' := T.naturality γM
  have hmon := NatTrans.IsMonoidal.tensor (τ := e) R M
  have hη' := hη R
  have hT'' := hT R M
  simp only [Functor.comp_map, Functor.id_map] at hT'
  simp only [comp_μ] at hT''
  calc ((η₁.app R ≫ G.map α) ▷ G.obj P ≫ μ G S P ≫ G.map γP) ≫
        G.map (inv u ≫ e.app M) ≫ T.app M
      = η₁.app R ▷ G.obj P ≫ μ G (L₁.obj R) P ≫
          G.map (α ▷ P ≫ γP ≫ inv u) ≫ G.map (e.app M) ≫ T.app M := by
        simp only [comp_whiskerRight, Category.assoc, μ_natural_left_assoc, Functor.map_comp]
    _ = η₁.app R ▷ G.obj P ≫ (G.obj (L₁.obj R) ◁ G.map (inv u)) ≫
          μ G (L₁.obj R) (L₁.obj M) ≫ G.map (μ L₁ R M ≫ e.app (R ⊗ M)) ≫
          G.map (L₂.map γM) ≫ T.app M := by
        rw [hu']
        simp only [Functor.map_comp, Category.assoc, μ_natural_right_assoc]
        rw [← G.map_comp_assoc (L₁.map γM), e.naturality, G.map_comp_assoc]
    _ = η₁.app R ▷ G.obj P ≫ (G.obj (L₁.obj R) ◁ G.map (inv u)) ≫
          (G.map (e.app R) ⊗ₘ G.map (e.app M)) ≫
          (μ G (L₂.obj R) (L₂.obj M) ≫ G.map (μ L₂ R M)) ≫ T.app (R ⊗ M) ≫ γM := by
        rw [hmon, G.map_comp]
        simp only [Category.assoc]
        rw [hT', ← μ_natural_assoc]
    _ = R ◁ (G.map (inv u ≫ e.app M)) ≫ η₂.app R ▷ _ ≫
          (μ G (L₂.obj R) (L₂.obj M) ≫ G.map (μ L₂ R M)) ≫ T.app (R ⊗ M) ≫ γM := by
        rw [← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
          tensorHom_comp_tensorHom_assoc, ← id_tensorHom, ← tensorHom_id,
          tensorHom_comp_tensorHom_assoc]
        simp only [Category.comp_id, Category.assoc, Functor.map_comp]
        erw [Category.id_comp, hη', Category.id_comp, Category.id_comp]
    _ = R ◁ (G.map (inv u ≫ e.app M) ≫ T.app M) ≫ γM := by
        simp only [Category.assoc] at hT'' ⊢
        erw [reassoc_of% hT'']
        rw [MonoidalCategory.whiskerLeft_comp_assoc]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme MonObj

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} {g : Y ⟶ X} [WeaklyEtale g] {d : ℕ} (hg : IsLocallySplit g d)

/-- The underlying map `g_* g^* M ⟶ M` of the trace on module objects: the trace on sheaves,
after the identifications of the underlying sheaf of `g^* M` with `g^* M.X` and of `g^*` with
the restriction `j_g^*`. -/
noncomputable def splitTraceModuleHom
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ((g)_*⟦Λ⟧.obj ((g)^*⟦Λ⟧.obj M)).X ⟶ M.X :=
  (g)_*[Ab.{u + 1}].map (inv (upperStarUnitHom Λ g M) ≫
    (upperStarIsoLocalizationRestriction Ab.{u + 1} g inferInstance).hom.app M.X) ≫
    (splitTrace hg Ab.{u + 1}).app M.X

/-- The trace is `Λ_X`-linear, by the projection formula. -/
instance isModHom_splitTraceModuleHom
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsModHom (condensedRingObj Λ X) (splitTraceModuleHom Λ hg M) := by
  refine ⟨?_⟩
  simp only [MonoidalCategory.selfLeftAction_actionHomRight]
  rw [lowerStar_obj_smul]
  exact comp_trace_eq_of_projection
    (upperStarIsoLocalizationRestriction Ab.{u + 1} g inferInstance).hom
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} g).unit
    (localizationRestrictionLowerStarAdjunction Ab.{u + 1} g inferInstance).unit
    (fun X ↦ Adjunction.unit_leftAdjointUniq_hom_app _ _ X)
    (splitTrace hg Ab.{u + 1}) (splitTrace_projection hg)
    γ[condensedRingObj Λ X, M.X] γ[condensedRingObj Λ Y, ((g)^*⟦Λ⟧.obj M).X]
    (condensedPullbackHom Λ g) (upperStarUnitHom Λ g M)
    ((Category.assoc _ _ _).symm.trans
      ((Mod.smul_extendUnitHom (condensedPullbackHom Λ g)
        (((g)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ X)).obj M)).trans
      (Mod.whiskerLeft_extendUnitHom_smul (condensedPullbackHom Λ g)
        (((g)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ X)).obj M)).symm))

/-- The **trace** `g^* ⋙ g_* ⟶ 𝟭` on module objects over `Λ`, for a weakly étale `g` which is
pro-étale locally split into `d` sheets. -/
noncomputable def splitTraceModule : (g)^*⟦Λ⟧ ⋙ (g)_*⟦Λ⟧ ⟶ 𝟭 _ where
  app M := ⟨splitTraceModuleHom Λ hg M⟩
  naturality M N f := by
    refine Mod.Hom.ext ?_
    change (g)_*[Ab.{u + 1}].map ((g)^*⟦Λ⟧.map f).hom ≫ splitTraceModuleHom Λ hg N =
      splitTraceModuleHom Λ hg M ≫ f.hom
    have h₁ : ((g)^*⟦Λ⟧.map f).hom ≫ inv (upperStarUnitHom Λ g N) =
        inv (upperStarUnitHom Λ g M) ≫ (g)^*[Ab.{u + 1}].map f.hom := by
      rw [IsIso.eq_inv_comp, upperStarUnitHom_map_hom_assoc, IsIso.hom_inv_id,
        Category.comp_id]
    have h₂ := (upperStarIsoLocalizationRestriction Ab.{u + 1} g inferInstance).hom.naturality
      f.hom
    have h₃ := (splitTrace hg Ab.{u + 1}).naturality f.hom
    simp only [Functor.comp_map, Functor.id_map] at h₃
    simp only [splitTraceModuleHom, ← Functor.map_comp_assoc, reassoc_of% h₁, h₂]
    simp only [Functor.map_comp, Category.assoc, h₃]

/-- The underlying map of the trace on module objects. -/
lemma splitTraceModule_app_hom
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ((splitTraceModule Λ hg).app M).hom = splitTraceModuleHom Λ hg M := rfl

/-- The unit of `g^* ⊣ g_*` on module objects followed by the trace of a cover locally split
into `d` sheets is multiplication by `d`. -/
theorem unit_comp_splitTraceModule :
    (upperStarLowerStarAdjunction Λ g).unit ≫ splitTraceModule Λ hg = d • 𝟙 _ := by
  refine NatTrans.ext (funext fun M ↦ Mod.Hom.ext ?_)
  have h := forget_map_upperStarLowerStarAdjunction_unit_app' Λ g M
  have hT := congr_app (unit_comp_splitTrace hg Ab.{u + 1}) M.X
  have hn : (d • 𝟙 M).hom = d • 𝟙 M.X := (Mod.forget _).map_nsmul (f := 𝟙 M) (n := d)
  simp only [NatTrans.comp_app, NatTrans.app_nsmul, NatTrans.id_app] at hT ⊢
  rw [Mod.comp_hom']
  erw [hn]
  rw [splitTraceModule_app_hom]
  have h' : ((upperStarLowerStarAdjunction Λ g).unit.app M).hom = _ := h
  rw [h', upperStarForgetIso_hom_app, splitTraceModuleHom]
  have hl : (lowerStarForgetIso Λ g).hom.app ((g)^*⟦Λ⟧.obj M) = 𝟙 _ := rfl
  rw [hl]
  simp only [Category.assoc]
  erw [Category.id_comp]
  have he : (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} g).unit.app M.X ≫
      (g)_*[Ab.{u + 1}].map
        ((upperStarIsoLocalizationRestriction Ab.{u + 1} g inferInstance).hom.app M.X) =
      (localizationRestrictionLowerStarAdjunction Ab.{u + 1} g inferInstance).unit.app M.X :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ _
  rw [← Functor.map_comp_assoc, IsIso.hom_inv_id_assoc]
  erw [reassoc_of% he]
  exact hT

include hg in
/-- **Split derived units along a locally split finite cover**, for `ℚ̲̄_ℓ`-coefficients: let
`g : Y ⟶ X` be finite of finite presentation and weakly étale (e.g. finite étale), pro-étale
locally split into `d ≠ 0` sheets. Then the unit of the derived adjunction `Lg^* ⊣ Rg_*` is a
split monomorphism at every complex. -/
theorem isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_of_isLocallySplit
    (ℓ : ℕ) [Fact ℓ.Prime] [IsFinite g] [LocallyOfFinitePresentation g] (hd : d ≠ 0)
    (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))) :
    IsSplitMono ((derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ)
      g).unit.app G) :=
  isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_of_nsmul ℓ g
    (splitTraceModule _ hg) hd (unit_comp_splitTraceModule _ hg) G

end AlgebraicGeometry.ProEtale.CondensedRing
