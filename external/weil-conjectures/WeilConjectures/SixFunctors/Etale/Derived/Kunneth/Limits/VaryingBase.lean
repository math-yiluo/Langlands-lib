/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.FixedBase
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.PushforwardLimit

/-!
# Higher direct images along a limit with varying base

Let `gᵢ : Tᵢ ⟶ Sᵢ` be a cofiltered system of quasi-compact quasi-separated morphisms with affine
transition maps, with limit `g₀ : T ⟶ S`, the stages `Sᵢ` being quasi-compact and
quasi-separated, and let `G` be a sheaf on a scheme `W` to which the `Tᵢ` map compatibly. Then
on every geometric stalk of `S`, `R^q g₀_* (G|_T)` is the filtered colimit of the
`πᵢ^* R^q gᵢ_* (G|_{Tᵢ})` (`AlgebraicGeometry.Etale.isStalkColimit_varyingBaseSystem`,
Stacks 0EYM).

The proof combines the fixed-base statement `AlgebraicGeometry.Etale.higherDirectImage_limit`
(Stacks 09Z1) over each `Sⱼ`, for the system `Tₖ ⟶ Sₖ ⟶ Sⱼ`, with the statement
`AlgebraicGeometry.Etale.isStalkColimit_pushforwardStageSystem` for `g₀` and the system `Sⱼ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {I : Type u} [Category.{u} I] {S T : I ⥤ Scheme.{u}} (g : T ⟶ S) {cS : Cone S}
  {cT : Cone T} {g₀ : cT.pt ⟶ cS.pt} (hg₀ : ∀ i, g₀ ≫ cS.π.app i = cT.π.app i ≫ g.app i)
  {W : Scheme.{u}} (w : T ⟶ (Functor.const I).obj W) (w₀ : cT.pt ⟶ W)
  (hw₀ : ∀ i, cT.π.app i ≫ w.app i = w₀)

/-- The system of stages `(Tᵢ, Sᵢ, gᵢ, πᵢ, wᵢ)` over `S = cS.pt`, with limit stage
`(T, S, g₀, 𝟙, w₀)`. -/
@[simps]
noncomputable def varyingBaseSystem : LimitStageSystem cS.pt W I where
  obj i := ⟨T.obj i, S.obj i, g.app i, cS.π.app i, w.app i⟩
  map f := ⟨T.map f, S.map f, g.naturality f, cS.w f, by simp⟩
  map_id i := LimitStage.Hom.ext (T.map_id i) (S.map_id i)
  map_comp f g := LimitStage.Hom.ext (T.map_comp f g) (S.map_comp f g)
  pt := ⟨cT.pt, cS.pt, g₀, 𝟙 _, w₀⟩
  π i := ⟨cT.π.app i, cS.π.app i, (hg₀ i).symm, by simp, hw₀ i⟩
  w f := LimitStage.Hom.ext (cT.w f) (cS.w f)

/-- The fixed-base system over `Sⱼ`, pulled back to `S`, with coefficients from `W`: the stages
`(Tₖ, Sⱼ, Tₖ ⟶ Tⱼ ⟶ Sⱼ, πⱼ, Tₖ ⟶ Tⱼ ⟶ W)` for `k ⟶ j`. -/
noncomputable abbrev varyingBaseFixedSystem (j : I) : LimitStageSystem cS.pt W (Over j) :=
  (fixedBaseSystem (k := g.app j) (p := cS.π.app j) (D := Over.post (X := j) T)
    (c := cT.overPost j)).mapW (w.app j)

include hg₀ in
lemma isStalkColimit_varyingBaseFixedSystem [IsCofiltered I] (hS : IsLimit cS)
    (hT : IsLimit cT) [∀ i, QuasiCompact (g.app i)] [∀ i, QuasiSeparated (g.app i)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (S.map f)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (T.map f)] [QuasiCompact g₀] [QuasiSeparated g₀]
    (j : I) (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    (varyingBaseFixedSystem (cS := cS) (cT := cT) g w j).IsStalkColimit Λ
      ((DerivedCategory.Plus.singleFunctor _ 0).obj G) q := by
  have : ∀ {U V : Over j} (φ : U ⟶ V), IsAffineHom ((Over.post (X := j) T).map φ).left :=
    fun φ ↦ (inferInstance : IsAffineHom (T.map φ.left))
  have : ∀ U : Over j, QuasiCompact (((Over.post (X := j) T).obj U).hom ≫ g.app j) :=
    fun U ↦ (inferInstance : QuasiCompact (T.map U.hom ≫ g.app j))
  have : ∀ U : Over j, QuasiSeparated (((Over.post (X := j) T).obj U).hom ≫ g.app j) :=
    fun U ↦ (inferInstance : QuasiSeparated (T.map U.hom ≫ g.app j))
  have : IsAffineHom (cS.π.app j) := isAffineHom_π_app S cS hS j
  have : QuasiCompact ((cT.overPost j).pt.hom ≫ g.app j) := by
    change QuasiCompact (cT.π.app j ≫ g.app j)
    rw [← hg₀]
    infer_instance
  have : QuasiSeparated ((cT.overPost j).pt.hom ≫ g.app j) := by
    change QuasiSeparated (cT.π.app j ≫ g.app j)
    rw [← hg₀]
    infer_instance
  have hc : IsLimit ((Over.forget (T.obj j)).mapCone (cT.overPost j)) :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget j) cT).symm hT
  exact LimitStageSystem.isStalkColimit_mapW (w.app j) _ (LimitStageSystem.isStalkColimit_of_iso _
    ((((w.app j)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app G)
    (isStalkColimit_fixedBaseSystem Λ (g.app j) (((w.app j)^*[ModuleCat.{u + 1} Λ]).obj G) q
      (Over.post (X := j) T) (cT.overPost j) (cS.π.app j) hc))

/-- The `[*]`-system `(T, Sⱼ, g₀ ≫ πⱼ, πⱼ, 𝟙 ≫ w₀)`. -/
noncomputable abbrev varyingBaseStarSystem : LimitStageSystem cS.pt W I :=
  (pushforwardStageSystem cS g₀).mapW w₀

lemma isStalkColimit_varyingBaseStarSystem [IsCofiltered I] (hS : IsLimit cS)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (S.map f)]
    [∀ i, CompactSpace (S.obj i)] [∀ i, QuasiSeparatedSpace (S.obj i)]
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    (varyingBaseStarSystem (g₀ := g₀) w₀).IsStalkColimit Λ
      ((DerivedCategory.Plus.singleFunctor _ 0).obj G) q :=
  LimitStageSystem.isStalkColimit_mapW w₀ _ (LimitStageSystem.isStalkColimit_of_iso _
    ((((w₀)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app G)
    (isStalkColimit_pushforwardStageSystem Λ cS g₀ hS _ q))

include hg₀ hw₀ in
/-- **Higher direct images along a limit with varying base** (Stacks 0EYM), on geometric
stalks: `R^q g₀_* (G|_T)` is the filtered colimit of the `πᵢ^* R^q gᵢ_* (G|_{Tᵢ})`. -/
theorem isStalkColimit_varyingBaseSystem [IsCofiltered I] (hS : IsLimit cS) (hT : IsLimit cT)
    [∀ i, QuasiCompact (g.app i)] [∀ i, QuasiSeparated (g.app i)]
    [∀ i, CompactSpace (S.obj i)] [∀ i, QuasiSeparatedSpace (S.obj i)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (S.map f)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (T.map f)] [QuasiCompact g₀] [QuasiSeparated g₀]
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    (varyingBaseSystem g hg₀ w w₀ hw₀).IsStalkColimit Λ
      ((DerivedCategory.Plus.singleFunctor _ 0).obj G) q := by
  intro x
  have hE := isStalkColimit_varyingBaseStarSystem Λ (g₀ := g₀) w₀ hS G q x
  have hD := fun j ↦ isStalkColimit_varyingBaseFixedSystem Λ g hg₀ w hS hT j G q x
  let K := (DerivedCategory.Plus.singleFunctor (Sheaf W.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) 0).obj G
  let 𝒜 := varyingBaseSystem g hg₀ w w₀ hw₀
  let ℰ := varyingBaseStarSystem (g₀ := g₀) w₀
  let 𝒟 (j : I) := varyingBaseFixedSystem (cS := cS) (cT := cT) g w j
  let θ {α β : LimitStage cS.pt W} (φ : LimitStage.Hom α β) :=
    ((stalkHomology Λ q x).map ((LimitStage.transition Λ φ).app K)).hom
  have tc' {α β γ : LimitStage cS.pt W} (φ : LimitStage.Hom α β) (ψ : LimitStage.Hom β γ) (y) :
      θ φ (θ ψ y) = θ (φ.comp ψ) y := LimitStage.transition_apply_comp Λ q x K φ ψ _ rfl y
  have inv' {α β : LimitStage cS.pt W} (φ : LimitStage.Hom α β) (ψ : LimitStage.Hom β α)
      (h : φ.comp ψ = LimitStage.Hom.id α) (y) : θ φ (θ ψ y) = y :=
    LimitStage.transition_apply_inv Λ q x K φ ψ h y
  let ζ : LimitStage.Hom ℰ.pt 𝒜.pt := ⟨𝟙 _, 𝟙 _, by simp [ℰ, 𝒜], by simp [ℰ, 𝒜], by
    simp only [varyingBaseSystem_pt_w, Category.id_comp, LimitStageSystem.mapW_pt_w,
      pushforwardStageSystem_pt_w, ℰ, 𝒜]
    exact (Category.id_comp _).symm⟩
  let ζ' : LimitStage.Hom 𝒜.pt ℰ.pt := ⟨𝟙 _, 𝟙 _, by simp [ℰ, 𝒜], by simp [ℰ, 𝒜], by
    simp only [LimitStageSystem.mapW_pt_w, pushforwardStageSystem_pt_w, Category.id_comp,
      varyingBaseSystem_pt_w, 𝒜, ℰ]
    exact Category.id_comp _⟩
  let ξ (j : I) : LimitStage.Hom (𝒟 j).pt (ℰ.obj j) :=
    ⟨𝟙 _, 𝟙 _, by simp [ℰ, 𝒟, hg₀]; rfl, by simp [ℰ, 𝒟], by
      simp only [LimitStageSystem.mapW_obj_w, pushforwardStageSystem_obj_w, Category.id_comp,
        LimitStageSystem.mapW_pt_w, Functor.const_obj_obj, fixedBaseSystem_pt_w, 𝒟, ℰ]
      exact (Category.id_comp _).trans (hw₀ j).symm⟩
  let ξ' (j : I) : LimitStage.Hom (ℰ.obj j) (𝒟 j).pt :=
    ⟨𝟙 _, 𝟙 _, by simp [ℰ, 𝒟, hg₀]; rfl, by simp [ℰ, 𝒟], by
      simp only [LimitStageSystem.mapW_pt_w, Functor.const_obj_obj, fixedBaseSystem_pt_w,
        Category.id_comp, LimitStageSystem.mapW_obj_w, pushforwardStageSystem_obj_w, ℰ, 𝒟]
      exact (hw₀ j).trans (Category.id_comp _).symm⟩
  let σD (j : I) (U : Over j) : LimitStage.Hom (ℰ.obj j) ((𝒟 j).obj U) := (ξ' j).comp ((𝒟 j).π U)
  let ρ (k : I) : LimitStage.Hom ((𝒟 k).obj (Over.mk (𝟙 k))) (𝒜.obj k) :=
    ⟨𝟙 _, 𝟙 _,
      by
        simp only [varyingBaseSystem_obj_g, Category.id_comp, LimitStageSystem.mapW_obj_g,
          Functor.const_obj_obj, fixedBaseSystem_obj_g, Category.comp_id, 𝒟, 𝒜]
        exact ((congrArg (· ≫ g.app k) (T.map_id k)).trans (Category.id_comp _)).symm,
      by simp [𝒜, 𝒟],
      by
        simp only [varyingBaseSystem_obj_w, Category.id_comp, LimitStageSystem.mapW_obj_w,
          Functor.const_obj_obj, fixedBaseSystem_obj_w, 𝒟, 𝒜]
        exact ((congrArg (· ≫ w.app k) (T.map_id k)).trans (Category.id_comp _)).symm⟩
  let ψ {j : I} (U : Over j) : LimitStage.Hom (𝒜.obj U.left) ((𝒟 j).obj U) :=
    ⟨𝟙 _, S.map U.hom,
      by
        simp only [LimitStageSystem.mapW_obj_g, Functor.const_obj_obj, fixedBaseSystem_obj_g,
          Category.id_comp, varyingBaseSystem_obj_g, 𝒜, 𝒟]
        exact g.naturality U.hom,
      by simp [𝒜, 𝒟],
      by
        simp only [LimitStageSystem.mapW_obj_w, Functor.const_obj_obj, fixedBaseSystem_obj_w,
          Category.id_comp, varyingBaseSystem_obj_w, 𝒜, 𝒟]
        exact (w.naturality U.hom).trans (Category.comp_id _)⟩
  refine ⟨fun b ↦ ?_, fun k a ha ↦ ?_⟩
  · obtain ⟨j, e, he⟩ := hE.1 (θ ζ b)
    obtain ⟨U, d, hd⟩ := (hD j).1 (θ (ξ j) e)
    refine ⟨U.left, θ (ψ U) d, ?_⟩
    have he' : θ (σD j U) d = e := by
      have : θ ((𝒟 j).π U) d = θ (ξ j) e := hd
      change θ ((ξ' j).comp ((𝒟 j).π U)) d = e
      rw [← tc', this, inv' _ _ (LimitStage.Hom.ext (by simp [ξ, ξ']) (by simp [ξ, ξ']))]
    have hχ : (𝒜.π U.left).comp (ψ U) = ζ'.comp ((ℰ.π j).comp (σD j U)) :=
      LimitStage.Hom.ext
        (by
          simp only [varyingBaseSystem_π_t, Category.comp_id, LimitStageSystem.mapW_π_t,
            pushforwardStageSystem_π_t, Functor.const_obj_obj, fixedBaseSystem_π_t,
            Cone.overPost_π_app, Over.homMk_left, Category.id_comp, 𝒜, 𝒟, ℰ, ζ', ψ, σD, ξ']
          exact (Category.id_comp _).symm)
        (by
          simp only [varyingBaseSystem_π_s, Cone.w, LimitStageSystem.mapW_π_s,
            pushforwardStageSystem_π_s, Functor.const_obj_obj, fixedBaseSystem_π_s,
            Category.id_comp, 𝒜, 𝒟, ℰ, ζ', ψ, σD, ξ']
          exact (Category.comp_id _).symm)
    have hinv := inv' ζ' ζ (LimitStage.Hom.ext (by simp [ζ, ζ']) (by simp [ζ, ζ'])) b
    change θ (𝒜.π U.left) (θ (ψ U) d) = b
    have he0 : θ (ℰ.π j) e = θ ζ b := he
    rw [tc', hχ, ← tc', ← tc', he', he0, hinv]
  · let e := θ (σD k (Over.mk (𝟙 k))) (θ (ρ k) a)
    have he0 : θ (ℰ.π k) e = 0 := by
      have hχ : ((ℰ.π k).comp (σD k (Over.mk (𝟙 k)))).comp (ρ k) = ζ.comp (𝒜.π k) :=
        LimitStage.Hom.ext
          (by
            simp only [LimitStageSystem.mapW_π_t, pushforwardStageSystem_π_t,
              Functor.const_obj_obj, fixedBaseSystem_π_t, Cone.overPost_π_app, Over.mk_left,
              Over.homMk_left, Category.id_comp, Category.comp_id, varyingBaseSystem_π_t, ℰ, 𝒜,
              𝒟, σD, ρ, ζ, ξ']
            exact Category.id_comp _)
          (by
            simp only [LimitStageSystem.mapW_π_s, pushforwardStageSystem_π_s,
              Functor.const_obj_obj, fixedBaseSystem_π_s, Category.id_comp, Category.comp_id,
              varyingBaseSystem_π_s, ℰ, 𝒜, 𝒟, σD, ρ, ζ, ξ']
            exact Category.comp_id _)
      have : θ (𝒜.π k) a = 0 := ha
      simp only [e]
      rw [tc', tc', hχ, ← tc', this, map_zero]
    obtain ⟨j, f, hf⟩ := hE.2 k e he0
    let aj := θ (𝒜.map f) a
    have hd0 : θ ((𝒟 j).π (Over.mk (𝟙 j))) (θ (ρ j) aj) = 0 := by
      have hχ : ((σD j (Over.mk (𝟙 j))).comp (ρ j)).comp (𝒜.map f) =
          (ℰ.map f).comp ((σD k (Over.mk (𝟙 k))).comp (ρ k)) :=
        LimitStage.Hom.ext
          (by
            simp only [LimitStageSystem.mapW_π_t, Functor.const_obj_obj, fixedBaseSystem_π_t,
              Cone.overPost_π_app, Over.mk_left, Over.homMk_left, Category.id_comp,
              Category.comp_id, varyingBaseSystem_map_t, Cone.w, LimitStageSystem.mapW_map_t,
              pushforwardStageSystem_map_t, ℰ, 𝒜, 𝒟, σD, ρ, ξ']
            exact (Category.id_comp _).symm)
          (by
            simp only [LimitStageSystem.mapW_π_s, Functor.const_obj_obj, fixedBaseSystem_π_s,
              Category.id_comp, Category.comp_id, varyingBaseSystem_map_s,
              LimitStageSystem.mapW_map_s, pushforwardStageSystem_map_s, ℰ, 𝒜, 𝒟, σD, ρ, ξ']
            exact (Category.id_comp _).trans (Category.comp_id _).symm)
      have h1 : θ (ℰ.map f) e = 0 := hf
      have h2 : θ (σD j (Over.mk (𝟙 j))) (θ (ρ j) aj) = 0 := by
        simp only [aj]
        rw [tc', tc', hχ, ← tc', ← tc']
        exact h1
      rw [← inv' (ξ j) (ξ' j) (LimitStage.Hom.ext (by simp [ξ, ξ']) (by simp [ξ, ξ']))
        (θ ((𝒟 j).π (Over.mk (𝟙 j))) (θ (ρ j) aj)), tc' (ξ' j)]
      simp only [σD] at h2
      rw [h2, map_zero]
    obtain ⟨V, φ, hφ⟩ := (hD j).2 (Over.mk (𝟙 j)) (θ (ρ j) aj) hd0
    refine ⟨V.left, V.hom ≫ f, ?_⟩
    have hχ : 𝒜.map (V.hom ≫ f) = (((ψ V).comp ((𝒟 j).map φ)).comp (ρ j)).comp (𝒜.map f) :=
      LimitStage.Hom.ext (by simp [ψ, ρ, 𝒜, 𝒟, ← Over.w φ])
        (by
          simp only [varyingBaseSystem_map_s, Functor.map_comp, LimitStageSystem.mapW_map_s,
            Functor.const_obj_obj, fixedBaseSystem_map_s, Category.comp_id, Category.assoc, 𝒜,
            𝒟, ψ, ρ]
          exact congrArg (S.map V.hom ≫ ·) (Category.id_comp _).symm)
    have hφ' : θ ((𝒟 j).map φ) (θ (ρ j) aj) = 0 := hφ
    change θ (𝒜.map (V.hom ≫ f)) a = 0
    rw [hχ, ← tc', ← tc', ← tc']
    simp only [aj] at hφ'
    rw [hφ', map_zero]

end AlgebraicGeometry.Etale
