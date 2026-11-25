/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteEtaleTraceGlue

/-!
# Linearity of morphisms of pro-étale module objects is local

Let `g i : W i ⟶ X` be a pro-étale covering family and `M`, `N` module objects over `Λ_X`.
A morphism `f : M ⟶ N` of the underlying sheaves is `Λ_X`-linear as soon as each pullback
`(g i)^* f` is the underlying morphism of a morphism of module objects
`(g i)^* M ⟶ (g i)^* N` (`AlgebraicGeometry.ProEtale.CondensedRing.exists_hom_of_upperStar`).
Combined with the gluing of morphisms of sheaves
(`AlgebraicGeometry.ProEtale.existsUnique_hom_of_localizationRestriction`), this reduces the
construction of morphisms of module objects to the construction of compatible local morphisms.

* `CategoryTheory.Functor.map_smul_comp_eq_of_isModHom`: if `F` is lax monoidal with invertible
  tensor comparison, and `F.map f` is linear for the induced module structures, then `F` maps
  the two sides of the linearity condition of `f` to the same morphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory MonObj Functor.LaxMonoidal

open scoped CategoryTheory.Obj

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  (F : C ⥤ D) [F.LaxMonoidal] {R : C} [MonObj R] {M N : C} [ModObj R M] [ModObj R N]

/-- If `F` is lax monoidal with invertible tensor comparison at `(R, M)` and `F.map f` is linear
for the induced `F.obj R`-module structures, then `F` identifies the two sides of the linearity
condition `γ ≫ f = (R ◁ f) ≫ γ` of `f`. -/
lemma map_smul_comp_eq_of_isModHom [IsIso (Functor.LaxMonoidal.μ F R M)] (f : M ⟶ N)
    [IsModHom (F.obj R) (F.map f)] :
    F.map (γ[R, M] ≫ f) = F.map (R ◁ f ≫ γ[R, N]) := by
  have h := IsModHom.smul_hom (A := F.obj R) (f := F.map f)
  simp only [modObjObj_smul, MonoidalCategory.selfLeftAction_actionHomRight,
    Category.assoc] at h
  rw [← cancel_epi (Functor.LaxMonoidal.μ F R M), F.map_comp, F.map_comp, h,
    μ_natural_right_assoc]

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- If the pullback of a morphism `f` of underlying sheaves is, through the comparisons
`upperStarUnitHom`, the underlying morphism of a morphism of module objects, then it is linear
for the module structures of the pullbacks of the underlying sheaves. -/
lemma isModHom_upperStar_map {X Y : Scheme.{u}} (h : X ⟶ Y)
    {M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
    (f : M.X ⟶ N.X) (φ : (h)^*⟦Λ⟧.obj M ⟶ (h)^*⟦Λ⟧.obj N)
    (hφ : upperStarUnitHom Λ h M ≫ φ.hom =
      (h)^*[Ab.{u + 1}].map f ≫ upperStarUnitHom Λ h N) :
    IsModHom ((h)^*[Ab.{u + 1}].obj (condensedRingObj Λ Y)) ((h)^*[Ab.{u + 1}].map f) := by
  let F := (h)^*[Ab.{u + 1}]
  let M' := (F.mapMod (condensedRingObj Λ Y)).obj M
  let N' := (F.mapMod (condensedRingObj Λ Y)).obj N
  let α := condensedPullbackHom Λ h
  let ψ : M' ⟶ (Mod.comap α).obj ((h)^*⟦Λ⟧.obj N) :=
    Mod.extendUnit α M' ≫ (Mod.comap α).map φ
  have hψ := ψ.isModHom.smul_hom
  have hN := (Mod.extendUnit α N').isModHom.smul_hom
  refine ⟨?_⟩
  rw [← cancel_mono (upperStarUnitHom Λ h N)]
  change γ[F.obj (condensedRingObj Λ Y), M'.X] ≫ F.map f ≫ upperStarUnitHom Λ h N = _
  rw [← hφ]
  erw [hψ]
  rw [show ψ.hom = F.map f ≫ upperStarUnitHom Λ h N from hφ]
  simp only [MonoidalCategory.selfLeftAction_actionHomRight, MonoidalCategory.whiskerLeft_comp,
    Category.assoc] at hN ⊢
  erw [← hN]
  rfl

section Cover

variable {X : Scheme.{u}} {κ : Type*} {W : κ → Scheme.{u}} (g : ∀ i, W i ⟶ X)
  [∀ i, WeaklyEtale (g i)]

/-- **Linearity is local**: a morphism `f` of the underlying sheaves of module objects over
`Λ_X` whose pullbacks along a pro-étale covering family `g i` are, through the comparisons
`upperStarUnitHom`, the underlying morphisms of morphisms `φ i` of module objects, is the
underlying morphism of a morphism of module objects, whose pullbacks are the `φ i`. -/
theorem exists_hom_of_upperStar (hg : Presieve.ofArrows W g ∈ proetalePrecoverage X)
    {M N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)} (f : M.X ⟶ N.X)
    (φ : ∀ i, (g i)^*⟦Λ⟧.obj M ⟶ (g i)^*⟦Λ⟧.obj N)
    (hφ : ∀ i, upperStarUnitHom Λ (g i) M ≫ (φ i).hom =
      (g i)^*[Ab.{u + 1}].map f ≫ upperStarUnitHom Λ (g i) N) :
    ∃ ψ : M ⟶ N, ψ.hom = f ∧ ∀ i, (g i)^*⟦Λ⟧.map ψ = φ i := by
  have : IsModHom (condensedRingObj Λ X) f := ⟨by
    simp only [MonoidalCategory.selfLeftAction_actionHomRight]
    refine ProEtale.hom_ext_of_upperStar Ab.{u + 1} g hg fun i ↦ ?_
    have := isModHom_upperStar_map Λ (g i) f (φ i) (hφ i)
    exact Functor.map_smul_comp_eq_of_isModHom _ f⟩
  refine ⟨⟨f⟩, rfl, fun i ↦ Mod.Hom.ext ?_⟩
  rw [← cancel_epi (upperStarUnitHom Λ (g i) M), upperStarUnitHom_map_hom, hφ i]

/-- The morphism of restrictions of underlying sheaves along a weakly étale `g` induced by a
morphism `φ : g^* M ⟶ g^* N` of pullbacks of module objects, through the comparisons
`upperStarUnitHom` and `ProEtale.upperStarIsoLocalizationRestriction`. -/
noncomputable def localizationRestrictionHom {W : Scheme.{u}} (g : W ⟶ X) [WeaklyEtale g]
    {M N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (φ : (g)^*⟦Λ⟧.obj M ⟶ (g)^*⟦Λ⟧.obj N) :
    (localizationRestriction Ab.{u + 1} g inferInstance).obj M.X ⟶
      (localizationRestriction Ab.{u + 1} g inferInstance).obj N.X :=
  (upperStarIsoLocalizationRestriction Ab.{u + 1} g inferInstance).inv.app M.X ≫
    upperStarUnitHom Λ g M ≫ φ.hom ≫ inv (upperStarUnitHom Λ g N) ≫
    (upperStarIsoLocalizationRestriction Ab.{u + 1} g inferInstance).hom.app N.X

/-- **Gluing of morphisms of pro-étale module objects**: morphisms
`φ i : (g i)^* M ⟶ (g i)^* N` of the pullbacks of module objects along a pro-étale covering
family, whose induced morphisms of restrictions of underlying sheaves are compatible, are the
pullbacks of a unique morphism `M ⟶ N`. -/
theorem existsUnique_hom_of_upperStar (hg : Presieve.ofArrows W g ∈ proetalePrecoverage X)
    {M N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (φ : ∀ i, (g i)^*⟦Λ⟧.obj M ⟶ (g i)^*⟦Λ⟧.obj N)
    (hφ : GlueCompatible g fun i ↦ localizationRestrictionHom Λ (g i) (φ i)) :
    ∃! ψ : M ⟶ N, ∀ i, (g i)^*⟦Λ⟧.map ψ = φ i := by
  obtain ⟨f, hf, -⟩ := existsUnique_hom_of_localizationRestriction hg hφ
  obtain ⟨ψ, -, hψ⟩ := exists_hom_of_upperStar Λ g hg f φ fun i ↦ by
    have h2 : (g i)^*[Ab.{u + 1}].map f = upperStarUnitHom Λ (g i) M ≫ (φ i).hom ≫
        inv (upperStarUnitHom Λ (g i) N) := by
      have := (upperStarIsoLocalizationRestriction Ab.{u + 1} (g i) inferInstance).hom.naturality f
      rw [← cancel_mono ((upperStarIsoLocalizationRestriction Ab.{u + 1} (g i)
        inferInstance).hom.app N.X), this, hf i, localizationRestrictionHom]
      simp
    rw [h2]
    simp
  exact ⟨ψ, hψ, fun ψ' hψ' ↦
    hom_ext_of_upperStar Λ g hg fun i ↦ (hψ' i).trans (hψ i).symm⟩

end Cover

end AlgebraicGeometry.ProEtale.CondensedRing
