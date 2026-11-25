/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.DimensionShift

/-!
# Calculus of transition maps on stalks

Elementwise consequences of the composition law of the transition maps of stages
(`AlgebraicGeometry.Etale.LimitStage.transition_apply_comp`), transport of elementwise colimits
along isomorphisms (`ModuleCat.IsElementwiseColimit.of_iso`), and change of the scheme of
coefficients along a morphism `v : W' ⟶ W` (`AlgebraicGeometry.Etale.LimitStage.mapW`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace ModuleCat.IsElementwiseColimit

variable {R : Type*} [Ring R] {I : Type*} [Category I]

/-- Elementwise colimits are transported along compatible isomorphisms. -/
lemma of_iso {A A' : I → ModuleCat R} {B B' : ModuleCat R} {σ : ∀ i, A i ⟶ B}
    {σ' : ∀ i, A' i ⟶ B'} {τ : ∀ {i j : I}, (i ⟶ j) → (A j ⟶ A i)}
    {τ' : ∀ {i j : I}, (i ⟶ j) → (A' j ⟶ A' i)} (e : ∀ i, A i ≅ A' i) (eB : B ≅ B')
    (hσ : ∀ i, (e i).hom ≫ σ' i = σ i ≫ eB.hom)
    (hτ : ∀ {i j : I} (f : i ⟶ j), (e j).hom ≫ τ' f = τ f ≫ (e i).hom)
    (h' : IsElementwiseColimit A' B' σ' τ') : IsElementwiseColimit A B σ τ := by
  refine ⟨fun b ↦ ?_, fun i a ha ↦ ?_⟩
  · obtain ⟨i, a', ha'⟩ := h'.1 (eB.hom.hom b)
    refine ⟨i, (e i).inv.hom a', ?_⟩
    apply (ConcreteCategory.injective_of_mono_of_preservesPullback eB.hom)
    rw [← ModuleCat.comp_apply, ← hσ, ModuleCat.comp_apply, ← ModuleCat.comp_apply (e i).inv,
      Iso.inv_hom_id, ModuleCat.id_apply, ha']
  · have h0 : (σ' i).hom ((e i).hom.hom a) = 0 := by
      rw [← ModuleCat.comp_apply, hσ, ModuleCat.comp_apply, ha, map_zero]
    obtain ⟨j, f, hf⟩ := h'.2 i _ h0
    refine ⟨j, f, ?_⟩
    apply (ConcreteCategory.injective_of_mono_of_preservesPullback (e j).hom)
    rw [← ModuleCat.comp_apply, ← hτ, ModuleCat.comp_apply, hf, map_zero]

end ModuleCat.IsElementwiseColimit

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

namespace LimitStage

variable {B W : Scheme.{u}}

/-- The composition law of the transition maps, applied to elements of stalks. -/
lemma transition_apply_comp (q : ℤ) (x : B)
    (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {α β γ : LimitStage B W} (φ : Hom α β) (ψ : Hom β γ) (χ : Hom α γ) (h : φ.comp ψ = χ)
    (y : (stalkHomology Λ q x).obj ((functor Λ γ).obj K)) :
    ((stalkHomology Λ q x).map ((transition Λ φ).app K)).hom
        (((stalkHomology Λ q x).map ((transition Λ ψ).app K)).hom y) =
      ((stalkHomology Λ q x).map ((transition Λ χ).app K)).hom y := by
  subst h
  rw [← ModuleCat.comp_apply, ← Functor.map_comp, ← NatTrans.comp_app, transition_comp]

/-- The transition maps of a pair of mutually inverse morphisms of stages are inverse. -/
lemma transition_apply_inv (q : ℤ) (x : B)
    (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {α β : LimitStage B W} (φ : Hom α β) (ψ : Hom β α) (h : φ.comp ψ = Hom.id α)
    (y : (stalkHomology Λ q x).obj ((functor Λ α).obj K)) :
    ((stalkHomology Λ q x).map ((transition Λ φ).app K)).hom
        (((stalkHomology Λ q x).map ((transition Λ ψ).app K)).hom y) = y := by
  rw [transition_apply_comp Λ q x K φ ψ _ h, transition_id, NatTrans.id_app,
    CategoryTheory.Functor.map_id]
  rfl

section MapW

variable {W' : Scheme.{u}} (v : W' ⟶ W)

/-- Change of the scheme of coefficients: the stage `(T, S, g, π, w ≫ v)`. -/
abbrev mapW (α : LimitStage B W') : LimitStage B W := ⟨α.T, α.S, α.g, α.π, α.w ≫ v⟩

/-- Change of the scheme of coefficients for morphisms of stages. -/
abbrev Hom.mapW {α β : LimitStage B W'} (φ : Hom α β) : Hom (α.mapW v) (β.mapW v) :=
  ⟨φ.t, φ.s, φ.wg, φ.wπ, by rw [← Category.assoc, φ.ww]⟩

/-- `π^* Rg_* (w ≫ v)^* K ≅ π^* Rg_* w^* (v^* K)`. -/
noncomputable def mapWIso (α : LimitStage B W')
    (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (functor Λ (α.mapW v)).obj K ≅ (functor Λ α).obj (D+((v)^*[ModuleCat.{u + 1} Λ]).obj K) :=
  D+((α.π)^*[ModuleCat.{u + 1} Λ]).mapIso (R+((α.g)_*[ModuleCat.{u + 1} Λ]).mapIso
    ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) α.w v (α.w ≫ v) rfl).app K))

lemma transition_mapW {α β : LimitStage B W'} (φ : Hom α β)
    (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (transition Λ (φ.mapW v)).app K ≫ (mapWIso Λ v α K).hom =
      (mapWIso Λ v β K).hom ≫ (transition Λ φ).app (D+((v)^*[ModuleCat.{u + 1} Λ]).obj K) := by
  have hA := NatTrans.congr_app (Etale.upperStarCompDerivedPlus_assoc (ModuleCat.{u + 1} Λ)
    φ.t β.w v α.w (β.w ≫ v) (α.w ≫ v) φ.ww.symm rfl rfl) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hA
  have h3 : (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) φ.t (β.w ≫ v) (α.w ≫ v)
        (φ.mapW v).ww.symm).inv.app K ≫
      (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) α.w v (α.w ≫ v) rfl).hom.app K =
      D+((φ.t)^*[ModuleCat.{u + 1} Λ]).map
          ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) β.w v (β.w ≫ v) rfl).hom.app K) ≫
        (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) φ.t β.w α.w φ.ww.symm).inv.app
          (D+((v)^*[ModuleCat.{u + 1} Λ]).obj K) := by
    rw [← cancel_epi ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) φ.t (β.w ≫ v) (α.w ≫ v)
      (φ.mapW v).ww.symm).hom.app K), Iso.hom_inv_id_app_assoc, reassoc_of% hA,
      Iso.hom_inv_id_app, Category.comp_id]
  have n1 := (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) α.π φ.s β.π φ.wπ.symm).hom.naturality
    (R+((β.g)_*[ModuleCat.{u + 1} Λ]).map
      ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) β.w v (β.w ≫ v) rfl).hom.app K))
  have n2 := congrArg D+((α.π)^*[ModuleCat.{u + 1} Λ]).map
    ((Etale.baseChange (ModuleCat.{u + 1} Λ) ⟨φ.wg⟩).naturality
      ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) β.w v (β.w ≫ v) rfl).hom.app K))
  have n3 := congrArg (fun x ↦ D+((α.π)^*[ModuleCat.{u + 1} Λ]).map
    (R+((α.g)_*[ModuleCat.{u + 1} Λ]).map x)) h3
  simp only [Functor.comp_map, Functor.map_comp] at n1 n2 n3
  simp only [transition_app, mapWIso, Functor.mapIso_hom, Iso.app_hom, Functor.map_comp,
    Category.assoc]
  rw [reassoc_of% n1, reassoc_of% n2, n3]

end MapW

end LimitStage

namespace LimitStageSystem

variable {B W : Scheme.{u}} {I : Type u} [Category.{u} I]

variable {Λ}

/-- Being a stalkwise colimit only depends on the complex up to isomorphism. -/
lemma isStalkColimit_of_iso (𝒮 : LimitStageSystem B W I)
    {K K' : DerivedCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (e : K ≅ K')
    {q : ℤ} (h : 𝒮.IsStalkColimit Λ K' q) : 𝒮.IsStalkColimit Λ K q := fun x ↦
  ModuleCat.IsElementwiseColimit.of_iso
    (fun i ↦ (stalkHomology Λ q x).mapIso ((LimitStage.functor Λ (𝒮.obj i)).mapIso e))
    ((stalkHomology Λ q x).mapIso ((LimitStage.functor Λ 𝒮.pt).mapIso e))
    (fun i ↦ by
      simp only [Functor.mapIso_hom, ← Functor.map_comp]
      rw [(LimitStage.transition Λ (𝒮.π i)).naturality])
    (fun f ↦ by
      simp only [Functor.mapIso_hom, ← Functor.map_comp]
      rw [(LimitStage.transition Λ (𝒮.map f)).naturality])
    (h x)

variable {W' : Scheme.{u}} (v : W' ⟶ W)

/-- Change of the scheme of coefficients of a system of stages along `v : W' ⟶ W`. -/
@[simps]
def mapW (𝒮 : LimitStageSystem B W' I) : LimitStageSystem B W I where
  obj i := (𝒮.obj i).mapW v
  map f := (𝒮.map f).mapW v
  map_id i := LimitStage.Hom.ext (by rw [𝒮.map_id]) (by rw [𝒮.map_id])
  map_comp f g := LimitStage.Hom.ext (by rw [𝒮.map_comp]) (by rw [𝒮.map_comp])
  pt := 𝒮.pt.mapW v
  π i := (𝒮.π i).mapW v
  w f := LimitStage.Hom.ext (by rw [← 𝒮.w f]) (by rw [← 𝒮.w f])

/-- A system is a stalkwise colimit at `K` after change of coefficients along `v` as soon as it
is one at `v^* K` before. -/
lemma isStalkColimit_mapW (𝒮 : LimitStageSystem B W' I)
    {K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))} {q : ℤ}
    (h : 𝒮.IsStalkColimit Λ (D+((v)^*[ModuleCat.{u + 1} Λ]).obj K) q) :
    (𝒮.mapW v).IsStalkColimit Λ K q := fun x ↦
  ModuleCat.IsElementwiseColimit.of_iso
    (fun i ↦ (stalkHomology Λ q x).mapIso (LimitStage.mapWIso Λ v (𝒮.obj i) K))
    ((stalkHomology Λ q x).mapIso (LimitStage.mapWIso Λ v 𝒮.pt K))
    (fun i ↦ by
      simp only [Functor.mapIso_hom, ← Functor.map_comp]
      exact congrArg (stalkHomology Λ q x).map (LimitStage.transition_mapW Λ v (𝒮.π i) K).symm)
    (fun f ↦ by
      simp only [Functor.mapIso_hom, ← Functor.map_comp]
      exact congrArg (stalkHomology Λ q x).map (LimitStage.transition_mapW Λ v (𝒮.map f) K).symm)
    (h x)

end LimitStageSystem

end AlgebraicGeometry.Etale
