/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.IhomComparison
public import WeilConjectures.CategoryTheory.Preadditive.AveragingDuality
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityMap

/-!

# Nearby duality restricted to averaging summands

This file contains the formal part of the slice compatibility of nearby duality (blueprint
`lemma-nearby-duality-slice--1` (2), with `lemma-duality-invariants-pro-p--1`), over abstract
monoidal closed categories.

* **Equivariance** (`CategoryTheory.Verdier.app_comp_nearbyDualityMap_eq`): an endomorphism `σ`
  of `Ψ` which is monoidal and fixes the dualizing map `θ` intertwines the duality map with the
  contragredient action: `σ_{D M} ≫ δ_M = δ_M ≫ D(σ'_M)` for `σ'_M` a left inverse of `σ_M`.
* **Restriction to averaging summands**
  (`CategoryTheory.Verdier.isIso_map_nearbyDualityMap_of_averaging`): in the situation of the
  open restriction `CategoryTheory.Verdier.nearbyDualityMap_restrict`, if the exchange
  `α : F' Ψ_X ⟶ Ψ_U F` is at `M` and at `D M` the inclusion of the summand cut out by the
  averaging idempotent of an action of a finite group `Γ` on `Ψ_U` (by monoidal endomorphisms
  fixing `θ_U`), and the duality maps of `F`, `F'` and `Ψ_U` are isomorphisms, then
  `F'(δ_{X,M})` is an isomorphism.

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory MonoidalCategory MonoidalClosed Opposite

namespace CategoryTheory.Verdier

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [MonoidalClosed C]
  {C' : Type u₂} [Category.{v₂} C'] [MonoidalCategory C'] [MonoidalClosed C']

/-- **Equivariance of the duality map**: if `σ : Ψ ⟶ Ψ` is monoidal for `μ` and fixes `θ`, and
`σ'` is a left inverse of `σ_M`, then `σ_{D M} ≫ δ_M = δ_M ≫ D(σ')`. -/
lemma app_comp_nearbyDualityMap_eq {Ψ : C ⥤ C'} (μ : ∀ A B : C, Ψ.obj A ⊗ Ψ.obj B ⟶ Ψ.obj (A ⊗ B))
    {ω : C} {ω' : C'} (θ : Ψ.obj ω ⟶ ω') (σ : Ψ ⟶ Ψ)
    (hσμ : ∀ A B, (σ.app A ⊗ₘ σ.app B) ≫ μ A B = μ A B ≫ σ.app (A ⊗ B))
    (hσθ : σ.app ω ≫ θ = θ) (M : C) (σ' : Ψ.obj M ⟶ Ψ.obj M) (hσ' : σ' ≫ σ.app M = 𝟙 _) :
    σ.app ((ihom M).obj ω) ≫ nearbyDualityMap μ θ M =
      nearbyDualityMap μ θ M ≫ (pre σ').app ω' := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_pre_app, uncurry_nearbyDualityMap]
  conv_rhs => rw [← hσθ,
    σ.naturality_assoc (X := M ⊗ (ihom M).obj ω) (Y := ω) ((ihom.ev M).app ω),
    ← reassoc_of% (hσμ M ((ihom M).obj ω)), tensorHom_def, Category.assoc,
    ← comp_whiskerRight_assoc, hσ', id_whiskerRight,
    Category.id_comp]

section Averaging

variable {U : Type u₃} [Category.{v₃} U] [MonoidalCategory U] [MonoidalClosed U]
  {U' : Type u₄} [Category.{v₄} U'] [MonoidalCategory U'] [MonoidalClosed U'] [Preadditive U']
  [MonoidalPreadditive U']
  {ΨX : C ⥤ C'} {ΨU : U ⥤ U'} (μX : ∀ A B : C, ΨX.obj A ⊗ ΨX.obj B ⟶ ΨX.obj (A ⊗ B))
  (μU : ∀ A B : U, ΨU.obj A ⊗ ΨU.obj B ⟶ ΨU.obj (A ⊗ B))
  {ωX : C} {ωX' : C'} {ωU : U} {ωU' : U'} (θX : ΨX.obj ωX ⟶ ωX') (θU : ΨU.obj ωU ⟶ ωU')
  {F : C ⥤ U} {F' : C' ⥤ U'} [F.LaxMonoidal] [F'.LaxMonoidal]
  (ρ : F.obj ωX ⟶ ωU) (ρ' : F'.obj ωX' ⟶ ωU')
  (α : ∀ A : C, F'.obj (ΨX.obj A) ⟶ ΨU.obj (F.obj A))

/-- The contravariant internal hom `RHom(-, ω)` into a fixed object is additive. -/
instance additive_internalHom_flip_obj (ω : U') :
    (MonoidalClosed.internalHom.flip.obj ω : U'ᵒᵖ ⥤ U').Additive where
  map_add {_ _ f g} := pre_add_app f.unop g.unop ω

/-- **Nearby duality restricted to averaging summands** (blueprint `lemma-nearby-duality-slice--1`
(2), with `lemma-duality-invariants-pro-p--1`). In the situation of
`CategoryTheory.Verdier.nearbyDualityMap_restrict` (a monoidal exchange `α : F' Ψ_X ⟶ Ψ_U F`
compatible with the dualizing maps), let a finite group `Γ` act on `Ψ_U` by monoidal
endomorphisms `σ a` fixing `θ_U`, with `σ a⁻¹` left inverse to `σ a` on `Ψ_U F M`, and suppose
that `α` is split at `M` and at `D M` by retractions `rᵢ` with `|Γ| • (rᵢ ≫ α) = ∑ₐ σ a`, `|Γ|`
being invertible on `Ψ_U F D M`. If the duality maps of `(F', ρ')` at `Ψ_X M`, of `(F, ρ)` at `M`
and of `(Ψ_U, θ_U)` at `F M` are isomorphisms, then so is `F'(δ_{X,M})`. -/
theorem isIso_map_nearbyDualityMap_of_averaging
    (hμU : ∀ {A A' B B' : U} (x : A ⟶ A') (y : B ⟶ B'),
      (ΨU.map x ⊗ₘ ΨU.map y) ≫ μU A' B' = μU A B ≫ ΨU.map (x ⊗ₘ y))
    (hα : ∀ {A B : C} (g : A ⟶ B), F'.map (ΨX.map g) ≫ α B = α A ≫ ΨU.map (F.map g))
    (hμ : ∀ A B : C, (α A ⊗ₘ α B) ≫ μU _ _ ≫ ΨU.map (Functor.LaxMonoidal.μ F A B) =
      Functor.LaxMonoidal.μ F' _ _ ≫ F'.map (μX A B) ≫ α (A ⊗ B))
    (hθ : F'.map θX ≫ ρ' = α ωX ≫ ΨU.map ρ ≫ θU) (M : C)
    {Γ : Type*} [Group Γ] [Fintype Γ] (σ : Γ → (ΨU ⟶ ΨU))
    (hσμ : ∀ a A B, ((σ a).app A ⊗ₘ (σ a).app B) ≫ μU A B = μU A B ≫ (σ a).app (A ⊗ B))
    (hσθ : ∀ a, (σ a).app ωU ≫ θU = θU)
    (hσinv : ∀ a, (σ a⁻¹).app (F.obj M) ≫ (σ a).app (F.obj M) = 𝟙 _)
    (hn : IsIso (Fintype.card Γ • 𝟙 (ΨU.obj (F.obj ((ihom M).obj ωX)))))
    (r₁ : ΨU.obj (F.obj ((ihom M).obj ωX)) ⟶ F'.obj (ΨX.obj ((ihom M).obj ωX)))
    (h₁ : α _ ≫ r₁ = 𝟙 _) (hρ₁ : Fintype.card Γ • (r₁ ≫ α _) = ∑ a, (σ a).app _)
    (r₂ : ΨU.obj (F.obj M) ⟶ F'.obj (ΨX.obj M))
    (h₂ : α M ≫ r₂ = 𝟙 _) (hρ₂ : Fintype.card Γ • (r₂ ≫ α M) = ∑ a, (σ a).app _)
    (hF' : IsIso (nearbyDualityMap (Functor.LaxMonoidal.μ F') ρ' (ΨX.obj M)))
    (hF : IsIso (nearbyDualityMap (Functor.LaxMonoidal.μ F) ρ M))
    (hU : IsIso (nearbyDualityMap μU θU (F.obj M))) :
    IsIso (F'.map (nearbyDualityMap μX θX M)) := by
  have e := nearbyDualityMap_restrict μX μU θX θU ρ ρ' α hμU hα hμ hθ M
  have hf (a : Γ) : (σ a).app _ ≫ ΨU.map (nearbyDualityMap (Functor.LaxMonoidal.μ F) ρ M) ≫
      nearbyDualityMap μU θU (F.obj M) =
      (ΨU.map (nearbyDualityMap (Functor.LaxMonoidal.μ F) ρ M) ≫
        nearbyDualityMap μU θU (F.obj M)) ≫
        (MonoidalClosed.internalHom.flip.obj ωU').map ((σ a⁻¹).app (F.obj M)).op := by
    rw [← (σ a).naturality_assoc, Category.assoc,
      app_comp_nearbyDualityMap_eq μU θU (σ a) (hσμ a) (hσθ a) (F.obj M) _ (hσinv a)]
    rfl
  have hiso := isIso_comp_comp_map_op_of_averaging
    (MonoidalClosed.internalHom.flip.obj ωU') h₁ hρ₁ h₂ hρ₂ _ hf
  have : IsIso (F'.map (nearbyDualityMap μX θX M) ≫
      nearbyDualityMap (Functor.LaxMonoidal.μ F') ρ' (ΨX.obj M)) := by
    rw [e, ← Category.assoc (ΨU.map _)]
    exact hiso
  exact IsIso.of_isIso_comp_right _ (nearbyDualityMap (Functor.LaxMonoidal.μ F') ρ' (ΨX.obj M))

/-- `CategoryTheory.Verdier.isIso_map_nearbyDualityMap_of_averaging` for an exchange given as a
natural transformation `β : Ψ_X ⋙ F' ⟶ F ⋙ Ψ_U`, when the dualizing objects of the restrictions
are the images `F ω_X` and `F' ω_{X'}` with the identities as comparison maps: the compatibility
of the dualizing maps is `F'(θ_X) = θ ∘ β_{ω_X}`. -/
theorem isIso_map_nearbyDualityMap_of_averaging_of_eq
    (θ : ΨU.obj (F.obj ωX) ⟶ F'.obj ωX') (β : ΨX ⋙ F' ⟶ F ⋙ ΨU)
    (hμU : ∀ {A A' B B' : U} (x : A ⟶ A') (y : B ⟶ B'),
      (ΨU.map x ⊗ₘ ΨU.map y) ≫ μU A' B' = μU A B ≫ ΨU.map (x ⊗ₘ y))
    (hμ : ∀ A B : C, (β.app A ⊗ₘ β.app B) ≫ μU _ _ ≫ ΨU.map (Functor.LaxMonoidal.μ F A B) =
      Functor.LaxMonoidal.μ F' _ _ ≫ F'.map (μX A B) ≫ β.app (A ⊗ B))
    (hθ : F'.map θX = β.app ωX ≫ θ) (M : C)
    {Γ : Type*} [Group Γ] [Fintype Γ] (σ : Γ → (ΨU ⟶ ΨU))
    (hσμ : ∀ a A B, ((σ a).app A ⊗ₘ (σ a).app B) ≫ μU A B = μU A B ≫ (σ a).app (A ⊗ B))
    (hσθ : ∀ a, (σ a).app (F.obj ωX) ≫ θ = θ)
    (hσinv : ∀ a, (σ a⁻¹).app (F.obj M) ≫ (σ a).app (F.obj M) = 𝟙 _)
    (hn : IsIso (Fintype.card Γ • 𝟙 (ΨU.obj (F.obj ((ihom M).obj ωX)))))
    (r₁ : ΨU.obj (F.obj ((ihom M).obj ωX)) ⟶ F'.obj (ΨX.obj ((ihom M).obj ωX)))
    (h₁ : β.app _ ≫ r₁ = 𝟙 _) (hρ₁ : Fintype.card Γ • (r₁ ≫ β.app _) = ∑ a, (σ a).app _)
    (r₂ : ΨU.obj (F.obj M) ⟶ F'.obj (ΨX.obj M))
    (h₂ : β.app M ≫ r₂ = 𝟙 _) (hρ₂ : Fintype.card Γ • (r₂ ≫ β.app M) = ∑ a, (σ a).app _)
    (hF' : IsIso (nearbyDualityMap (Functor.LaxMonoidal.μ F') (𝟙 (F'.obj ωX')) (ΨX.obj M)))
    (hF : IsIso (nearbyDualityMap (Functor.LaxMonoidal.μ F) (𝟙 (F.obj ωX)) M))
    (hU : IsIso (nearbyDualityMap μU θ (F.obj M))) :
    IsIso (F'.map (nearbyDualityMap μX θX M)) :=
  isIso_map_nearbyDualityMap_of_averaging μX μU θX θ (𝟙 _) (𝟙 _) (fun A ↦ β.app A) hμU
    (fun g ↦ β.naturality g) hμ
    (by rw [Category.comp_id, CategoryTheory.Functor.map_id, Category.id_comp, hθ]) M σ hσμ hσθ
    hσinv hn r₁ h₁ hρ₁ r₂ h₂ hρ₂ hF' hF hU

end Averaging

end CategoryTheory.Verdier
