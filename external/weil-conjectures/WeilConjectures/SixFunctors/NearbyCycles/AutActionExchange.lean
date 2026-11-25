/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.AutActionTrivial
public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayerMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence

/-!

# The action of self-maps of models and the exchange morphisms

Let `τ : M ⟶ N` be a morphism of models over `f, f'`, and `s : M ⟶ M`, `s' : N ⟶ N` morphisms of
models over the identities with `s ≫ τ = τ ≫ s'` on total spaces and geometric generic fibres.
Then the exchanges of `τ` intertwine the actions of `s` and `s'` on nearby cycles
(`NearbyCyclesModel.Hom.autAction`):

* `α_τ(C) ≫ ρ(s)(Lf^* C) = Lf'^*(ρ(s')(C)) ≫ α_τ(C)` for the pullback exchange
  (`NearbyCyclesModel.Hom.pullbackExchange_app_comp_autAction_of_comm`, from
  `WeilConjectures.SixFunctors.NearbyCycles.GaloisLayerMap`);
* `χ_τ(E) ≫ Rf'_*(ρ(s)(E)) = ρ(s')(Rf_* E) ≫ χ_τ(E)` for the pushforward exchange
  (`NearbyCyclesModel.Hom.pushforwardExchange_app_comp_map_autAction`).

Moreover the action of a self-map fixes the specialization unit
(`NearbyCyclesModel.Hom.unit_comp_autAction`).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

/-- A transformation `χ : R₁ ⋙ G ⟶ H ⋙ R₂` with the counit property of the mate of
`α : G ⋙ L₂ ⟶ L₁ ⋙ H` intertwines endomorphisms `β` of `H` (natural) and `β'` of `G` which
`α` intertwines:
if `α(B) ≫ β(L₁ B) = L₂(β'(B)) ≫ α(B)` for all `B`, then
`χ(E) ≫ R₂(β(E)) = β'(R₁ E) ≫ χ(E)`. -/
lemma comp_map_of_comp_of_map_comp_counit {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂]
    [Category D₁] [Category D₂] {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁} {L₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) {G : C₁ ⥤ C₂} {H : D₁ ⥤ D₂} (α : G ⋙ L₂ ⟶ L₁ ⋙ H)
    (χ : ∀ E, G.obj (R₁.obj E) ⟶ R₂.obj (H.obj E))
    (hχ : ∀ E, L₂.map (χ E) ≫ adj₂.counit.app (H.obj E) =
      α.app (R₁.obj E) ≫ H.map (adj₁.counit.app E))
    (β : ∀ E, H.obj E ⟶ H.obj E) (hβ : ∀ {E E' : D₁} (g : E ⟶ E'), β E ≫ H.map g = H.map g ≫ β E')
    (β' : ∀ B, G.obj B ⟶ G.obj B) (h : ∀ B, α.app B ≫ β (L₁.obj B) = L₂.map (β' B) ≫ α.app B)
    (E : D₁) :
    χ E ≫ R₂.map (β E) = β' (R₁.obj E) ≫ χ E := by
  apply (adj₂.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, L₂.map_comp, L₂.map_comp,
    Category.assoc, Category.assoc, adj₂.counit_naturality, ← Category.assoc,
    hχ, Category.assoc]
  erw [← hβ]
  rw [← Category.assoc, h, Category.assoc]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

namespace Hom

/-- **The pushforward exchange intertwines the actions of self-maps**: if `s ≫ τ = τ ≫ s'` on
total spaces and geometric generic fibres, then `χ_τ(E) ≫ Rf'_*(ρ(s)(E)) = ρ(s')(Rf_* E) ≫ χ_τ(E)`.
-/
lemma pushforwardExchange_app_comp_map_autAction (τ : M.Hom N f f') (s : M.Hom M (𝟙 X) (𝟙 X'))
    (s' : N.Hom N (𝟙 Y) (𝟙 Y')) (htot : s.total ≫ τ.total = τ.total ≫ s'.total)
    (hgen : s.generic ≫ τ.generic = τ.generic ≫ s'.generic)
    (E : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (τ.pushforwardExchange Λ).app E ≫ R((f')_*⟦Λ⟧).map (s.autAction Λ E) =
      s'.autAction Λ (R((f)_*⟦Λ⟧).obj E) ≫ (τ.pushforwardExchange Λ).app E := by
  exact comp_map_of_comp_of_map_comp_counit (G := N.nearbyCycles Λ) (H := M.nearbyCycles Λ)
    (derivedUpperStarLowerStarAdjunction Λ f)
    (derivedUpperStarLowerStarAdjunction Λ f') (τ.pullbackExchange Λ)
    (fun E ↦ (τ.pushforwardExchange Λ).app E) (τ.map_pushforwardExchange_app_comp_counit_app Λ)
    (s.autAction Λ)
    (s.autAction_naturality Λ) (s'.autAction Λ)
    (τ.pullbackExchange_app_comp_autAction_of_comm Λ s s' htot hgen) E

/-- The diagram chase behind `NearbyCyclesModel.Hom.unit_comp_autAction`. -/
private lemma unit_comp_autAction_aux {D D' : Type*} [Category D] [Category D'] (Ψ : D ⥤ D')
    {I : D ⥤ D} {I' : D' ⥤ D'} (e : I ≅ 𝟭 D) (e' : I' ≅ 𝟭 D') {A : D} {B : D'}
    (u : B ⟶ Ψ.obj A) (α : Ψ ⋙ I' ⟶ I ⋙ Ψ)
    (h : I'.map u ≫ α.app A = (e'.app B).hom ≫ u ≫ Ψ.map (e.app A).inv) :
    u ≫ e'.inv.app (Ψ.obj A) ≫ α.app A ≫ Ψ.map (e.hom.app A) = u := by
  have hn := e'.inv.naturality u
  simp only [Functor.id_map, Functor.id_obj] at hn
  rw [← Category.assoc, hn, Category.assoc, reassoc_of% h]
  simp

/-- **The action of a self-map fixes the specialization unit**: `σ_M ≫ ρ(s)(Λ) = σ_M`. -/
lemma unit_comp_autAction (s : M.Hom M (𝟙 X) (𝟙 X')) :
    M.unit Λ ≫ s.autAction Λ (𝟙_ _) = M.unit Λ := by
  have h := s.map_unit_comp_pullbackExchange_app Λ
  have hU : leftDerivedUpperStarUnitIso Λ (𝟙 X) = (leftDerivedUpperStarId Λ X).app (𝟙_ _) :=
    Iso.ext (leftDerivedUpperStarId_hom_app_unit Λ X).symm
  have hU' : leftDerivedUpperStarUnitIso Λ (𝟙 X') = (leftDerivedUpperStarId Λ X').app (𝟙_ _) :=
    Iso.ext (leftDerivedUpperStarId_hom_app_unit Λ X').symm
  rw [hU, hU'] at h
  exact unit_comp_autAction_aux (M.nearbyCycles Λ) (leftDerivedUpperStarId Λ X)
    (leftDerivedUpperStarId Λ X') (M.unit Λ) (s.pullbackExchange Λ) h

end Hom

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
