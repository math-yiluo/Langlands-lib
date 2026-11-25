/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.AutActionTrivial
public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeId

/-!

# The action of morphisms of models on nearby cycles is multiplicative

For morphisms of models `σ, τ : M ⟶ M` over the identities, the action on nearby cycles
(`NearbyCyclesModel.Hom.autAction`) of a morphism `χ` whose components are the composites of those
of `σ` and `τ` is the composite of the actions, `τ` first
(`NearbyCyclesModel.Hom.autAction_comp_of_eq`), and a morphism of models with identity components
acts trivially (`NearbyCyclesModel.Hom.autAction_of_eq_id`). Both follow from the composition law
of the pullback exchanges (`NearbyCyclesModel.Hom.pullbackExchange_comp_app_of_eq`).

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' : Scheme.{u}} {M : NearbyCyclesModel X X'}

/-- A morphism of models over the identities whose components are identities acts trivially on
nearby cycles. -/
lemma Hom.autAction_of_eq_id (σ : M.Hom M (𝟙 X) (𝟙 X')) (ht : σ.total = 𝟙 _)
    (hg : σ.generic = 𝟙 _)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    σ.autAction Λ A = 𝟙 _ := by
  rw [Hom.autAction, Hom.pullbackExchange_app_of_eq_id Λ M σ ht hg A, Category.assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app]
  exact ((leftDerivedUpperStarId Λ X').inv_hom_id_app_assoc _ _).trans
    ((M.nearbyCycles Λ).map_id _)

/-- The diagram chase behind `NearbyCyclesModel.Hom.autAction_comp_of_eq`, for abstract functors:
`L₀ ≅ 𝟭`, `L ≅ 𝟭` (the pullbacks along identities), `Ψ` (the nearby cycles) and transformations
`α : Ψ ⋙ L ⟶ L₀ ⋙ Ψ` (the pullback exchanges) satisfying the composition law `hx`. -/
private lemma autAction_comp_aux {D D' : Type*} [Category D] [Category D'] {L₀ : D ⥤ D}
    {L : D' ⥤ D'} (I₀ : L₀ ≅ 𝟭 D) (I : L ≅ 𝟭 D') (Ψ : D ⥤ D') (ασ ατ αχ : Ψ ⋙ L ⟶ L₀ ⋙ Ψ)
    (c₀ : L₀ ⟶ L₀ ⋙ L₀) (c : L ⟶ L ⋙ L) (C : D)
    (hx : αχ.app C ≫ Ψ.map (c₀.app C) =
      c.app (Ψ.obj C) ≫ L.map (ατ.app C) ≫ ασ.app (L₀.obj C))
    (hc : c₀.app C ≫ I₀.hom.app (L₀.obj C) = 𝟙 _)
    (hd : c.app (Ψ.obj C) ≫ I.hom.app (L.obj (Ψ.obj C)) = 𝟙 _) :
    I.inv.app (Ψ.obj C) ≫ αχ.app C ≫ Ψ.map (I₀.hom.app C) =
      (I.inv.app (Ψ.obj C) ≫ ατ.app C ≫ Ψ.map (I₀.hom.app C)) ≫
        I.inv.app (Ψ.obj C) ≫ ασ.app C ≫ Ψ.map (I₀.hom.app C) := by
  have hc' : c₀.app C = I₀.inv.app (L₀.obj C) := by
    rw [← cancel_mono (I₀.hom.app (L₀.obj C)), hc, Iso.inv_hom_id_app]
    rfl
  have hd' : c.app (Ψ.obj C) = I.inv.app (L.obj (Ψ.obj C)) := by
    rw [← cancel_mono (I.hom.app (L.obj (Ψ.obj C))), hd, Iso.inv_hom_id_app]
    rfl
  have hχ : αχ.app C = I.inv.app (L.obj (Ψ.obj C)) ≫ L.map (ατ.app C) ≫ ασ.app (L₀.obj C) ≫
      Ψ.map (I₀.hom.app (L₀.obj C)) := by
    rw [← hd', ← reassoc_of% hx, hc', ← Ψ.map_comp, Iso.inv_hom_id_app]
    simp
  have hu : Ψ.map (I₀.hom.app (L₀.obj C)) ≫ Ψ.map (I₀.hom.app C) =
      Ψ.map (L₀.map (I₀.hom.app C)) ≫ Ψ.map (I₀.hom.app C) := by
    rw [← Ψ.map_comp, ← Ψ.map_comp]
    congr 1
    exact (I₀.hom.naturality (I₀.hom.app C)).symm
  have hs := ασ.naturality (I₀.hom.app C)
  have hb := I.inv.naturality (ατ.app C ≫ Ψ.map (I₀.hom.app C))
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map,
    Functor.map_comp, Category.assoc] at hs hb
  rw [hχ]
  simp only [Category.assoc]
  rw [hu, ← reassoc_of% hs, reassoc_of% hb.symm]

/-- **The action of morphisms of models over the identities is multiplicative**: if the
components of `χ` are the composites of those of `σ` and `τ`, then `χ` acts on nearby cycles as
`τ` followed by `σ`. -/
lemma Hom.autAction_comp_of_eq (σ τ χ : M.Hom M (𝟙 X) (𝟙 X'))
    (htot : σ.total ≫ τ.total = χ.total) (hgen : σ.generic ≫ τ.generic = χ.generic)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    χ.autAction Λ C = τ.autAction Λ C ≫ σ.autAction Λ C := by
  have hx := σ.pullbackExchange_comp_app_of_eq Λ τ χ (Category.id_comp (𝟙 X))
    (Category.id_comp (𝟙 X')) htot hgen C
  have hc := leftDerivedUpperStarCompOfEq_hom_app_comp_leftDerivedUpperStarId Λ
    (Category.id_comp (𝟙 X)) C
  have hd := leftDerivedUpperStarCompOfEq_hom_app_comp_leftDerivedUpperStarId Λ
    (Category.id_comp (𝟙 X')) ((M.nearbyCycles Λ).obj C)
  rw [eqToHom_refl] at hc hd
  exact autAction_comp_aux (leftDerivedUpperStarId Λ X) (leftDerivedUpperStarId Λ X')
    (M.nearbyCycles Λ) (σ.pullbackExchange Λ) (τ.pullbackExchange Λ) (χ.pullbackExchange Λ)
    (leftDerivedUpperStarCompOfEq Λ (Category.id_comp (𝟙 X))).hom
    (leftDerivedUpperStarCompOfEq Λ (Category.id_comp (𝟙 X'))).hom C hx hc hd

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
