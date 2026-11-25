/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayer

/-!

# The Galois action on nearby cycles

Let `N` be a model of `X` with special fibre `X'`, let `h : N.generic ⟶ Spec L` be a morphism to
the spectrum of a field and let `Ω/L` be a field extension, possibly infinite. The group
`Aut(Ω/L)` acts on the Galois layer `N_Ω` (`NearbyCyclesModel.galoisLayer`), the model with the
total space and special fibre of `N` and generic fibre `N.generic ×_{Spec L} Spec Ω`, through
`Spec σ` on the second factor (`NearbyCyclesModel.galoisLayerAut`). This induces an action on the
nearby cycles `Ψ_{N_Ω}` (`NearbyCyclesModel.galoisLayerAction`), by the pullback exchange of the
automorphism of models (`NearbyCyclesModel.Hom.autAction`).

For a model `N` over a strictly henselian trait `S` whose generic fibre lies over the generic point
`η = Spec K` of `S`, and `Ω` a separable closure of `K`, this is the action of the inertia group
`I = Gal(K^sep/K)` on the geometric nearby cycles `RΨ = ī^* Rj̄_*` of SGA 7 XIII 1.3, by
functoriality of the construction in automorphisms of `η̄` over `η`.

## Main results

- `NearbyCyclesModel.galoisLayerAction_one`, `NearbyCyclesModel.galoisLayerAction_mul`: this is a
  (right) action of the group `Aut(Ω/L)`.
- `NearbyCyclesModel.Hom.pullbackExchange_app_comp_autAction`: an automorphism of models which
  does not change a morphism of models `ψ` fixes the pullback exchange of `ψ`.
- `NearbyCyclesModel.pullbackExchange_galoisLayerHom_app_comp_galoisLayerAction`: the pullback
  exchange `L(𝟙)^* Ψ_N ⟶ Ψ_{N_Ω} L(𝟙)^*` of the projection `N_Ω ⟶ N` lands in the invariants of
  the action.

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The diagram chase behind `NearbyCyclesModel.Hom.pullbackExchange_app_comp_autAction`, for
abstract functors: `I₀ : L₀ ≅ 𝟭`, `I : L ≅ 𝟭` (pullbacks along identities), `L'` (a pullback),
`Ψ`, `Ψ'` (nearby cycles) and exchanges `ασ`, `αψ` satisfying the composition law `hx`. -/
private lemma pullbackExchange_comp_autAction_aux {D D' E E' : Type*} [Category D]
    [Category D'] [Category E] [Category E'] {L₀ : D ⥤ D} {L : D' ⥤ D'} (Lf : E ⥤ D)
    (Lf' : E' ⥤ D') (I₀ : L₀ ≅ 𝟭 D) (I : L ≅ 𝟭 D') (Ψ : D ⥤ D') (Ψ' : E ⥤ E')
    (ασ : Ψ ⋙ L ⟶ L₀ ⋙ Ψ) (αψ : Ψ' ⋙ Lf' ⟶ Lf ⋙ Ψ) (c₀ : Lf ⟶ Lf ⋙ L₀) (c : Lf' ⟶ Lf' ⋙ L)
    (C : E)
    (hx : αψ.app C ≫ Ψ.map (c₀.app C) =
      c.app (Ψ'.obj C) ≫ L.map (αψ.app C) ≫ ασ.app (Lf.obj C))
    (hc : c₀.app C ≫ I₀.hom.app (Lf.obj C) = 𝟙 _)
    (hd : c.app (Ψ'.obj C) ≫ I.hom.app (Lf'.obj (Ψ'.obj C)) = 𝟙 _) :
    αψ.app C ≫ (I.inv.app (Ψ.obj (Lf.obj C)) ≫ ασ.app (Lf.obj C) ≫
      Ψ.map (I₀.hom.app (Lf.obj C))) = αψ.app C := by
  have hd' : c.app (Ψ'.obj C) = I.inv.app (Lf'.obj (Ψ'.obj C)) := by
    rw [← cancel_mono (I.hom.app (Lf'.obj (Ψ'.obj C))), hd, Iso.inv_hom_id_app]
    rfl
  have hb : αψ.app C ≫ I.inv.app (Ψ.obj (Lf.obj C)) =
      I.inv.app (Lf'.obj (Ψ'.obj C)) ≫ L.map (αψ.app C) := by
    simpa using I.inv.naturality (αψ.app C)
  calc αψ.app C ≫ (I.inv.app (Ψ.obj (Lf.obj C)) ≫ ασ.app (Lf.obj C) ≫
        Ψ.map (I₀.hom.app (Lf.obj C)))
      = (c.app (Ψ'.obj C) ≫ L.map (αψ.app C) ≫ ασ.app (Lf.obj C)) ≫
          Ψ.map (I₀.hom.app (Lf.obj C)) := by
        rw [hd', ← Category.assoc, hb]; simp only [Category.assoc]
    _ = αψ.app C ≫ Ψ.map (c₀.app C ≫ I₀.hom.app (Lf.obj C)) := by
        rw [← hx, Category.assoc, Ψ.map_comp]
    _ = αψ.app C := by simp [hc]

variable {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- **An automorphism which does not change a morphism of models fixes its pullback exchange.**
If `σ : M ⟶ M` over the identities and `ψ : M ⟶ N` satisfy `σ ≫ ψ = ψ` on total spaces and
geometric generic fibres, then the pullback exchange `α_ψ : Lf'^* Ψ_N C ⟶ Ψ_M (Lf^* C)` followed
by the action of `σ` is `α_ψ`. -/
lemma Hom.pullbackExchange_app_comp_autAction (σ : M.Hom M (𝟙 X) (𝟙 X')) (ψ : M.Hom N f f')
    (htot : σ.total ≫ ψ.total = ψ.total) (hgen : σ.generic ≫ ψ.generic = ψ.generic)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (ψ.pullbackExchange Λ).app C ≫ σ.autAction Λ (L((f)^*⟦Λ⟧).obj C) =
      (ψ.pullbackExchange Λ).app C := by
  have hx := σ.pullbackExchange_comp_app_of_eq Λ ψ ψ (Category.id_comp f)
    (Category.id_comp f') htot hgen C
  have hc := leftDerivedUpperStarCompOfEq_hom_app_comp_leftDerivedUpperStarId Λ
    (Category.id_comp f) C
  have hd := leftDerivedUpperStarCompOfEq_hom_app_comp_leftDerivedUpperStarId Λ
    (Category.id_comp f') ((N.nearbyCycles Λ).obj C)
  rw [eqToHom_refl] at hc hd
  exact pullbackExchange_comp_autAction_aux L((f)^*⟦Λ⟧) L((f')^*⟦Λ⟧)
    (leftDerivedUpperStarId Λ X) (leftDerivedUpperStarId Λ X') (M.nearbyCycles Λ)
    (N.nearbyCycles Λ) (σ.pullbackExchange Λ) (ψ.pullbackExchange Λ)
    (leftDerivedUpperStarCompOfEq Λ (Category.id_comp f)).hom
    (leftDerivedUpperStarCompOfEq Λ (Category.id_comp f')).hom C hx hc hd

variable (N : NearbyCyclesModel X X') {L : Type u} [Field L] (h : N.generic ⟶ Spec (.of L))
  (Ω : Type u) [Field Ω] [Algebra L Ω]

/-- **The Galois action on nearby cycles**: `σ ∈ Aut(Ω/L)` acts on the nearby cycles
`Ψ_{N_Ω} C` of the Galois layer `N_Ω` by the pullback exchange of the automorphism of models
`NearbyCyclesModel.galoisLayerAut` (identity on the total space, `Spec σ` on the generic fibre
`N.generic ×_{Spec L} Spec Ω`). -/
noncomputable def galoisLayerAction (σ : Ω ≃ₐ[L] Ω)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    ((N.galoisLayer h Ω).nearbyCycles Λ).obj C ⟶ ((N.galoisLayer h Ω).nearbyCycles Λ).obj C :=
  (N.galoisLayerAut h Ω σ).autAction Λ C

/-- The Galois action is natural in the complex. -/
@[reassoc]
lemma galoisLayerAction_naturality (σ : Ω ≃ₐ[L] Ω)
    {C C' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (φ : C ⟶ C') :
    N.galoisLayerAction Λ h Ω σ C ≫ ((N.galoisLayer h Ω).nearbyCycles Λ).map φ =
      ((N.galoisLayer h Ω).nearbyCycles Λ).map φ ≫ N.galoisLayerAction Λ h Ω σ C' :=
  Hom.autAction_naturality Λ _ φ

/-- The identity of `Ω` acts trivially. -/
@[simp]
lemma galoisLayerAction_one
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    N.galoisLayerAction Λ h Ω 1 C = 𝟙 _ := by
  refine Hom.autAction_of_eq_id Λ _ rfl ?_ C
  refine Limits.pullback.hom_ext ?_ ?_
  · simp
  · simp only [galoisLayerAut_generic, pullbackAction_snd, Category.id_comp]
    have h1 : specGaloisAction L Ω (1 : Ω ≃ₐ[L] Ω) = 𝟙 _ := by
      rw [specGaloisAction]
      exact Spec.map_id _
    rw [h1]
    exact Category.comp_id _

/-- **The Galois action is a right action**: `σ * τ` acts as `τ` followed by `σ`. -/
lemma galoisLayerAction_mul (σ τ : Ω ≃ₐ[L] Ω)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    N.galoisLayerAction Λ h Ω (σ * τ) C =
      N.galoisLayerAction Λ h Ω τ C ≫ N.galoisLayerAction Λ h Ω σ C :=
  N.galoisLayerAut_autAction_mul h Ω Λ σ τ C

/-- The Galois action is by automorphisms. -/
@[reassoc (attr := simp)]
lemma galoisLayerAction_inv_comp (σ : Ω ≃ₐ[L] Ω)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    N.galoisLayerAction Λ h Ω σ C ≫ N.galoisLayerAction Λ h Ω σ⁻¹ C = 𝟙 _ := by
  rw [← galoisLayerAction_mul, inv_mul_cancel, galoisLayerAction_one]

/-- **The exchange of the projection lands in the invariants**: the pullback exchange
`α : L(𝟙)^* Ψ_N C ⟶ Ψ_{N_Ω} (L(𝟙)^* C)` of the projection `N_Ω ⟶ N` followed by the action of
any `σ ∈ Aut(Ω/L)` is `α`. -/
lemma pullbackExchange_galoisLayerHom_app_comp_galoisLayerAction (σ : Ω ≃ₐ[L] Ω)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    ((N.galoisLayerHom h Ω).pullbackExchange Λ).app C ≫
        N.galoisLayerAction Λ h Ω σ (L((𝟙 X)^*⟦Λ⟧).obj C) =
      ((N.galoisLayerHom h Ω).pullbackExchange Λ).app C :=
  Hom.pullbackExchange_app_comp_autAction Λ _ _ (Category.id_comp _)
    (by simp [galoisLayerAut]) C

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
