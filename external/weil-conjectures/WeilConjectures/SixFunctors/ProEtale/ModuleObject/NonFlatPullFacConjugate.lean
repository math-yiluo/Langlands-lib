/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Conjugates of composition isomorphisms of derived adjunctions and counits

Let `L_φ ⊣ R_φ`, `L_ψ ⊣ R_ψ` and `L_χ ⊣ R_χ` be adjunctions between "derived" categories `D_•`,
induced by adjunctions `E_φ ⊣ C_φ`, `E_ψ ⊣ C_ψ` and `E_χ ⊣ C_χ` between "homotopy" categories
`H_•` along functors `Q : H_• ⥤ D_•`, in the sense that the units are compatible with counits
`κ : Q ⋙ L ⟶ E ⋙ Q` and isomorphisms `σ : Q ⋙ R ≅ C ⋙ Q`. Given an isomorphism
`β : R_ψ ⋙ R_φ ≅ R_χ` induced by maps `ρ : C_χ ⟶ C_ψ ⋙ C_φ`, we show that the conjugate
isomorphism `L_χ ≅ L_φ ⋙ L_ψ` is compatible with the counits, through maps `j : E_φ ⋙ E_ψ ⟶ E_χ`
conjugate to `ρ` (`CategoryTheory.Adjunction.conjugateIsoEquiv_symm_inv_app_comp_counit`).

This applies to the transitivity isomorphism of the derived extensions of scalars of module
objects, whose restrictions of scalars are exact.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Adjunction

variable {H_R H_S H_T D_R D_S D_T : Type*} [Category* H_R] [Category* H_S] [Category* H_T]
  [Category* D_R] [Category* D_S] [Category* D_T]
  {Q_R : H_R ⥤ D_R} {Q_S : H_S ⥤ D_S} {Q_T : H_T ⥤ D_T}
  {E_φ : H_R ⥤ H_S} {E_ψ : H_S ⥤ H_T} {E_χ : H_R ⥤ H_T}
  {C_φ : H_S ⥤ H_R} {C_ψ : H_T ⥤ H_S} {C_χ : H_T ⥤ H_R}
  {L_φ : D_R ⥤ D_S} {L_ψ : D_S ⥤ D_T} {L_χ : D_R ⥤ D_T}
  {R_φ : D_S ⥤ D_R} {R_ψ : D_T ⥤ D_S} {R_χ : D_T ⥤ D_R}

/-- The conjugate `L_χ ≅ L_φ ⋙ L_ψ` of an isomorphism `β : R_ψ ⋙ R_φ ≅ R_χ` of right adjoints is
compatible with the counits `κ : Q ⋙ L ⟶ E ⋙ Q`, through maps `j : E_ψ (E_φ M) ⟶ E_χ M`, provided
the units of the adjunctions `L ⊣ R` are induced by those of `E ⊣ C` and `β` is induced by maps
`ρ : C_χ N ⟶ C_φ (C_ψ N)` conjugate to the `j`. -/
lemma conjugateIsoEquiv_symm_inv_app_comp_counit
    (e_φ : E_φ ⊣ C_φ) (e_ψ : E_ψ ⊣ C_ψ) (e_χ : E_χ ⊣ C_χ)
    (a_φ : L_φ ⊣ R_φ) (a_ψ : L_ψ ⊣ R_ψ) (a_χ : L_χ ⊣ R_χ)
    (κ_φ : Q_R ⋙ L_φ ⟶ E_φ ⋙ Q_S) (κ_ψ : Q_S ⋙ L_ψ ⟶ E_ψ ⋙ Q_T)
    (κ_χ : Q_R ⋙ L_χ ⟶ E_χ ⋙ Q_T)
    (σ_φ : Q_S ⋙ R_φ ≅ C_φ ⋙ Q_R) (σ_ψ : Q_T ⋙ R_ψ ≅ C_ψ ⋙ Q_S)
    (σ_χ : Q_T ⋙ R_χ ≅ C_χ ⋙ Q_R)
    (β : R_ψ ⋙ R_φ ≅ R_χ) (ρ : ∀ N, C_χ.obj N ⟶ C_φ.obj (C_ψ.obj N))
    (j : ∀ M, E_ψ.obj (E_φ.obj M) ⟶ E_χ.obj M)
    (h_φ : ∀ M, a_φ.unit.app (Q_R.obj M) ≫ R_φ.map (κ_φ.app M) =
      Q_R.map (e_φ.unit.app M) ≫ σ_φ.inv.app (E_φ.obj M))
    (h_ψ : ∀ M, a_ψ.unit.app (Q_S.obj M) ≫ R_ψ.map (κ_ψ.app M) =
      Q_S.map (e_ψ.unit.app M) ≫ σ_ψ.inv.app (E_ψ.obj M))
    (h_χ : ∀ M, a_χ.unit.app (Q_R.obj M) ≫ R_χ.map (κ_χ.app M) =
      Q_R.map (e_χ.unit.app M) ≫ σ_χ.inv.app (E_χ.obj M))
    (hβ : ∀ N, σ_χ.inv.app N ≫ β.inv.app (Q_T.obj N) =
      Q_R.map (ρ N) ≫ σ_φ.inv.app (C_ψ.obj N) ≫ R_φ.map (σ_ψ.inv.app N))
    (hj : ∀ M, e_χ.unit.app M ≫ ρ (E_χ.obj M) =
      e_φ.unit.app M ≫ C_φ.map (e_ψ.unit.app (E_φ.obj M) ≫ C_ψ.map (j M)))
    (M : H_R) :
    ((conjugateIsoEquiv (a_φ.comp a_ψ) a_χ).symm β).inv.app (Q_R.obj M) ≫ κ_χ.app M =
      L_ψ.map (κ_φ.app M) ≫ κ_ψ.app (E_φ.obj M) ≫ Q_T.map (j M) := by
  apply ((a_φ.comp a_ψ).homEquiv _ _).injective
  have h₁ := unit_conjugateEquiv_symm a_χ (a_φ.comp a_ψ) β.inv (Q_R.obj M)
  have n₁ := β.inv.naturality (κ_χ.app M)
  have n₂ := a_ψ.unit.naturality (κ_φ.app M)
  have n₃ := σ_ψ.inv.naturality (j M)
  have n₄ := σ_φ.inv.naturality (e_ψ.unit.app (E_φ.obj M) ≫ C_ψ.map (j M))
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_map,
    comp_unit_app, Category.assoc] at h₁ n₁ n₂ n₃ n₄
  rw [homEquiv_unit, homEquiv_unit]
  simp only [Functor.comp_obj, Functor.comp_map, Functor.map_comp, comp_unit_app,
    Category.assoc]
  calc _ = (a_χ.unit.app (Q_R.obj M) ≫ β.inv.app (L_χ.obj (Q_R.obj M))) ≫
        R_φ.map (R_ψ.map (κ_χ.app M)) := by
          rw [h₁]; simp only [Category.assoc, conjugateIsoEquiv_symm_apply_inv]
    _ = Q_R.map (e_χ.unit.app M ≫ ρ (E_χ.obj M)) ≫
        σ_φ.inv.app (C_ψ.obj (E_χ.obj M)) ≫ R_φ.map (σ_ψ.inv.app (E_χ.obj M)) := by
          rw [Category.assoc, ← n₁, reassoc_of% (h_χ M), hβ, Q_R.map_comp_assoc]
    _ = Q_R.map (e_φ.unit.app M) ≫ σ_φ.inv.app (E_φ.obj M) ≫
        R_φ.map (Q_S.map (e_ψ.unit.app (E_φ.obj M) ≫ C_ψ.map (j M)) ≫
          σ_ψ.inv.app (E_χ.obj M)) := by
          rw [hj M, Q_R.map_comp_assoc, R_φ.map_comp, ← reassoc_of% n₄]
    _ = a_φ.unit.app (Q_R.obj M) ≫ R_φ.map (κ_φ.app M ≫ a_ψ.unit.app (Q_S.obj (E_φ.obj M)) ≫
          R_ψ.map (κ_ψ.app (E_φ.obj M) ≫ Q_T.map (j M))) := by
          rw [R_φ.map_comp (κ_φ.app M), reassoc_of% (h_φ M), R_ψ.map_comp (κ_ψ.app _),
            reassoc_of% (h_ψ (E_φ.obj M)),
            ← n₃]
          simp only [Functor.map_comp, Category.assoc]
    _ = _ := by
          rw [reassoc_of% n₂]
          simp only [Functor.map_comp]

end CategoryTheory.Adjunction
