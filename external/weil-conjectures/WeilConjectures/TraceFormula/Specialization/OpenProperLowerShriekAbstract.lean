/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate

/-!

# The adjoint of an open-proper factorization of the lower shriek, abstractly

Let `ι₃ : Y ⟶ X₃`, `ι₁ : Y ⟶ X₁` be open immersions and `p : X₃ ⟶ X₁` proper with `ι₃ ≫ p = ι₁`,
such that `Y = X₃ ×_{X₁} Y`. The isomorphism `E : ι₁! ≅ Rι₁_! ≅ Rι₃_! ⋙ Rp_! ≅ ι₃! ⋙ Rp_*` has
adjoint `E♭ = Lp^*(E) ≫ ε_p : Lp^* ι₁! ⟶ ι₃!`. This file proves, for arbitrary adjunctions and
natural transformations standing for the functors of the six-functor formalism:

* `CategoryTheory.baseChange_comp_map_comp_counit_eq_map`: if the compact-support base change
  `Ex : Rι₁_! ⋙ Lp^* ⟶ L𝟙^* ⋙ Rι₃_!` is the mate of `C⁻¹ : R𝟙_! ⋙ Rι₁_! ⟶ Rι₃_! ⋙ Rp_!` (up to
  `R𝟙_! ≅ 𝟭`) and is inverse to the extension-by-zero base change `BC' : L𝟙^* ⋙ ι₃! ⟶ ι₁! ⋙ Lp^*`,
  then `BC' ≫ E♭ = ι₃!(L𝟙^* ≅ 𝟭)`;
* `CategoryTheory.unit_comp_map_eq_unit_of_exchangeLeft`: if `BC'` is `Adjunction.exchangeLeft` of
  the pullback comparison, then `η_{ι₁} ≫ (Lι₁^* ≅ Lι₃^* Lp^*) ≫ Lι₃^*(E♭) = η_{ι₃}`.

-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

variable {𝒴 𝒳₁ 𝒳₃ : Type*} [Category 𝒴] [Category 𝒳₁] [Category 𝒳₃]

/-- **The adjoint of `E : E₁ ≅ E₃ ⋙ R_p` inverts the extension-by-zero base change**, abstractly:
let `Ex : S₁ ⋙ L_p ⟶ L_𝟙 ⋙ S₃` be the mate of `Σ : S_𝟙 ⋙ S₁ ⟶ S₃ ⋙ S_p` with
`Σ = S₁(ι_𝟙) ≫ C` (for the adjunctions `L_𝟙 ⊣ S_𝟙` and `L_p ⊣ R_p ≅ S_p`), and let
`BC' : L_𝟙 ⋙ E₃ ⟶ E₁ ⋙ L_p` satisfy `Ex ≫ O₃ ≫ BC' = L_p(O₁)`, with `Ex` invertible. Then
`BC' ≫ L_p(O₁⁻¹ ≫ C ≫ S_p(O₃) ≫ P_p) ≫ ε_p = E₃(L_𝟙 ≅ 𝟭)`. -/
lemma baseChange_comp_map_comp_counit_eq_map {S1 L1 : 𝒴 ⥤ 𝒴} {S₁ E₁ : 𝒴 ⥤ 𝒳₁}
    {S₃ E₃ : 𝒴 ⥤ 𝒳₃} {Sp Rp : 𝒳₃ ⥤ 𝒳₁} {Lp : 𝒳₁ ⥤ 𝒳₃} (a1 : L1 ⊣ S1) (ap : Lp ⊣ Rp)
    (ι1 : S1 ≅ 𝟭 𝒴) (U1 : L1 ≅ 𝟭 𝒴)
    (hc1 : ∀ N, a1.counit.app N = U1.hom.app (S1.obj N) ≫ ι1.hom.app N)
    (O₁ : S₁ ≅ E₁) (O₃ : S₃ ≅ E₃) (Pp : Sp ≅ Rp) (C : S₁ ≅ S₃ ⋙ Sp) (Sig : S1 ⋙ S₁ ⟶ S₃ ⋙ Sp)
    (hSig : ∀ N, Sig.app N = S₁.map (ι1.hom.app N) ≫ C.hom.app N) (Ex : S₁ ⋙ Lp ⟶ L1 ⋙ S₃)
    (hEx : Ex = (mateEquiv a1 (ap.ofNatIsoRight Pp.symm)).symm Sig) (BC' : L1 ⋙ E₃ ⟶ E₁ ⋙ Lp)
    (hO : ∀ K, Ex.app K ≫ O₃.hom.app (L1.obj K) ≫ BC'.app K = Lp.map (O₁.hom.app K))
    (K : 𝒴) [IsIso (Ex.app K)] :
    BC'.app K ≫ Lp.map (O₁.inv.app K ≫ C.hom.app K ≫ Sp.map (O₃.hom.app K) ≫
        Pp.hom.app (E₃.obj K)) ≫ ap.counit.app (E₃.obj K) =
      E₃.map (U1.hom.app K) := by
  -- the key formula `L_p(C ≫ P_p) ≫ ε_p = Ex ≫ S₃(L_𝟙 ≅ 𝟭)`
  have hkey : Lp.map (C.hom.app K ≫ Pp.hom.app (S₃.obj K)) ≫ ap.counit.app (S₃.obj K) =
      Ex.app K ≫ S₃.map (U1.hom.app K) := by
    rw [← cancel_epi (Lp.map (S₁.map (ι1.hom.app K)))]
    have hm := mateEquiv_counit_symm a1 (ap.ofNatIsoRight Pp.symm) Sig K
    rw [← hEx] at hm
    simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app, Functor.whiskerRight_app,
      Iso.symm_inv, Functor.id_obj] at hm
    have hn := Ex.naturality (ι1.hom.app K)
    simp only [Functor.comp_map, Functor.id_obj] at hn
    have hU := U1.hom.naturality (ι1.hom.app K)
    simp only [Functor.id_map, Functor.id_obj] at hU
    rw [reassoc_of% hn, ← S₃.map_comp, hU, ← hc1, ← hm, hSig]
    simp only [Functor.map_comp, Category.assoc]
  -- `BC' ≫ L_p(O₁⁻¹) ≫ Ex = O₃⁻¹`
  have hE : BC'.app K ≫ Lp.map (O₁.inv.app K) ≫ Ex.app K = O₃.inv.app (L1.obj K) := by
    have h₁ : BC'.app K = O₃.inv.app _ ≫ inv (Ex.app K) ≫ Lp.map (O₁.hom.app K) := by
      rw [← hO K]
      simp
    rw [h₁]
    simp [← Lp.map_comp_assoc]
  have hP := Pp.hom.naturality (O₃.hom.app K)
  have hε := ap.counit.naturality (O₃.hom.app K)
  simp only [Functor.comp_map, Functor.id_map, Functor.id_obj] at hP hε
  have hP' : Lp.map (Sp.map (O₃.hom.app K) ≫ Pp.hom.app (E₃.obj K)) ≫ ap.counit.app (E₃.obj K) =
      Lp.map (Pp.hom.app (S₃.obj K)) ≫ ap.counit.app (S₃.obj K) ≫ O₃.hom.app K := by
    rw [hP, Lp.map_comp_assoc, hε]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Lp.map_comp_assoc (Sp.map _), hP', ← Lp.map_comp_assoc (C.hom.app K), reassoc_of% hkey,
    reassoc_of% hE, ← O₃.inv.naturality_assoc]
  simp

/-- **The unit identity of the adjoint of `E`**, abstractly: if `BC' = exchangeLeft a₁ a₃ θ` for
`θ = (L_𝟙 ≅ 𝟭) ≫ c` and `φ : L_p E₁ K ⟶ E₃ K` satisfies `BC' ≫ φ = E₃(L_𝟙 ≅ 𝟭)`, then
`η₁ ≫ c ≫ L₃(φ) = η₃`. -/
lemma unit_comp_map_eq_unit_of_exchangeLeft {L1 : 𝒴 ⥤ 𝒴} {E₁ : 𝒴 ⥤ 𝒳₁} {L₁ : 𝒳₁ ⥤ 𝒴}
    {E₃ : 𝒴 ⥤ 𝒳₃} {L₃ : 𝒳₃ ⥤ 𝒴} {Lp : 𝒳₁ ⥤ 𝒳₃} (a₁ : E₁ ⊣ L₁) (a₃ : E₃ ⊣ L₃)
    (U1 : L1 ≅ 𝟭 𝒴) (c : L₁ ≅ Lp ⋙ L₃) (θ : L₁ ⋙ L1 ≅ Lp ⋙ L₃)
    (hθ : ∀ Z, θ.hom.app Z = U1.hom.app (L₁.obj Z) ≫ c.hom.app Z) (BC' : L1 ⋙ E₃ ⟶ E₁ ⋙ Lp)
    (hBC' : BC' = Adjunction.exchangeLeft a₁ a₃ θ) (K : 𝒴) (φ : Lp.obj (E₁.obj K) ⟶ E₃.obj K)
    (hφ : BC'.app K ≫ φ = E₃.map (U1.hom.app K)) :
    a₁.unit.app K ≫ c.hom.app (E₁.obj K) ≫ L₃.map φ = a₃.unit.app K := by
  have hA : a₃.unit.app (L1.obj K) ≫ L₃.map (BC'.app K) =
      U1.hom.app K ≫ a₁.unit.app K ≫ c.hom.app (E₁.obj K) := by
    subst hBC'
    rw [Adjunction.exchangeLeft_app, ← E₃.map_comp_assoc]
    erw [← Adjunction.homEquiv_counit, ← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]
    rw [hθ]
    have hU := U1.hom.naturality (a₁.unit.app K)
    simp only [Functor.id_map, Functor.id_obj, Functor.comp_obj] at hU
    rw [reassoc_of% hU]
  rw [← cancel_epi (U1.hom.app K), ← reassoc_of% hA, ← L₃.map_comp, hφ]
  exact (a₃.unit.naturality (U1.hom.app K)).symm
end CategoryTheory
