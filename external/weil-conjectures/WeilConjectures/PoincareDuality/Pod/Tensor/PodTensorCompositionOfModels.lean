/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Products.Basic
import Mathlib.Tactic.CategoryTheory.Slice
/-! # Pasting three tensor model equations
Source: blueprint dual-Tate compatibility, Steps 1 and 5. -/
@[expose] public section
set_option autoImplicit false
open CategoryTheory
namespace WeilConjectures
/-- Cancel the output model comparison after pasting three tensor model squares.
Source: blueprint Steps 1 and 5; Stacks 07A4, 0941
(blueprint: lem-pod-tensor-composition-of-models).
Proof: compose with the invertible output comparison. Move the intermediate
factor through tensor naturality, use the three model squares, and substitute
the input and output compositor squares. Functoriality of the tensor functor
and its comparison naturality identify the results; cancel the comparison. -/
theorem podTensorCompositionOfModels
    {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₀ ⥤ C₂) (κ : H ≅ F ⋙ G)
    (B₀ : C₀ × C₀ ⥤ C₀) (B₁ : C₁ × C₁ ⥤ C₁) (B₂ : C₂ × C₂ ⥤ C₂)
    {M N K : C₀} {FM FN FK : C₁} {HM HN HK GM GN GK : C₂}
    (e₀ : B₀.obj (M, N) ⟶ K) (eF : B₁.obj (FM, FN) ⟶ FK)
    (eG : B₂.obj (GM, GN) ⟶ GK) (eH : B₂.obj (HM, HN) ⟶ HK) [IsIso eG]
    (fM : F.obj M ≅ FM) (fN : F.obj N ≅ FN)
    (gM : G.obj FM ≅ GM) (gN : G.obj FN ≅ GN)
    (hM : H.obj M ≅ HM) (hN : H.obj N ≅ HN)
    (cF : F.obj K ⟶ FK) (cG : G.obj FK ⟶ GK) (cH : H.obj K ⟶ HK)
    (dM : HM ⟶ GM) (dN : HN ⟶ GN) (dK : HK ⟶ GK)
    (μF : F.obj (B₀.obj (M, N)) ⟶ B₁.obj (F.obj M, F.obj N))
    (μG : G.obj (B₁.obj (F.obj M, F.obj N)) ⟶
      B₂.obj (G.obj (F.obj M), G.obj (F.obj N)))
    (μG' : G.obj (B₁.obj (FM, FN)) ⟶ B₂.obj (G.obj FM, G.obj FN))
    (μH : H.obj (B₀.obj (M, N)) ⟶ B₂.obj (H.obj M, H.obj N))
    (hF : HEq (F.map e₀ ≫ cF)
      (μF ≫ B₁.map (Prod.mkHom fM.hom fN.hom) ≫ eF))
    (hG : HEq (G.map eF ≫ cG)
      (μG' ≫ B₂.map (Prod.mkHom gM.hom gN.hom) ≫ eG))
    (hH : HEq (H.map e₀ ≫ cH)
      (μH ≫ B₂.map (Prod.mkHom hM.hom hN.hom) ≫ eH))
    (hn : G.map (B₁.map (Prod.mkHom fM.hom fN.hom)) ≫ μG' =
      μG ≫ B₂.map (Prod.mkHom (G.map fM.hom) (G.map fN.hom)))
    (hd : B₂.map (Prod.mkHom dM dN) ≫ eG = eH ≫ dK)
    (hm : κ.hom.app M ≫ G.map fM.hom ≫ gM.hom = hM.hom ≫ dM)
    (hq : κ.hom.app N ≫ G.map fN.hom ≫ gN.hom = hN.hom ≫ dN)
    (hk : κ.hom.app K ≫ G.map cF ≫ cG = cH ≫ dK) :
    κ.hom.app (B₀.obj (M, N)) ≫ G.map μF ≫ μG =
      μH ≫ B₂.map (Prod.mkHom (κ.hom.app M) (κ.hom.app N)) := by
  have hF := eq_of_heq hF
  have hG := eq_of_heq hG
  have hH := eq_of_heq hH
  let rM := G.mapIso fM ≪≫ gM
  let rN := G.mapIso fN ≪≫ gN
  apply (cancel_mono ((B₂.mapIso (rM.prod rN)).hom ≫ eG)).1
  have hprod {X X' X'' Y Y' Y'' : C₂} (a : X ⟶ X') (b : Y ⟶ Y')
      (c : X' ⟶ X'') (d : Y' ⟶ Y'') :
      B₂.map (Prod.mkHom a b) ≫ B₂.map (Prod.mkHom c d) =
        B₂.map (Prod.mkHom (a ≫ c) (b ≫ d)) := (B₂.map_comp _ _).symm
  change _ ≫ (B₂.map (Prod.mkHom (G.map fM.hom ≫ gM.hom)
    (G.map fN.hom ≫ gN.hom)) ≫ eG) = _
  calc
    _ = κ.hom.app (B₀.obj (M, N)) ≫ G.map μF ≫
        G.map (B₁.map (Prod.mkHom fM.hom fN.hom)) ≫ G.map eF ≫ cG := by
      rw [← hprod]
      simp only [Category.assoc]
      slice_lhs 3 4 => rw [← hn]
      simp only [Category.assoc]
      rw [← hG]
    _ = κ.hom.app (B₀.obj (M, N)) ≫ G.map (F.map e₀) ≫ G.map cF ≫ cG := by
      have he := congrArg (fun z ↦ G.map z) hF
      simp only [CategoryTheory.Functor.map_comp] at he
      slice_lhs 2 4 => rw [← he]
      simp only [Category.assoc]
    _ = H.map e₀ ≫ cH ≫ dK := by
      have he := κ.hom.naturality e₀
      change H.map e₀ ≫ κ.hom.app K =
        κ.hom.app (B₀.obj (M, N)) ≫ G.map (F.map e₀) at he
      slice_lhs 1 2 => rw [← he]
      simp only [Category.assoc]
      rw [hk]
    _ = μH ≫ B₂.map (Prod.mkHom hM.hom hN.hom) ≫
        B₂.map (Prod.mkHom dM dN) ≫ eG := by
      rw [← Category.assoc, hH]
      simp only [Category.assoc]
      rw [hd]
    _ = _ := by
      simp only [Category.assoc]
      rw [← Category.assoc _ _ eG, hprod, ← hm, ← hq]
      change _ = μH ≫ B₂.map (Prod.mkHom (κ.hom.app M) (κ.hom.app N)) ≫
        B₂.map (Prod.mkHom (G.map fM.hom ≫ gM.hom) (G.map fN.hom ≫ gN.hom)) ≫ eG
      slice_rhs 2 3 => rw [hprod]

end WeilConjectures
