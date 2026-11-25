/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Products.Basic

/-! # Pasting a tensor square through integral coordinates

The proof uses only functoriality, naturality, and cancellation of an isomorphism.
(blueprint: lem-sf-adic-integral-tensor-pasting).
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory
namespace WeilConjectures.AdicQbarRealization

/-- Paste a finite tensor square through coordinate isomorphisms.
Source: the categorical diagram calculation in BS 6.8.15.
(blueprint: lem-sf-adic-integral-tensor-pasting). -/
theorem pasteIntegralTensorSquare
    {CY CX : Type*} [Category* CY] [Category* CX]
    (F : CY ⥤ CX) (BY : CY × CY ⥤ CY) (BX : CX × CX ⥤ CX)
    (W : BY ⋙ F ≅ F.prod F ⋙ BX)
    {yK yL yK₀ yL₀ yS yT yT₀ : CY}
    {gK gL xK xL eK eL xGS xSG xTJ xTj xGT xTp ePt eT : CX}
    {rYK : yK ≅ yK₀} {rYL : yL ≅ yL₀} {rYT : yT ≅ yT₀}
    {rXK : xK ≅ eK} {rXL : xL ≅ eL} {rXT : xTj ≅ eT} {rXPT : xTp ≅ ePt}
    {μY : BY.obj (yK, yL) ⟶ yS} {aY : yS ⟶ yT}
    {cS : F.obj yS ⟶ xGS} {cT : F.obj yT ⟶ xGT}
    {m : xGS ⟶ xSG} {aG : xGS ⟶ xGT} {pT : xGT ⟶ xTp} {ν : ePt ⟶ eT}
    {pK : gK ⟶ xK} {pL : gL ⟶ xL} {cK : F.obj yK ⟶ gK} {cL : F.obj yL ⟶ gL}
    {sP : xSG ⟶ xTJ} {μXG : BX.obj (gK, gL) ⟶ xSG}
    {μXJ : BX.obj (xK, xL) ⟶ xTJ} {aX : xTJ ⟶ xTj}
    {bY : BY.obj (yK₀, yL₀) ⟶ yT₀} {bX : BX.obj (eK, eL) ⟶ eT}
    {dT : F.obj yT₀ ⟶ ePt} {dK : F.obj yK₀ ⟶ eK} {dL : F.obj yL₀ ⟶ eL}
    [IsIso (sP ≫ aX ≫ rXT.hom)]
    (hTY : μY ≫ aY ≫ rYT.hom = BY.map (Prod.mkHom rYK.hom rYL.hom) ≫ bY)
    (hTX : μXJ ≫ aX ≫ rXT.hom = BX.map (Prod.mkHom rXK.hom rXL.hom) ≫ bX)
    (htail : m ≫ sP ≫ aX ≫ rXT.hom = aG ≫ pT ≫ rXPT.hom ≫ ν)
    (hcNat : F.map aY ≫ cT = cS ≫ aG)
    (hpT : cT ≫ pT ≫ rXPT.hom = F.map rYT.hom ≫ dT)
    (hfinite : F.map bY ≫ dT ≫ ν =
      W.hom.app (yK₀, yL₀) ≫ BX.map (Prod.mkHom dK dL) ≫ bX)
    (hANat : BX.map (Prod.mkHom pK pL) ≫ μXJ = μXG ≫ sP)
    (hpK : cK ≫ pK ≫ rXK.hom = F.map rYK.hom ≫ dK)
    (hpL : cL ≫ pL ≫ rXL.hom = F.map rYL.hom ≫ dL) :
    F.map μY ≫ cS ≫ m = W.hom.app (yK, yL) ≫ BX.map (Prod.mkHom cK cL) ≫ μXG := by
  apply (cancel_mono (sP ≫ aX ≫ rXT.hom)).mp
  have hleft : (F.map μY ≫ cS ≫ m) ≫ (sP ≫ aX ≫ rXT.hom) =
      F.map (BY.map (Prod.mkHom rYK.hom rYL.hom)) ≫
        W.hom.app (yK₀, yL₀) ≫ BX.map (Prod.mkHom dK dL) ≫ bX := by
    simp only [Category.assoc]
    rw [htail, ← reassoc_of% hcNat, reassoc_of% hpT]
    have ht := congrArg F.map hTY
    simp only [Functor.map_comp] at ht
    rw [reassoc_of% ht, hfinite]
  have hright : (W.hom.app (yK, yL) ≫ BX.map (Prod.mkHom cK cL) ≫ μXG) ≫
      (sP ≫ aX ≫ rXT.hom) =
      F.map (BY.map (Prod.mkHom rYK.hom rYL.hom)) ≫
        W.hom.app (yK₀, yL₀) ≫ BX.map (Prod.mkHom dK dL) ≫ bX := by
    simp only [Category.assoc]
    rw [← reassoc_of% hANat, hTX]
    simp only [← Functor.map_comp_assoc, prod_comp, hpK, hpL]
    rw [show Prod.mkHom (F.map rYK.hom ≫ dK) (F.map rYL.hom ≫ dL) =
      Prod.mkHom (F.map rYK.hom) (F.map rYL.hom) ≫ Prod.mkHom dK dL from rfl]
    rw [Functor.map_comp]
    simp only [Category.assoc]
    have hWNat := W.hom.naturality (Prod.mkHom rYK.hom rYL.hom)
    change F.map (BY.map (Prod.mkHom rYK.hom rYL.hom)) ≫ W.hom.app (yK₀, yL₀) =
      W.hom.app (yK, yL) ≫ BX.map (Prod.mkHom (F.map rYK.hom) (F.map rYL.hom)) at hWNat
    rw [← reassoc_of% hWNat]
  exact hleft.trans hright.symm

end WeilConjectures.AdicQbarRealization
