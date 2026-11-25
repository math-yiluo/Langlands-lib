/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!

# The support identity of the fixed square on a component, abstractly

The *support identity* of `FixedSquareClosedExchange` at `M = Rj_! N₀` (`j : B ⟶ F` a component
of the fixed locus) is
```
ν_c(Rι_* M) ≫ Ψ_{X×X}(Ξ(M)) ≫ χ_Δ(Rd_! M) ≫ RΔ'_*(Ψ_X(κ) ≫ χ_{dj}(N₀))
  = Rc'_!(Ψ_C(a) ≫ χ_g(N₀) ≫ (Rg'_* ≅ Rι'_* Rr_*)) ≫ Ξ'(Rr_* Ψ_B N₀) ≫ RΔ'_*(g')
```
(`Ξ`, `Ξ'` the composition isomorphisms of the fixed squares, `a : Rι_* Rj_! ≅ R(ιj)_*`,
`κ : Rd_! Rj_! ≅ R(dj)_*`). This file deduces it, in arbitrary categories
(`CategoryTheory.supportIdentity_aux`), from

* the identity of `ν_c` on `G N₀ = R(ιj)_* N₀` through the compactification
  (`supportCompactSupportExchange_app_lowerStar`, hypothesis `hF1`);
* the agreement of the compactification route and the fixed-square route to `R(dj ≫ Δ)_*` on both
  fibres (`compactificationRoute_ambient_eq_fixedSquareRoute'`, hypotheses `hF2`, `hF2'`);
* the composition law of the pushforward exchanges `χ_{phg} = χ_Δ ∘ χ_{dj}`
  (`componentSupportModelHom_pushforwardExchange_app`, hypothesis `hF3`);
* the descriptions of the exchanges on bounded constructible complexes as the ambient ones
  (`hχg`, `hχdj`, `hχΔ`) and of the composition isomorphisms (`hL`, `hL'`).

All the functors to the ambient categories (`ιB`, `ιs`, …) and the compatibility isomorphisms
(`cG`, `cT`, …) are arbitrary, so that the concrete instance is a single application.

-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

variable {CB CB' CC CC' CF CF' CX CX' CY CY' CP CP' DB DB' DC DC' DX DX' DY DY' DP DP' : Type*}
  [Category CB] [Category CB'] [Category CC] [Category CC'] [Category CF] [Category CF']
  [Category CX] [Category CX'] [Category CY] [Category CY'] [Category CP] [Category CP']
  [Category DB] [Category DB'] [Category DC] [Category DC'] [Category DX] [Category DX']
  [Category DY] [Category DY'] [Category DP] [Category DP']

/-- **The support identity on a component**, abstractly (see the module docstring). -/
theorem supportIdentity_aux
    {Sp : CC ⥤ CC'} {LSf : CC ⥤ CY} {LSf' : CC' ⥤ CY'} {Ts : CY ⥤ CY'}
    {OLS : CC ⥤ CP} {OLS' : CC' ⥤ CP'} {LStp : CP ⥤ CY} {LStp' : CP' ⥤ CY'}
    {ιB : CB ⥤ DB} {ιB' : CB' ⥤ DB'} {ιC : CC ⥤ DC} {ιC' : CC' ⥤ DC'} {ιP : CP ⥤ DP}
    {ιP' : CP' ⥤ DP'} {ιX : CX ⥤ DX} {ιX' : CX' ⥤ DX'} {ιs : CY ⥤ DY} {ιs' : CY' ⥤ DY'}
    (hι : ιs'.Faithful)
    {ΨC : DC ⥤ DC'} {ΨB : DB ⥤ DB'} {ΨX : DX ⥤ DX'} {Ψs : DY ⥤ DY'}
    {Dh : DC ⥤ DP} {Dh' : DC' ⥤ DP'} {Rp : DP ⥤ DY} {Rp' : DP' ⥤ DY'}
    (i₁ : LSf' ≅ OLS' ⋙ LStp') (i₂ : LSf ≅ OLS ⋙ LStp)
    (cSp : Sp ⋙ ιC' ≅ ιC ⋙ ΨC) (cO' : OLS' ⋙ ιP' ≅ ιC' ⋙ Dh')
    (cR' : LStp' ⋙ ιs' ≅ ιP' ⋙ Rp') (cO : OLS ⋙ ιP ≅ ιC ⋙ Dh) (cR : LStp ⋙ ιs ≅ ιP ⋙ Rp)
    (cT : Ts ⋙ ιs' ≅ ιs ⋙ Ψs) (ν : Sp ⋙ LSf' ⟶ LSf ⋙ Ts)
    {G : CB ⥤ CC} {Rg : DB ⥤ DC} (cG : G ⋙ ιC ≅ ιB ⋙ Rg)
    {G' : CB' ⥤ CC'} {Rg' : DB' ⥤ DC'} (cG' : G' ⋙ ιC' ≅ ιB' ⋙ Rg')
    {SB : CB ⥤ CB'} (cSB : SB ⋙ ιB' ≅ ιB ⋙ ΨB)
    {Rhg : DB ⥤ DP} {Rhg' : DB' ⥤ DP'} {Rphg : DB ⥤ DY} {Rphg' : DB' ⥤ DY'}
    (e : Rg ⋙ Dh ⟶ Rhg) (e' : Rg' ⋙ Dh' ⟶ Rhg') (conj : Rphg ≅ Rhg ⋙ Rp)
    (conj' : Rphg' ≅ Rhg' ⋙ Rp') (χg : Rg ⋙ ΨC ⟶ ΨB ⋙ Rg') (χphg : Rphg ⋙ Ψs ⟶ ΨB ⋙ Rphg')
    (χgB : G ⋙ Sp ⟶ SB ⋙ G')
    (hχg : ∀ N, ιC'.map (χgB.app N) = cSp.hom.app (G.obj N) ≫ ΨC.map (cG.hom.app N) ≫
      χg.app (ιB.obj N) ≫ Rg'.map (cSB.inv.app N) ≫ cG'.inv.app (SB.obj N))
    {Rι : CF ⥤ CC} {Rd : CF ⥤ CX} {RΔ : CX ⥤ CY} (Ξ : Rι ⋙ LSf ≅ Rd ⋙ RΔ)
    {SX : CX ⥤ CX'} {RΔ' : CX' ⥤ CY'} (χΔ : RΔ ⋙ Ts ⟶ SX ⋙ RΔ')
    {Rι' : CF' ⥤ CC'} {Rd' : CF' ⥤ CX'} (Ξ' : Rι' ⋙ LSf' ≅ Rd' ⋙ RΔ')
    {RΔa : DX ⥤ DY} {RΔa' : DX' ⥤ DY'} (cΔ : RΔ ⋙ ιs ≅ ιX ⋙ RΔa)
    (cΔ' : RΔ' ⋙ ιs' ≅ ιX' ⋙ RΔa') (cSX : SX ⋙ ιX' ≅ ιX ⋙ ΨX) (χΔa : RΔa ⋙ Ψs ⟶ ΨX ⋙ RΔa')
    (hχΔ : ∀ T, ιs'.map (χΔ.app T) = cT.hom.app (RΔ.obj T) ≫ Ψs.map (cΔ.hom.app T) ≫
      χΔa.app (ιX.obj T) ≫ RΔa'.map (cSX.inv.app T) ≫ cΔ'.inv.app (SX.obj T))
    {Rjd : CB ⥤ CX} {Rjda : DB ⥤ DX} (cjd : Rjd ⋙ ιX ≅ ιB ⋙ Rjda)
    {Rjd' : CB' ⥤ CX'} {Rjda' : DB' ⥤ DX'} (cjd' : Rjd' ⋙ ιX' ≅ ιB' ⋙ Rjda')
    (χdjB : Rjd ⋙ SX ⟶ SB ⋙ Rjd') (χdj : Rjda ⋙ ΨX ⟶ ΨB ⋙ Rjda')
    (hχdj : ∀ N, ιX'.map (χdjB.app N) = cSX.hom.app (Rjd.obj N) ≫ ΨX.map (cjd.hom.app N) ≫
      χdj.app (ιB.obj N) ≫ Rjda'.map (cSB.inv.app N) ≫ cjd'.inv.app (SB.obj N))
    (conj3 : Rphg ≅ Rjda ⋙ RΔa) (conj3' : Rphg' ≅ Rjda' ⋙ RΔa')
    (hF3 : ∀ E, χphg.app E ≫ conj3'.hom.app (ΨB.obj E) =
      Ψs.map (conj3.hom.app E) ≫ χΔa.app (Rjda.obj E) ≫ RΔa'.map (χdj.app E))
    (N₀ : CB) {N N₂ : CF} (t : N ⟶ N₂) (a₂ : Rι.obj N₂ ⟶ G.obj N₀)
    {T₂ : CY} (κ₂ : Rd.obj N₂ ⟶ Rjd.obj N₀) (lsc : RΔ.obj (Rjd.obj N₀) ⟶ T₂)
    (back : T₂ ⟶ RΔ.obj (Rjd.obj N₀)) (hback : lsc ≫ back = 𝟙 _)
    (E1 : Rphg.obj (ιB.obj N₀) ⟶ ιs.obj T₂)
    (hF1 : ιs'.map (i₁.inv.app (Sp.obj (G.obj N₀))) ≫ ιs'.map (ν.app (G.obj N₀)) ≫
        cT.hom.app (LSf.obj (G.obj N₀)) ≫
        Ψs.map (ιs.map (i₂.hom.app (G.obj N₀)) ≫ cR.hom.app (OLS.obj (G.obj N₀)) ≫
          Rp.map (cO.hom.app (G.obj N₀)) ≫ Rp.map (Dh.map (cG.hom.app N₀)) ≫
          Rp.map (e.app (ιB.obj N₀)) ≫ conj.inv.app (ιB.obj N₀)) ≫ χphg.app (ιB.obj N₀) =
      cR'.hom.app (OLS'.obj (Sp.obj (G.obj N₀))) ≫
        Rp'.map (cO'.hom.app (Sp.obj (G.obj N₀)) ≫ Dh'.map (cSp.hom.app (G.obj N₀)) ≫
          Dh'.map (ΨC.map (cG.hom.app N₀)) ≫ Dh'.map (χg.app (ιB.obj N₀)) ≫
          e'.app (ΨB.obj (ιB.obj N₀))) ≫ conj'.inv.app (ΨB.obj (ιB.obj N₀)))
    (hF2 : ιs.map (LSf.map a₂) ≫ ιs.map (i₂.hom.app (G.obj N₀)) ≫
        cR.hom.app (OLS.obj (G.obj N₀)) ≫ Rp.map (cO.hom.app (G.obj N₀)) ≫
        Rp.map (Dh.map (cG.hom.app N₀)) ≫ Rp.map (e.app (ιB.obj N₀)) ≫
        conj.inv.app (ιB.obj N₀) ≫ E1 = ιs.map (Ξ.hom.app N₂ ≫ RΔ.map κ₂ ≫ lsc))
    (hL : E1 ≫ ιs.map back =
      conj3.hom.app (ιB.obj N₀) ≫ RΔa.map (cjd.inv.app N₀) ≫ cΔ.inv.app (Rjd.obj N₀))
    {M' : CF'} (c₂' : Rι'.obj M' ⟶ G'.obj (SB.obj N₀))
    (cinv : G'.obj (SB.obj N₀) ⟶ Rι'.obj M') (hcinv : cinv ≫ c₂' = 𝟙 _)
    {T' : CX'} (g'' : Rd'.obj M' ⟶ T') {T₂' : CY'} (lsc' : RΔ'.obj T' ⟶ T₂')
    (tr : T' ⟶ Rjd'.obj (SB.obj N₀)) (back' : T₂' ⟶ RΔ'.obj (Rjd'.obj (SB.obj N₀)))
    (hback' : lsc' ≫ back' = RΔ'.map tr)
    (E1' : Rphg'.obj (ιB'.obj (SB.obj N₀)) ⟶ ιs'.obj T₂')
    (hF2' : ιs'.map (LSf'.map c₂') ≫ ιs'.map (i₁.hom.app (G'.obj (SB.obj N₀))) ≫
        cR'.hom.app (OLS'.obj (G'.obj (SB.obj N₀))) ≫
        Rp'.map (cO'.hom.app (G'.obj (SB.obj N₀))) ≫
        Rp'.map (Dh'.map (cG'.hom.app (SB.obj N₀))) ≫ Rp'.map (e'.app (ιB'.obj (SB.obj N₀))) ≫
        conj'.inv.app (ιB'.obj (SB.obj N₀)) ≫ E1' = ιs'.map (Ξ'.hom.app M' ≫ RΔ'.map g'' ≫ lsc'))
    (hL' : E1' ≫ ιs'.map back' = conj3'.hom.app (ιB'.obj (SB.obj N₀)) ≫
      RΔa'.map (cjd'.inv.app (SB.obj N₀)) ≫ cΔ'.inv.app (Rjd'.obj (SB.obj N₀))) :
    ν.app (Rι.obj N) ≫ Ts.map (Ξ.hom.app N) ≫ χΔ.app (Rd.obj N) ≫
        RΔ'.map (SX.map (Rd.map t ≫ κ₂) ≫ χdjB.app N₀) =
      LSf'.map (Sp.map (Rι.map t ≫ a₂) ≫ χgB.app N₀ ≫ cinv) ≫ Ξ'.hom.app M' ≫
        RΔ'.map (g'' ≫ tr) := by
  -- the `Dᵇc` part: move `t` to the front
  have h1 := χΔ.naturality (Rd.map t ≫ κ₂)
  have h2 := Ξ.hom.naturality t
  have h3 := ν.naturality (Rι.map t)
  simp only [Functor.comp_map, Functor.comp_obj] at h1 h2 h3
  have L1 : ν.app (Rι.obj N) ≫ Ts.map (Ξ.hom.app N) ≫ χΔ.app (Rd.obj N) ≫
      RΔ'.map (SX.map (Rd.map t ≫ κ₂) ≫ χdjB.app N₀) =
      LSf'.map (Sp.map (Rι.map t)) ≫ ν.app (Rι.obj N₂) ≫
        Ts.map (Ξ.hom.app N₂ ≫ RΔ.map κ₂ ≫ lsc ≫ back) ≫ χΔ.app (Rjd.obj N₀) ≫
        RΔ'.map (χdjB.app N₀) := by
    rw [hback, Category.comp_id, RΔ'.map_comp, ← reassoc_of% h1, ← Ts.map_comp_assoc,
      RΔ.map_comp, ← reassoc_of% h2, Ts.map_comp, reassoc_of% h3]
    simp only [Functor.map_comp, Category.assoc]
  rw [L1]
  simp only [Functor.map_comp, Category.assoc]
  congr 1
  apply hι.map_injective
  -- the ambient part
  have hTy : ∀ {Y Z : CY} (y : Y ⟶ Z),
      ιs'.map (Ts.map y) = cT.hom.app Y ≫ Ψs.map (ιs.map y) ≫ cT.inv.app Z := by
    intro Y Z y
    have := cT.hom.naturality y
    simp only [Functor.comp_map, Functor.comp_obj] at this
    rw [← reassoc_of% this, Iso.hom_inv_id_app]; exact (Category.comp_id _).symm
  have hF2s : ιs.map (Ξ.hom.app N₂) ≫ ιs.map (RΔ.map κ₂) ≫ ιs.map lsc ≫ ιs.map back =
      ιs.map (LSf.map a₂) ≫ ιs.map (i₂.hom.app (G.obj N₀)) ≫
        cR.hom.app (OLS.obj (G.obj N₀)) ≫ Rp.map (cO.hom.app (G.obj N₀)) ≫
        Rp.map (Dh.map (cG.hom.app N₀)) ≫ Rp.map (e.app (ιB.obj N₀)) ≫
        conj.inv.app (ιB.obj N₀) ≫ conj3.hom.app (ιB.obj N₀) ≫ RΔa.map (cjd.inv.app N₀) ≫
        cΔ.inv.app (Rjd.obj N₀) := by
    rw [← hL]
    simp only [← Category.assoc] at hF2 ⊢
    rw [hF2]
    simp only [Functor.map_comp, Category.assoc]
  have hF1' : ιs'.map (ν.app (G.obj N₀)) ≫ cT.hom.app (LSf.obj (G.obj N₀)) ≫
      Ψs.map (ιs.map (i₂.hom.app (G.obj N₀)) ≫ cR.hom.app (OLS.obj (G.obj N₀)) ≫
          Rp.map (cO.hom.app (G.obj N₀)) ≫ Rp.map (Dh.map (cG.hom.app N₀)) ≫
          Rp.map (e.app (ιB.obj N₀)) ≫ conj.inv.app (ιB.obj N₀)) ≫ χphg.app (ιB.obj N₀) =
      ιs'.map (i₁.hom.app (Sp.obj (G.obj N₀))) ≫ cR'.hom.app (OLS'.obj (Sp.obj (G.obj N₀))) ≫
        Rp'.map (cO'.hom.app (Sp.obj (G.obj N₀)) ≫ Dh'.map (cSp.hom.app (G.obj N₀)) ≫
          Dh'.map (ΨC.map (cG.hom.app N₀)) ≫ Dh'.map (χg.app (ιB.obj N₀)) ≫
          e'.app (ΨB.obj (ιB.obj N₀))) ≫ conj'.inv.app (ΨB.obj (ιB.obj N₀)) := by
    rw [← hF1, ← ιs'.map_comp_assoc, Iso.hom_inv_id_app, ιs'.map_id, Category.id_comp]
  have h4 := ν.naturality a₂
  simp only [Functor.comp_map, Functor.comp_obj] at h4
  have hN4 : ιs'.map (ν.app (Rι.obj N₂)) ≫ cT.hom.app (LSf.obj (Rι.obj N₂)) ≫
      Ψs.map (ιs.map (LSf.map a₂)) = ιs'.map (LSf'.map (Sp.map a₂)) ≫
        ιs'.map (ν.app (G.obj N₀)) ≫ cT.hom.app (LSf.obj (G.obj N₀)) := by
    have := congrArg ιs'.map h4
    simp only [Functor.map_comp, hTy] at this
    rw [reassoc_of% this]; simp
  have hcΔ' := cΔ'.inv.naturality (χdjB.app N₀)
  have hχΔa := χΔa.naturality (cjd.inv.app N₀)
  simp only [Functor.comp_map, Functor.comp_obj] at hcΔ' hχΔa
  have hX : Ψs.map (cΔ.inv.app (Rjd.obj N₀)) ≫ cT.inv.app (RΔ.obj (Rjd.obj N₀)) ≫
      ιs'.map (χΔ.app (Rjd.obj N₀)) ≫ ιs'.map (RΔ'.map (χdjB.app N₀)) =
      χΔa.app (ιX.obj (Rjd.obj N₀)) ≫ RΔa'.map (ΨX.map (cjd.hom.app N₀) ≫
        χdj.app (ιB.obj N₀) ≫ Rjda'.map (cSB.inv.app N₀) ≫ cjd'.inv.app (SB.obj N₀)) ≫
        cΔ'.inv.app (Rjd'.obj (SB.obj N₀)) := by
    rw [hχΔ]; simp only [Category.assoc]; rw [← hcΔ', hχdj]
    simp only [Iso.inv_hom_id_app_assoc, ← Ψs.map_comp_assoc,
      Iso.inv_hom_id_app, Ψs.map_id, Category.id_comp, ← RΔa'.map_comp_assoc,
      Iso.inv_hom_id_app_assoc]
  have hY : Ψs.map (RΔa.map (cjd.inv.app N₀)) ≫ χΔa.app (ιX.obj (Rjd.obj N₀)) ≫
      RΔa'.map (ΨX.map (cjd.hom.app N₀) ≫ χdj.app (ιB.obj N₀) ≫
        Rjda'.map (cSB.inv.app N₀) ≫ cjd'.inv.app (SB.obj N₀)) =
      χΔa.app (Rjda.obj (ιB.obj N₀)) ≫ RΔa'.map (χdj.app (ιB.obj N₀) ≫
        Rjda'.map (cSB.inv.app N₀) ≫ cjd'.inv.app (SB.obj N₀)) := by
    rw [reassoc_of% hχΔa, ← RΔa'.map_comp, ← ΨX.map_comp_assoc, Iso.inv_hom_id_app]
    simp
  have LHS : ιs'.map (ν.app (Rι.obj N₂) ≫ Ts.map (Ξ.hom.app N₂) ≫ Ts.map (RΔ.map κ₂) ≫
      Ts.map lsc ≫ Ts.map back ≫ χΔ.app (Rjd.obj N₀) ≫ RΔ'.map (χdjB.app N₀)) =
      ιs'.map (LSf'.map (Sp.map a₂)) ≫ ιs'.map (i₁.hom.app (Sp.obj (G.obj N₀))) ≫
        cR'.hom.app (OLS'.obj (Sp.obj (G.obj N₀))) ≫
        Rp'.map (cO'.hom.app (Sp.obj (G.obj N₀)) ≫ Dh'.map (cSp.hom.app (G.obj N₀)) ≫
          Dh'.map (ΨC.map (cG.hom.app N₀)) ≫ Dh'.map (χg.app (ιB.obj N₀)) ≫
          e'.app (ΨB.obj (ιB.obj N₀))) ≫ conj'.inv.app (ΨB.obj (ιB.obj N₀)) ≫
        conj3'.hom.app (ΨB.obj (ιB.obj N₀)) ≫ RΔa'.map (Rjda'.map (cSB.inv.app N₀) ≫
          cjd'.inv.app (SB.obj N₀)) ≫ cΔ'.inv.app (Rjd'.obj (SB.obj N₀)) := by
    have hs := congrArg Ψs.map hF2s
    simp only [Functor.map_comp] at hs
    simp only [Functor.map_comp, Category.assoc, hTy, Iso.inv_hom_id_app_assoc]
    rw [reassoc_of% hs, reassoc_of% hN4, hX, reassoc_of% hY]
    have h3' := hF3 (ιB.obj N₀)
    simp only [Functor.map_comp, Category.assoc] at hF1' h3' ⊢
    rw [← reassoc_of% h3', reassoc_of% hF1']
  have hF2'' : ιs'.map (LSf'.map cinv) ≫ ιs'.map (Ξ'.hom.app M') ≫ ιs'.map (RΔ'.map g'') ≫
      ιs'.map (RΔ'.map tr) = ιs'.map (i₁.hom.app (G'.obj (SB.obj N₀))) ≫
        cR'.hom.app (OLS'.obj (G'.obj (SB.obj N₀))) ≫
        Rp'.map (cO'.hom.app (G'.obj (SB.obj N₀))) ≫
        Rp'.map (Dh'.map (cG'.hom.app (SB.obj N₀))) ≫ Rp'.map (e'.app (ιB'.obj (SB.obj N₀))) ≫
        conj'.inv.app (ιB'.obj (SB.obj N₀)) ≫ conj3'.hom.app (ιB'.obj (SB.obj N₀)) ≫
        RΔa'.map (cjd'.inv.app (SB.obj N₀)) ≫ cΔ'.inv.app (Rjd'.obj (SB.obj N₀)) := by
    rw [← hback', ← hL']
    simp only [Functor.map_comp] at hF2' ⊢
    rw [← reassoc_of% hF2', ← ιs'.map_comp_assoc, ← LSf'.map_comp, hcinv]
    simp
  have n1 := i₁.hom.naturality (χgB.app N₀)
  have n2 := cR'.hom.naturality (OLS'.map (χgB.app N₀))
  have n3 := cO'.hom.naturality (χgB.app N₀)
  have n4 := e'.naturality (cSB.inv.app N₀)
  have n5 := conj'.inv.naturality (cSB.inv.app N₀)
  have n6 := conj3'.hom.naturality (cSB.inv.app N₀)
  simp only [Functor.comp_map, Functor.comp_obj] at n1 n2 n3 n4 n5 n6
  have hNat : ιs'.map (LSf'.map (χgB.app N₀)) ≫ ιs'.map (i₁.hom.app (G'.obj (SB.obj N₀))) ≫
      cR'.hom.app (OLS'.obj (G'.obj (SB.obj N₀))) ≫
      Rp'.map (cO'.hom.app (G'.obj (SB.obj N₀))) =
      ιs'.map (i₁.hom.app (Sp.obj (G.obj N₀))) ≫ cR'.hom.app (OLS'.obj (Sp.obj (G.obj N₀))) ≫
        Rp'.map (cO'.hom.app (Sp.obj (G.obj N₀))) ≫ Rp'.map (Dh'.map (ιC'.map (χgB.app N₀))) := by
    rw [← ιs'.map_comp_assoc, n1, ιs'.map_comp_assoc, reassoc_of% n2, ← Rp'.map_comp, n3,
      Rp'.map_comp]
  rw [LHS]
  simp only [Functor.map_comp, Category.assoc]
  rw [hF2'', reassoc_of% hNat, hχg]
  simp only [Functor.map_comp, Category.assoc]
  have key : Rp'.map (Dh'.map (Rg'.map (cSB.inv.app N₀))) ≫
      Rp'.map (Dh'.map (cG'.inv.app (SB.obj N₀))) ≫ Rp'.map (Dh'.map (cG'.hom.app (SB.obj N₀))) ≫
      Rp'.map (e'.app (ιB'.obj (SB.obj N₀))) ≫ conj'.inv.app (ιB'.obj (SB.obj N₀)) ≫
      conj3'.hom.app (ιB'.obj (SB.obj N₀)) =
      Rp'.map (e'.app (ΨB.obj (ιB.obj N₀))) ≫ conj'.inv.app (ΨB.obj (ιB.obj N₀)) ≫
        conj3'.hom.app (ΨB.obj (ιB.obj N₀)) ≫ RΔa'.map (Rjda'.map (cSB.inv.app N₀)) := by
    rw [← Rp'.map_comp_assoc (Dh'.map (cG'.inv.app _)), ← Dh'.map_comp, Iso.inv_hom_id_app]
    simp only [Functor.map_id, Category.id_comp]
    rw [← Rp'.map_comp_assoc, n4, Rp'.map_comp_assoc, reassoc_of% n5, n6]
  rw [reassoc_of% key]

end CategoryTheory
