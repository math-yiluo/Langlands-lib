/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ExchangeOnProper
public import WeilConjectures.TraceFormula.Specialization.PointExchangeOpen

/-!

# The shape of the exchange `ν_X` on pushforwards

The compact-support exchange `ν_X` of the structure map of a separated scheme
(`ProEtale.CondensedRing.pointCompactSupportExchangeOfOpenImmersion`) has the shape
`openExchangeAux … (pointExchangeAux …)`: the mate `ν_u` of `α_u⁻¹` along the open immersion
`u : X ⊂ Y` (on bounded constructible complexes), followed by `ν_Y = χ_p⁻¹ ∘ Rp'_*(ν_h)` for the
dense compactification `h' : Y' ⊂ P'` of the special fibre of the deformation of the proper `Y`.

This file proves, in abstract categories, the identity of `ν_X` on objects `G N = g_* N`
(`openPointExchangeAux_app_comp_aux_of_eq`), reducing it to an identity on the ambient categories
(hypothesis `hC`) and to the description of `ν_u` through the inclusions (hypothesis `hνu`). This
is the analogue of `compactSupportExchangeAux_app_comp_aux` for `ν_X`.

-/

@[expose] public section

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The exchange `ν_h : h'_! Ψ_Y ⟶ Ψ_P` inside `pointExchangeAux`, for `h` the identity of `Y`
over `k` (`L1 = L(𝟙)^*`, `e : 𝟭 ≅ L1`) and an adjunction `h'_! ⊣ h'^*`. -/
noncomputable def pointOpenExchange {DX DX' DP : Type*} [Category DX] [Category DX'] [Category DP]
    {ΨX : DX ⥤ DX'} {ΨP : DX ⥤ DP} {Dh : DX' ⥤ DP} {Lh : DP ⥤ DX'} {L1 : DX ⥤ DX}
    (adj : Dh ⊣ Lh) (e : 𝟭 DX ≅ L1) (α : ΨP ⋙ Lh ⟶ L1 ⋙ ΨX) [IsIso α] : ΨX ⋙ Dh ⟶ ΨP :=
  Functor.whiskerRight ((Functor.leftUnitor ΨX).inv ≫ Functor.whiskerRight e.hom ΨX ≫ inv α) Dh ≫
    Functor.whiskerLeft ΨP adj.counit ≫ (Functor.rightUnitor ΨP).hom

/-- The components of `openExchangeAux`. -/
lemma openExchangeAux_app {A A' B B' P P' : Type*} [Category A] [Category A']
    [Category B] [Category B'] [Category P] [Category P'] {SpA : A ⥤ A'} {SpB : B ⥤ B'}
    {Ts : P ⥤ P'} {Lu : A ⥤ B} {Ru : B ⥤ A} {Lu' : A' ⥤ B'} {Ru' : B' ⥤ A'} {LSa : A ⥤ P}
    {LSb : B ⥤ P} {LSa' : A' ⥤ P'} {LSb' : B' ⥤ P'} (adj : Lu ⊣ Ru) (adj' : Lu' ⊣ Ru')
    (α : SpB ⋙ Ru' ⟶ Ru ⋙ SpA) (hα : IsIso α) (i' : LSa' ≅ Lu' ⋙ LSb') (i : LSa ≅ Lu ⋙ LSb)
    (νY : SpB ⋙ LSb' ⟶ LSb ⋙ Ts) (K : A) :
    (openExchangeAux adj adj' α hα i' i νY).app K =
      i'.hom.app (SpA.obj K) ≫
        LSb'.map (((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ (inv α))).app K) ≫
        νY.app (Lu.obj K) ≫ Ts.map (i.inv.app K) := by
  simp [openExchangeAux]

/-- The components of `pointExchangeAux`, after the fully faithful inclusion `ιs'`. -/
lemma pointExchangeAux_app {CX CX' CP Cs Cs' DX DX' DP Ds Ds' : Type*} [Category CX]
    [Category CX'] [Category CP] [Category Cs] [Category Cs'] [Category DX] [Category DX']
    [Category DP] [Category Ds] [Category Ds'] {Sp : CX ⥤ CX'} {LSa' : CX' ⥤ Cs'}
    {LSh OLS : CX' ⥤ CP} {LSp LStp : CP ⥤ Cs'} {LSa LSta : CX ⥤ Cs} {Ts : Cs ⥤ Cs'}
    {ιX : CX ⥤ DX} {ιX' : CX' ⥤ DX'} {ιP : CP ⥤ DP} {ιs : Cs ⥤ Ds} {ιs' : Cs' ⥤ Ds'}
    (hι : ιs'.FullyFaithful) {ΨX : DX ⥤ DX'} {ΨP : DX ⥤ DP} {Ψs : Ds ⥤ Ds'} {Dh : DX' ⥤ DP}
    {Lh : DP ⥤ DX'} {L1 : DX ⥤ DX} {Rp : DP ⥤ Ds'} {Ra : DX ⥤ Ds}
    (i1 : LSa' ≅ LSh ⋙ LSp) (i2 : LSh ≅ OLS) (i3 : LSp ≅ LStp) (i4 : LSa ≅ LSta)
    (cSp : Sp ⋙ ιX' ≅ ιX ⋙ ΨX) (cO : OLS ⋙ ιP ≅ ιX' ⋙ Dh) (cR : LStp ⋙ ιs' ≅ ιP ⋙ Rp)
    (cA : LSta ⋙ ιs ≅ ιX ⋙ Ra) (cT : Ts ⋙ ιs' ≅ ιs ⋙ Ψs) (adj : Dh ⊣ Lh) (e : 𝟭 DX ≅ L1)
    (α : ΨP ⋙ Lh ⟶ L1 ⋙ ΨX) (hα : IsIso α)
    (χinv : ιX ⋙ ΨP ⋙ Rp ⟶ ιX ⋙ Ra ⋙ Ψs) (M : CX) :
    ιs'.map ((pointExchangeAux hι i1 i2 i3 i4 cSp cO cR cA cT adj e α hα χinv).app M) =
      ιs'.map (i1.hom.app (Sp.obj M) ≫ LSp.map (i2.hom.app (Sp.obj M)) ≫
          i3.hom.app (OLS.obj (Sp.obj M))) ≫
        cR.hom.app (OLS.obj (Sp.obj M)) ≫ Rp.map (cO.hom.app (Sp.obj M)) ≫
        Rp.map (Dh.map (cSp.hom.app M)) ≫ Rp.map ((pointOpenExchange adj e α).app (ιX.obj M)) ≫
        χinv.app M ≫ Ψs.map (cA.inv.app M) ≫ cT.inv.app (LSta.obj M) ≫
        ιs'.map (Ts.map (i4.inv.app M)) := by
  simp only [pointExchangeAux, NatTrans.comp_app, Functor.map_comp, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  rw [map_whiskeringRight_preimage_app]
  simp [pointOpenExchange]

/-- **The shape of `ν_X` on pushforwards**, in abstract categories: for
`ν = openExchangeAux adjU adjU' αU hαU i' i (pointExchangeAux …)` (the shape of `ν_X`) and
`G N = g_* N` (`N₀ = ιB N`), if the mate `ν_u` of `αU⁻¹` is the ambient `νuA` through the
inclusions (`hνu`), and the ambient composite
`Rp'_*(h'_!(νuA)) ∘ Rp'_*(h'_!(Ψ_Y(eU))) ∘ Rp'_*(ν_h) ∘ χ₀ ∘ Ψ_s(Ra_*(eh)) ∘ conj⁻¹` at
`(ug)_* N₀` is identified with the pushforward exchange `χphg` for every right inverse `χ₀` of `χp`
(`hC`), then so is `ν` at `G N`, read through the composition isomorphisms. Here `M₁` is a bounded
constructible object with `ιX M₁ ≅ (ug)_* N₀` (`c₁`), used to move the inverse of `χp`. -/
lemma openPointExchangeAux_app_comp_aux_of_eq {A A' CX CX' CP Cs Cs' CB DA DA' DX DX' DP Ds Ds'
    DB DB' : Type*} [Category A] [Category A'] [Category CX] [Category CX'] [Category CP]
    [Category Cs] [Category Cs'] [Category CB] [Category DA] [Category DA'] [Category DX]
    [Category DX'] [Category DP] [Category Ds] [Category Ds'] [Category DB] [Category DB']
    {SpA : A ⥤ A'} {Sp : CX ⥤ CX'} {Ts : Cs ⥤ Cs'} {Lu : A ⥤ CX} {Ru : CX ⥤ A}
    {Lu' : A' ⥤ CX'} {Ru' : CX' ⥤ A'} {LSa : A ⥤ Cs} {LSb : CX ⥤ Cs} {LSa' : A' ⥤ Cs'}
    {LSb' : CX' ⥤ Cs'} (adjU : Lu ⊣ Ru) (adjU' : Lu' ⊣ Ru') (αU : Sp ⋙ Ru' ⟶ Ru ⋙ SpA)
    (hαU : IsIso αU) (i' : LSa' ≅ Lu' ⋙ LSb') (i : LSa ≅ Lu ⋙ LSb)
    {LSh OLS : CX' ⥤ CP} {LSp LStp : CP ⥤ Cs'} {LSta : CX ⥤ Cs}
    {ιA : A ⥤ DA} {ιA' : A' ⥤ DA'} {ιX : CX ⥤ DX} {ιX' : CX' ⥤ DX'} {ιP : CP ⥤ DP}
    {ιs : Cs ⥤ Ds} {ιs' : Cs' ⥤ Ds'} {ιB : CB ⥤ DB} (hι : ιs'.FullyFaithful)
    (hιX : ιX.FullyFaithful) {ΨA : DA ⥤ DA'} {ΨX : DX ⥤ DX'} {ΨP : DX ⥤ DP} {Ψs : Ds ⥤ Ds'}
    {ΨB : DB ⥤ DB'} {Dh : DX' ⥤ DP} {Lh : DP ⥤ DX'} {L1 : DX ⥤ DX} {Rp : DP ⥤ Ds'}
    {Ra : DX ⥤ Ds} (i1 : LSb' ≅ LSh ⋙ LSp) (i2 : LSh ≅ OLS) (i3 : LSp ≅ LStp) (i4 : LSb ≅ LSta)
    (cSp : Sp ⋙ ιX' ≅ ιX ⋙ ΨX) (cO : OLS ⋙ ιP ≅ ιX' ⋙ Dh) (cR : LStp ⋙ ιs' ≅ ιP ⋙ Rp)
    (cA : LSta ⋙ ιs ≅ ιX ⋙ Ra) (cT : Ts ⋙ ιs' ≅ ιs ⋙ Ψs) (adj : Dh ⊣ Lh) (e : 𝟭 DX ≅ L1)
    (α : ΨP ⋙ Lh ⟶ L1 ⋙ ΨX) (hα : IsIso α) (χp : Ra ⋙ Ψs ⟶ ΨP ⋙ Rp) (hφp : IsIsoOn ιX χp)
    (ν : SpA ⋙ LSa' ⟶ LSa ⋙ Ts)
    (hν : ν = openExchangeAux adjU adjU' αU hαU i' i
      (pointExchangeAux hι i1 i2 i3 i4 cSp cO cR cA cT adj e α hα (invOnSubcategory ιX χp hφp)))
    {DuS : DA ⥤ DX} {DuS' : DA' ⥤ DX'} (cSpA : SpA ⋙ ιA' ≅ ιA ⋙ ΨA) (cLu : Lu ⋙ ιX ≅ ιA ⋙ DuS)
    (cLu' : Lu' ⋙ ιX' ≅ ιA' ⋙ DuS') (νuA : ΨA ⋙ DuS' ⟶ DuS ⋙ ΨX)
    (hνu : ∀ K, ιX'.map (((mateEquiv adjU adjU').symm
        (TwoSquare.mk _ _ _ _ (inv αU))).app K) =
      cLu'.hom.app (SpA.obj K) ≫ DuS'.map (cSpA.hom.app K) ≫ νuA.app (ιA.obj K) ≫
        ΨX.map (cLu.inv.app K) ≫ cSp.inv.app (Lu.obj K))
    {G : CB ⥤ A} {Rg : DB ⥤ DA} (cG : G ⋙ ιA ≅ ιB ⋙ Rg) {Rg₁ Rhg : DB ⥤ DX} {Rphg : DB ⥤ Ds}
    {Rg' : DB' ⥤ DA'} {Rug' : DB' ⥤ DX'} {Rhug' : DB' ⥤ DP} {Rphg' : DB' ⥤ Ds'}
    (eU : Rg ⋙ DuS ⟶ Rg₁) (eh : Rg₁ ⟶ Rhg) (conj : Rphg ≅ Rhg ⋙ Ra)
    (χg : Rg ⋙ ΨA ⟶ ΨB ⋙ Rg') (eU' : Rg' ⋙ DuS' ⟶ Rug') (eH' : Rug' ⋙ Dh ⟶ Rhug')
    (conj' : Rphg' ≅ Rhug' ⋙ Rp) (χphg : Rphg ⋙ Ψs ⟶ ΨB ⋙ Rphg') (N : CB) (M₁ : CX)
    (c₁ : ιX.obj M₁ ≅ Rg₁.obj (ιB.obj N))
    (hC : ∀ χ₀ : (ΨP ⋙ Rp).obj (Rg₁.obj (ιB.obj N)) ⟶ (Ra ⋙ Ψs).obj (Rg₁.obj (ιB.obj N)),
      χ₀ ≫ χp.app (Rg₁.obj (ιB.obj N)) = 𝟙 _ →
        Rp.map (Dh.map (νuA.app (Rg.obj (ιB.obj N)) ≫ ΨX.map (eU.app (ιB.obj N)))) ≫
            Rp.map ((pointOpenExchange adj e α).app (Rg₁.obj (ιB.obj N))) ≫ χ₀ ≫
            Ψs.map (Ra.map (eh.app (ιB.obj N)) ≫ conj.inv.app (ιB.obj N)) ≫
            χphg.app (ιB.obj N) =
          Rp.map (Dh.map (DuS'.map (χg.app (ιB.obj N)) ≫ eU'.app (ΨB.obj (ιB.obj N))) ≫
            eH'.app (ΨB.obj (ιB.obj N))) ≫ conj'.inv.app (ΨB.obj (ιB.obj N))) :
    ιs'.map (i3.inv.app (OLS.obj (Lu'.obj (SpA.obj (G.obj N)))) ≫
        LSp.map (i2.inv.app (Lu'.obj (SpA.obj (G.obj N)))) ≫
        i1.inv.app (Lu'.obj (SpA.obj (G.obj N))) ≫ i'.inv.app (SpA.obj (G.obj N))) ≫
        ιs'.map (ν.app (G.obj N)) ≫ cT.hom.app (LSa.obj (G.obj N)) ≫
        Ψs.map (ιs.map (i.hom.app (G.obj N) ≫ i4.hom.app (Lu.obj (G.obj N))) ≫
          cA.hom.app (Lu.obj (G.obj N)) ≫ Ra.map (cLu.hom.app (G.obj N)) ≫
          Ra.map (DuS.map (cG.hom.app N)) ≫ Ra.map (eU.app (ιB.obj N)) ≫
          Ra.map (eh.app (ιB.obj N)) ≫ conj.inv.app (ιB.obj N)) ≫ χphg.app (ιB.obj N) =
      cR.hom.app (OLS.obj (Lu'.obj (SpA.obj (G.obj N)))) ≫
        Rp.map (cO.hom.app (Lu'.obj (SpA.obj (G.obj N))) ≫
          Dh.map (cLu'.hom.app (SpA.obj (G.obj N))) ≫ Dh.map (DuS'.map (cSpA.hom.app (G.obj N))) ≫
          Dh.map (DuS'.map (ΨA.map (cG.hom.app N))) ≫ Dh.map (DuS'.map (χg.app (ιB.obj N))) ≫
          Dh.map (eU'.app (ΨB.obj (ιB.obj N))) ≫ eH'.app (ΨB.obj (ιB.obj N))) ≫
        conj'.inv.app (ΨB.obj (ιB.obj N)) := by
  subst hν
  set K := G.obj N
  set M := Lu.obj K
  set N₀ := ιB.obj N
  set νh := pointOpenExchange adj e α
  set χinv := invOnSubcategory ιX χp hφp
  -- the core identity on the ambient categories
  let φ : ιX.obj M ⟶ Rg₁.obj N₀ := cLu.hom.app K ≫ DuS.map (cG.hom.app N) ≫ eU.app N₀
  let χ₀ := Rp.map (ΨP.map c₁.inv) ≫ χinv.app M₁ ≫ Ψs.map (Ra.map c₁.hom)
  have hχ₀ : χ₀ ≫ χp.app (Rg₁.obj N₀) = 𝟙 _ := by
    have hn := χp.naturality c₁.hom
    simp only [Functor.comp_map] at hn
    simp only [χ₀, Category.assoc, hn]
    rw [reassoc_of% (invOnSubcategory_app_comp ιX χp hφp M₁), ← Rp.map_comp, ← ΨP.map_comp,
      Iso.inv_hom_id, ΨP.map_id, Rp.map_id]
  have hχ : χinv.app M ≫ Ψs.map (Ra.map φ) = Rp.map (ΨP.map φ) ≫ χ₀ := by
    have hn := χinv.naturality (hιX.preimage (φ ≫ c₁.inv))
    simp only [Functor.comp_map, hιX.map_preimage] at hn
    simp only [χ₀, ← Category.assoc, ← Functor.map_comp]
    rw [hn]
    rw [Category.assoc, ← Ψs.map_comp, ← Ra.map_comp, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  have hcore : Rp.map (Dh.map (νuA.app (ιA.obj K) ≫ ΨX.map (cLu.inv.app K))) ≫
      Rp.map (νh.app (ιX.obj M)) ≫ χinv.app M ≫
      Ψs.map (Ra.map (cLu.hom.app K) ≫ Ra.map (DuS.map (cG.hom.app N)) ≫ Ra.map (eU.app N₀) ≫
        Ra.map (eh.app N₀) ≫ conj.inv.app N₀) ≫ χphg.app N₀ =
      Rp.map (Dh.map (DuS'.map (ΨA.map (cG.hom.app N)) ≫ DuS'.map (χg.app N₀) ≫
        eU'.app (ΨB.obj N₀)) ≫ eH'.app (ΨB.obj N₀)) ≫ conj'.inv.app (ΨB.obj N₀) := by
    have h1 : Ψs.map (Ra.map (cLu.hom.app K) ≫ Ra.map (DuS.map (cG.hom.app N)) ≫
        Ra.map (eU.app N₀) ≫ Ra.map (eh.app N₀) ≫ conj.inv.app N₀) =
        Ψs.map (Ra.map φ) ≫ Ψs.map (Ra.map (eh.app N₀) ≫ conj.inv.app N₀) := by
      simp [φ]
    have h2 := νh.naturality φ
    have h3 := νuA.naturality (cG.hom.app N)
    simp only [Functor.comp_map] at h2 h3
    rw [h1, Category.assoc, reassoc_of% hχ, ← Rp.map_comp_assoc, ← Rp.map_comp_assoc,
      Category.assoc, ← h2]
    have h4 : νuA.app (ιA.obj K) ≫ ΨX.map (cLu.inv.app K) ≫ ΨX.map φ =
        DuS'.map (ΨA.map (cG.hom.app N)) ≫ νuA.app (Rg.obj N₀) ≫ ΨX.map (eU.app N₀) := by
      simp only [φ, ← ΨX.map_comp, Iso.inv_hom_id_app_assoc]
      rw [ΨX.map_comp, reassoc_of% h3]
    rw [← Dh.map_comp_assoc, Category.assoc, h4]
    have := hC χ₀ hχ₀
    simp only [Functor.map_comp, Category.assoc] at this ⊢
    rw [this]
  rw [openExchangeAux_app]
  simp only [Functor.map_comp, Category.assoc]
  rw [pointExchangeAux_app]
  simp only [Functor.map_comp, Category.assoc]
  set m := ((mateEquiv adjU adjU').symm (TwoSquare.mk Ru Sp SpA Ru' (inv αU))).app K
  have n1 := i1.hom.naturality m
  have n2 := i2.hom.naturality m
  have n3 := i3.hom.naturality (OLS.map m)
  have n4 := cR.hom.naturality (OLS.map m)
  have n5 := cO.hom.naturality m
  simp only [Functor.comp_map, Functor.comp_obj] at n1 n2 n3 n4 n5
  have hB0 : i3.inv.app (OLS.obj (Lu'.obj (SpA.obj K))) ≫
      LSp.map (i2.inv.app (Lu'.obj (SpA.obj K))) ≫ i1.inv.app (Lu'.obj (SpA.obj K)) ≫
      i'.inv.app (SpA.obj K) ≫ i'.hom.app (SpA.obj K) ≫ LSb'.map m ≫ i1.hom.app (Sp.obj M) ≫
      LSp.map (i2.hom.app (Sp.obj M)) ≫ i3.hom.app (OLS.obj (Sp.obj M)) =
      LStp.map (OLS.map m) := by
    rw [Iso.inv_hom_id_app_assoc, reassoc_of% n1, Iso.inv_hom_id_app_assoc,
      ← LSp.map_comp_assoc, ← LSp.map_comp_assoc, Category.assoc, n2, Iso.inv_hom_id_app_assoc,
      n3, Iso.inv_hom_id_app_assoc]
  have hB : ιs'.map (i3.inv.app (OLS.obj (Lu'.obj (SpA.obj K)))) ≫
      ιs'.map (LSp.map (i2.inv.app (Lu'.obj (SpA.obj K)))) ≫
      ιs'.map (i1.inv.app (Lu'.obj (SpA.obj K))) ≫ ιs'.map (i'.inv.app (SpA.obj K)) ≫
      ιs'.map (i'.hom.app (SpA.obj K)) ≫ ιs'.map (LSb'.map m) ≫
      ιs'.map (i1.hom.app (Sp.obj M)) ≫ ιs'.map (LSp.map (i2.hom.app (Sp.obj M))) ≫
      ιs'.map (i3.hom.app (OLS.obj (Sp.obj M))) ≫ cR.hom.app (OLS.obj (Sp.obj M)) ≫
      Rp.map (cO.hom.app (Sp.obj M)) =
      cR.hom.app (OLS.obj (Lu'.obj (SpA.obj K))) ≫ Rp.map (cO.hom.app (Lu'.obj (SpA.obj K))) ≫
        Rp.map (Dh.map (ιX'.map m)) := by
    simp only [← ιs'.map_comp_assoc]
    rw [hB0, reassoc_of% n4, ← Rp.map_comp, ← Rp.map_comp, n5]
  have hT : ιs'.map (Ts.map (i4.inv.app M)) ≫ ιs'.map (Ts.map (i.inv.app K)) ≫
      cT.hom.app (LSa.obj K) ≫ Ψs.map (ιs.map (i.hom.app K)) ≫ Ψs.map (ιs.map (i4.hom.app M)) =
      cT.hom.app (LSta.obj M) := by
    have n6 := cT.hom.naturality (i4.inv.app M ≫ i.inv.app K)
    simp only [Functor.comp_map] at n6
    simp only [← Functor.map_comp_assoc, ← Functor.map_comp]
    rw [reassoc_of% n6]
    simp
  rw [reassoc_of% hB, reassoc_of% hT, Iso.inv_hom_id_app_assoc, ← Ψs.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [hνu]
  have hc : ∀ {Z} (h : Rp.obj (Dh.obj (ΨX.obj (ιX.obj M))) ⟶ Z),
      Rp.map (Dh.map (cSp.inv.app M)) ≫ Rp.map (Dh.map (cSp.hom.app M)) ≫ h = h := by
    intro Z h
    rw [← Rp.map_comp_assoc, ← Dh.map_comp, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [Functor.map_comp, Category.assoc] at hcore ⊢
  rw [hc, hcore]
end AlgebraicGeometry.ProEtale.CondensedRing
