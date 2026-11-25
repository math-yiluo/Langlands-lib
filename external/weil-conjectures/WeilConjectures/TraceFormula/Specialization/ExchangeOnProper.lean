/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.HomComp
public import WeilConjectures.TraceFormula.Specialization.SupportCompactSupportExchange

/-!

# The compact-support exchange of a compactification on proper pieces

Let `ν_f = χ_p⁻¹ ∘ Rp'_*(ν_h)` be the compact-support exchange of a compactified morphism of models
`f = p ∘ h` (`ProEtale.CondensedRing.compactSupportExchangeOfCompactification`), with `h` an open
immersion, `ν_h` the adjoint of `α_h⁻¹`, and `p` proper. Let `g : M_B ⟶ M_C` be a morphism of
models such that `h ∘ g` is again proper (closed in the compactification). Then on objects
`g_* N`, `ν_f` is the inverse proper exchange of `f ∘ g = p ∘ (h ∘ g)`:
```
ν_f(g_* N) ∘ f'_!(χ_g(N)⁻¹) = χ_{f∘g}(N)⁻¹
```
through `f'_! g'_* ≅ p'_* h'_! g'_* ≅ p'_* (hg)'_* ≅ (f∘g)'_*` and similarly over `k`. This is the
key lemma of step (B) of Varshavsky's argument.

## Main results

In arbitrary categories (namespace `AlgebraicGeometry.ProEtale.CondensedRing`):
- `exchange_baseChange_aux`: the composition law `α_{hg} = α_g(h^*) ∘ g'^* α_h` of the pullback
  exchanges implies that the base change maps `b : h^* (hg)_* ⟶ g_*` (characterized by their
  adjoints `g^* h^* (hg)_* ≅ (hg)^* (hg)_* ⟶ 𝟭`) intertwine the pushforward exchanges:
  `χ_g ∘ Ψ_C(b) ∘ α_h = b' ∘ h'^*(χ_{hg})`;
- `lowerShriekExchangeOfInv_app_comp_aux`: if `e : h_! g_* ⟶ (hg)_*` is adjoint to a right
  inverse of `b`, then `χ_{hg} ∘ Ψ_P(e) ∘ ν_h(g_* N) = e' ∘ h'_!(χ_g)`;
- `compactSupportExchange_comp_aux`: with the composition law `χ_{p(hg)} = p'_*(χ_{hg}) ∘
  χ_p((hg)_*)` of the pushforward exchanges, `χ_p⁻¹ ∘ p'_*(ν_h)` at `g_* N` is the pushforward
  exchange of `p ∘ (h ∘ g)` after `p'_* h'_!(χ_g)`;
- `compactSupportExchangeAux_app`, `compactSupportExchangeAux_app_comp_aux`: the same for the
  shape `compactSupportExchangeAux` of `ν_f` on bounded constructible complexes, through the
  compatibilities of the restricted functors with the inclusions.

For nearby cycles models (ambient derived categories):
- `closedBaseChange`: the base change map `Lh^* R(hg)_* ⟶ Rg_*` of the square `(𝟙, g, hg, h)`,
  invertible for `h` weakly étale and mono (`isIso_closedBaseChange`, by weakly étale base
  change); `closedExtension`: the adjoint `h_! g_* ⟶ (hg)_*` of its inverse;
- `NearbyCyclesModel.Hom.compactSupportExchange_comp_app`: the key lemma for morphisms of models
  `φ_g, φ_h, φ_p` and their composites.

The invertibility of `closedExtension` (`h_! ≅ h_*` on complexes supported on the closed subset
`B`) is not needed for these identities.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Unit

variable {DC DP SC SP : Type*} [Category DC] [Category DP] [Category SC] [Category SP]
  {ΨC : DC ⥤ SC} {ΨP : DP ⥤ SP} {Dh : DC ⥤ DP} {Lh : DP ⥤ DC} {Dh' : SC ⥤ SP} {Lh' : SP ⥤ SC}

/-- The adjoint of `ν_h = lowerShriekExchangeOfInv adj adj' α` under `Dh' ⊣ Lh'` is
`α⁻¹(Dh) ∘ Ψ_C(η)`. -/
lemma unit_comp_lowerShriekExchangeOfInv_app (adj : Dh ⊣ Lh) (adj' : Dh' ⊣ Lh')
    (α : ΨP ⋙ Lh' ⟶ Lh ⋙ ΨC) [IsIso α] (X : DC) :
    adj'.unit.app (ΨC.obj X) ≫ Lh'.map ((lowerShriekExchangeOfInv adj adj' α).app X) =
      ΨC.map (adj.unit.app X) ≫ (inv α).app (Dh.obj X) := by
  simp only [lowerShriekExchangeOfInv, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.comp_obj, Functor.id_obj, Category.id_comp, Category.comp_id, Functor.map_comp]
  simp only [← Functor.map_comp]
  rw [← Adjunction.homEquiv_unit, ← Adjunction.homEquiv_counit, Equiv.apply_symm_apply]

end Unit

section Shape

variable {DC DC' DP DP' CC CC' CP CP' Cs Cs' Ds Ds' : Type*} [Category DC] [Category DC']
  [Category DP] [Category DP'] [Category CC] [Category CC'] [Category CP] [Category CP']
  [Category Cs] [Category Cs'] [Category Ds] [Category Ds']

omit [Category DC] [Category DC'] [Category DP] [Category DP'] [Category CP] [Category CP']
  [Category Cs] [Category Ds] in
lemma map_whiskeringRight_preimage_app {ιs' : Cs' ⥤ Ds'} (hι : ιs'.FullyFaithful) {F G : CC ⥤ Cs'}
    (η : F ⋙ ιs' ⟶ G ⋙ ιs') (M : CC) :
    ιs'.map (((hι.whiskeringRight CC).preimage η).app M) = η.app M :=
  NatTrans.congr_app ((hι.whiskeringRight CC).map_preimage η) M

/-- The components of `compactSupportExchangeAux`, after the fully faithful inclusion `ιs'`. -/
lemma compactSupportExchangeAux_app {Sp : CC ⥤ CC'} {LSf' : CC' ⥤ Cs'} {LSf : CC ⥤ Cs}
    {Ts : Cs ⥤ Cs'} {OLS : CC ⥤ CP} {OLS' : CC' ⥤ CP'} {LStp : CP ⥤ Cs} {LStp' : CP' ⥤ Cs'}
    {ιC : CC ⥤ DC} {ιC' : CC' ⥤ DC'} {ιP : CP ⥤ DP} {ιP' : CP' ⥤ DP'} {ιs : Cs ⥤ Ds}
    {ιs' : Cs' ⥤ Ds'} (hι : ιs'.FullyFaithful) {ΨC : DC ⥤ DC'} {ΨP : DP ⥤ DP'} {Ψs : Ds ⥤ Ds'}
    {Dh : DC ⥤ DP} {Dh' : DC' ⥤ DP'} {Rp : DP ⥤ Ds} {Rp' : DP' ⥤ Ds'}
    (i₁ : LSf' ≅ OLS' ⋙ LStp') (i₂ : LSf ≅ OLS ⋙ LStp)
    (cSp : Sp ⋙ ιC' ≅ ιC ⋙ ΨC) (cO' : OLS' ⋙ ιP' ≅ ιC' ⋙ Dh') (cR' : LStp' ⋙ ιs' ≅ ιP' ⋙ Rp')
    (cO : OLS ⋙ ιP ≅ ιC ⋙ Dh) (cR : LStp ⋙ ιs ≅ ιP ⋙ Rp) (cT : Ts ⋙ ιs' ≅ ιs ⋙ Ψs)
    (νh : ΨC ⋙ Dh' ⟶ Dh ⋙ ΨP) (χinv : ιP ⋙ ΨP ⋙ Rp' ⟶ ιP ⋙ Rp ⋙ Ψs) (M : CC) :
    ιs'.map ((compactSupportExchangeAux hι i₁ i₂ cSp cO' cR' cO cR cT νh χinv).app M) =
      ιs'.map (i₁.hom.app (Sp.obj M)) ≫ cR'.hom.app (OLS'.obj (Sp.obj M)) ≫
        Rp'.map (cO'.hom.app (Sp.obj M)) ≫ Rp'.map (Dh'.map (cSp.hom.app M)) ≫
        Rp'.map (νh.app (ιC.obj M)) ≫ Rp'.map (ΨP.map (cO.inv.app M)) ≫ χinv.app (OLS.obj M) ≫
        Ψs.map (cR.inv.app (OLS.obj M)) ≫ cT.inv.app (LStp.obj (OLS.obj M)) ≫
        ιs'.map (Ts.map (i₂.inv.app M)) := by
  simp only [compactSupportExchangeAux, NatTrans.comp_app, Functor.map_comp,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [map_whiskeringRight_preimage_app]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj, Functor.comp_map, Category.assoc]

/-- `invOnSubcategory` is a right inverse of `χ` on the objects of `ι`. -/
@[reassoc]
lemma invOnSubcategory_app_comp {C D E : Type*} [Category C] [Category D] [Category E]
    (ι : C ⥤ D) {F G : D ⥤ E} (χ : F ⟶ G) (h : IsIsoOn ι χ) (K : C) :
    (invOnSubcategory ι χ h).app K ≫ χ.app (ι.obj K) = 𝟙 _ := by
  have : IsIso (Functor.whiskerLeft ι χ) := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ h
  exact NatTrans.congr_app (IsIso.inv_hom_id (Functor.whiskerLeft ι χ)) K

/-- **The shape of `ν_f` on pushforwards**, in abstract categories: if the ambient composite
`χ_p⁻¹ ∘ Rp'_*(ν_h)` at `Rg N₀` (`N₀ = ιB N`) is identified with the pushforward exchange `χ_{fg}`
for every right inverse `χ₀` of `χ_p` (`hC`, e.g. `compactSupportExchange_comp_aux`), then so is
`ν_f = compactSupportExchangeAux …` at `G N`, through the compatibilities of the restricted functors
with the inclusions. -/
lemma compactSupportExchangeAux_app_comp_aux {CB DB DB' : Type*} [Category CB] [Category DB]
    [Category DB'] {Sp : CC ⥤ CC'} {LSf' : CC' ⥤ Cs'} {LSf : CC ⥤ Cs}
    {Ts : Cs ⥤ Cs'} {OLS : CC ⥤ CP} {OLS' : CC' ⥤ CP'} {LStp : CP ⥤ Cs} {LStp' : CP' ⥤ Cs'}
    {ιC : CC ⥤ DC} {ιC' : CC' ⥤ DC'} {ιP : CP ⥤ DP} {ιP' : CP' ⥤ DP'} {ιs : Cs ⥤ Ds}
    {ιs' : Cs' ⥤ Ds'} (hι : ιs'.FullyFaithful) {ΨC : DC ⥤ DC'} {ΨP : DP ⥤ DP'} {Ψs : Ds ⥤ Ds'}
    {Dh : DC ⥤ DP} {Dh' : DC' ⥤ DP'} {Rp : DP ⥤ Ds} {Rp' : DP' ⥤ Ds'}
    (i₁ : LSf' ≅ OLS' ⋙ LStp') (i₂ : LSf ≅ OLS ⋙ LStp)
    (cSp : Sp ⋙ ιC' ≅ ιC ⋙ ΨC) (cO' : OLS' ⋙ ιP' ≅ ιC' ⋙ Dh') (cR' : LStp' ⋙ ιs' ≅ ιP' ⋙ Rp')
    (cO : OLS ⋙ ιP ≅ ιC ⋙ Dh) (cR : LStp ⋙ ιs ≅ ιP ⋙ Rp) (cT : Ts ⋙ ιs' ≅ ιs ⋙ Ψs)
    (νh : ΨC ⋙ Dh' ⟶ Dh ⋙ ΨP) (χp : Rp ⋙ Ψs ⟶ ΨP ⋙ Rp') (hφp : IsIsoOn ιP χp)
    {ιB : CB ⥤ DB} {G : CB ⥤ CC} {Rg : DB ⥤ DC} (cG : G ⋙ ιC ≅ ιB ⋙ Rg) {ΨB : DB ⥤ DB'}
    {Rg' : DB' ⥤ DC'} {Rhg : DB ⥤ DP} {Rhg' : DB' ⥤ DP'} {Rphg : DB ⥤ Ds} {Rphg' : DB' ⥤ Ds'}
    (e : Rg ⋙ Dh ⟶ Rhg) (e' : Rg' ⋙ Dh' ⟶ Rhg') (conj : Rphg ≅ Rhg ⋙ Rp)
    (conj' : Rphg' ≅ Rhg' ⋙ Rp') (χg : Rg ⋙ ΨC ⟶ ΨB ⋙ Rg') (χphg : Rphg ⋙ Ψs ⟶ ΨB ⋙ Rphg')
    (N : CB)
    (hC : ∀ χ₀ : (ΨP ⋙ Rp').obj (Dh.obj (Rg.obj (ιB.obj N))) ⟶
        (Rp ⋙ Ψs).obj (Dh.obj (Rg.obj (ιB.obj N))),
      χ₀ ≫ χp.app (Dh.obj (Rg.obj (ιB.obj N))) = 𝟙 _ →
        Rp'.map (νh.app (Rg.obj (ιB.obj N))) ≫ χ₀ ≫
            Ψs.map (Rp.map (e.app (ιB.obj N)) ≫ conj.inv.app (ιB.obj N)) ≫
            χphg.app (ιB.obj N) =
          Rp'.map (Dh'.map (χg.app (ιB.obj N)) ≫ e'.app (ΨB.obj (ιB.obj N))) ≫
            conj'.inv.app (ΨB.obj (ιB.obj N))) :
    ιs'.map (i₁.inv.app (Sp.obj (G.obj N))) ≫
        ιs'.map ((compactSupportExchangeAux hι i₁ i₂ cSp cO' cR' cO cR cT νh
          (invOnSubcategory ιP χp hφp)).app (G.obj N)) ≫ cT.hom.app (LSf.obj (G.obj N)) ≫
        Ψs.map (ιs.map (i₂.hom.app (G.obj N)) ≫ cR.hom.app (OLS.obj (G.obj N)) ≫
          Rp.map (cO.hom.app (G.obj N)) ≫ Rp.map (Dh.map (cG.hom.app N)) ≫
          Rp.map (e.app (ιB.obj N)) ≫ conj.inv.app (ιB.obj N)) ≫ χphg.app (ιB.obj N) =
      cR'.hom.app (OLS'.obj (Sp.obj (G.obj N))) ≫
        Rp'.map (cO'.hom.app (Sp.obj (G.obj N)) ≫ Dh'.map (cSp.hom.app (G.obj N)) ≫
          Dh'.map (ΨC.map (cG.hom.app N)) ≫ Dh'.map (χg.app (ιB.obj N)) ≫
          e'.app (ΨB.obj (ιB.obj N))) ≫ conj'.inv.app (ΨB.obj (ιB.obj N)) := by
  set M := G.obj N
  let u : ιP.obj (OLS.obj M) ≅ Dh.obj (Rg.obj (ιB.obj N)) := cO.app M ≪≫ Dh.mapIso (cG.app N)
  have hu := hC (Rp'.map (ΨP.map u.inv) ≫ (invOnSubcategory ιP χp hφp).app (OLS.obj M) ≫
    Ψs.map (Rp.map u.hom)) (by
    have hn := χp.naturality u.hom
    simp only [Functor.comp_map] at hn
    rw [Category.assoc, Category.assoc, hn,
      reassoc_of% (invOnSubcategory_app_comp ιP χp hφp (OLS.obj M)), ← Functor.map_comp,
      ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id]
    rfl)
  have hν := νh.naturality (cG.hom.app N)
  have hT := cT.hom.naturality (i₂.inv.app M)
  simp only [Functor.comp_map] at hν hT
  rw [compactSupportExchangeAux_app]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% hT]
  erw [Iso.inv_hom_id_app_assoc]
  rw [← Ψs.map_comp_assoc, ← Ψs.map_comp_assoc, Category.assoc, ← ιs.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
  have k1 : νh.app (ιC.obj M) ≫ ΨP.map (cO.inv.app M) =
      Dh'.map (ΨC.map (cG.hom.app N)) ≫ νh.app (Rg.obj (ιB.obj N)) ≫ ΨP.map u.inv := by
    have hv : Dh.map (cG.hom.app N) ≫ u.inv = cO.inv.app M := by
      simp only [u, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv]
      rw [← Dh.map_comp_assoc, Iso.hom_inv_id_app]
      erw [CategoryTheory.Functor.map_id, Category.id_comp]
    erw [reassoc_of% hν]
    rw [← ΨP.map_comp, hv]
  have k2 : Rp.map (cO.hom.app M ≫ Dh.map (cG.hom.app N) ≫ e.app (ιB.obj N)) =
      Rp.map u.hom ≫ Rp.map (e.app _) := by
    simp [u]
  rw [k1, k2]
  simp only [Functor.map_comp, Category.assoc] at hu ⊢
  rw [hu]

end Shape

section Abstract

variable {DB DC DP SB SC SP : Type*} [Category DB] [Category DC] [Category DP] [Category SB]
  [Category SC] [Category SP]
  {Lg : DC ⥤ DB} {Rg : DB ⥤ DC} {Lh : DP ⥤ DC} {Lhg : DP ⥤ DB} {Rhg : DB ⥤ DP}
  {Lg' : SC ⥤ SB} {Rg' : SB ⥤ SC} {Lh' : SP ⥤ SC} {Lhg' : SP ⥤ SB} {Rhg' : SB ⥤ SP}
  (adjg : Lg ⊣ Rg) (adjhg : Lhg ⊣ Rhg) (adjg' : Lg' ⊣ Rg') (adjhg' : Lhg' ⊣ Rhg')
  (c : Lhg ≅ Lh ⋙ Lg) (c' : Lhg' ≅ Lh' ⋙ Lg')
  {ΨB : DB ⥤ SB} {ΨC : DC ⥤ SC} {ΨP : DP ⥤ SP}
  (αg : ΨC ⋙ Lg' ⟶ Lg ⋙ ΨB) (αh : ΨP ⋙ Lh' ⟶ Lh ⋙ ΨC) (αhg : ΨP ⋙ Lhg' ⟶ Lhg ⋙ ΨB)
  (hα : ∀ K, αhg.app K ≫ ΨB.map (c.hom.app K) =
    c'.hom.app (ΨP.obj K) ≫ Lg'.map (αh.app K) ≫ αg.app (Lh.obj K))
  (χg : Rg ⋙ ΨC ⟶ ΨB ⋙ Rg') (hχg : χg = (mateEquiv adjg adjg' αg))
  (χhg : Rhg ⋙ ΨP ⟶ ΨB ⋙ Rhg') (hχhg : χhg = (mateEquiv adjhg adjhg' αhg))
  (b : Rhg ⋙ Lh ⟶ Rg)
  (hb : ∀ N, Lg.map (b.app N) ≫ adjg.counit.app N =
    c.inv.app (Rhg.obj N) ≫ adjhg.counit.app N)
  (b' : Rhg' ⋙ Lh' ⟶ Rg')
  (hb' : ∀ N, Lg'.map (b'.app N) ≫ adjg'.counit.app N =
    c'.inv.app (Rhg'.obj N) ≫ adjhg'.counit.app N)

include hα hχg hχhg hb hb' in
/-- **The base change maps intertwine the pushforward exchanges**: for the base change maps
`b : h^* (hg)_* ⟶ g_*` (characterized by their adjoints `g^* h^* (hg)_* ≅ (hg)^* (hg)_* ⟶ 𝟭`), the
composition law `α_{hg} = α_g(h^*) ∘ g'^* α_h` gives `χ_g ∘ Ψ_C(b) ∘ α_h = b' ∘ h'^*(χ_{hg})`. -/
lemma exchange_baseChange_aux (N : DB) :
    αh.app (Rhg.obj N) ≫ ΨC.map (b.app N) ≫ χg.app N =
      Lh'.map (χhg.app N) ≫ b'.app (ΨB.obj N) := by
  subst hχg hχhg
  apply (adjg'.homEquiv _ _).symm.injective
  have h1 := αg.naturality (b.app N)
  have h2 := c'.inv.naturality (((mateEquiv adjhg adjhg') αhg).app N)
  simp only [Functor.comp_map] at h1 h2
  have h3 : c'.inv.app (ΨP.obj (Rhg.obj N)) ≫ αhg.app (Rhg.obj N) =
      Lg'.map (αh.app (Rhg.obj N)) ≫ αg.app (Lh.obj (Rhg.obj N)) ≫
        ΨB.map (c.inv.app (Rhg.obj N)) := by
    rw [← cancel_epi (c'.hom.app _), Iso.hom_inv_id_app_assoc, ← reassoc_of% (hα _),
      ← ΨB.map_comp, Iso.hom_inv_id_app, ΨB.map_id, Category.comp_id]
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [mateEquiv_counit, hb', reassoc_of% h1, ← ΨB.map_comp, hb, ΨB.map_comp,
    ← reassoc_of% h3]
  erw [reassoc_of% h2, mateEquiv_counit]

variable {Dh : DC ⥤ DP} {Dh' : SC ⥤ SP} (adj : Dh ⊣ Lh) (adj' : Dh' ⊣ Lh') [IsIso αh]
  (e : Rg ⋙ Dh ⟶ Rhg) (he : ∀ N, adj.unit.app (Rg.obj N) ≫ Lh.map (e.app N) ≫ b.app N = 𝟙 _)
  (e' : Rg' ⋙ Dh' ⟶ Rhg')
  (he' : ∀ N, adj'.unit.app (Rg'.obj N) ≫ Lh'.map (e'.app N) ≫ b'.app N = 𝟙 _)

include hα hχg hχhg hb hb' he he' in
/-- **On `g_* N`, the exchange `ν_h` is the pushforward exchange of `h ∘ g`**: if
`e : h_! g_* ⟶ (hg)_*` is adjoint to a right inverse of the base change map `b` (for instance
the adjoint of `b⁻¹`; it is the identification of `h_!` and `h_*` on complexes supported on the
closed subset `B`, but its invertibility is not needed), then
`χ_{hg} ∘ Ψ_P(e) ∘ ν_h(g_* N) = e' ∘ h'_!(χ_g)`. -/
lemma lowerShriekExchangeOfInv_app_comp_aux (N : DB) [Mono (b'.app (ΨB.obj N))] :
    (lowerShriekExchangeOfInv adj adj' αh).app (Rg.obj N) ≫ ΨP.map (e.app N) ≫
        χhg.app N =
      Dh'.map (χg.app N) ≫ e'.app (ΨB.obj N) := by
  have hA := exchange_baseChange_aux adjg adjhg adjg' adjhg' c c' αg αh αhg hα χg hχg χhg hχhg
    b hb b' hb' N
  have hA' : (inv αh).app (Rhg.obj N) ≫ Lh'.map (χhg.app N) ≫ b'.app (ΨB.obj N) =
      ΨC.map (b.app N) ≫ χg.app N := by
    rw [← hA]
    simp
  have hn := (inv αh).naturality (e.app N)
  simp only [Functor.comp_map] at hn
  apply (adj'.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  rw [← cancel_mono (b'.app (ΨB.obj N))]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (unit_comp_lowerShriekExchangeOfInv_app adj adj' αh (Rg.obj N)),
    ← reassoc_of% hn, hA', ← ΨC.map_comp_assoc, ← ΨC.map_comp_assoc, Category.assoc, he]
  erw [ΨC.map_id, Category.id_comp]
  erw [adj'.unit_naturality_assoc]
  exact (Category.comp_id _).symm.trans (congrArg (χg.app N ≫ ·) (he' (ΨB.obj N)).symm)

variable {DY SY : Type*} [Category DY] [Category SY] {Rp : DP ⥤ DY} {Rp' : SP ⥤ SY}
  {Rphg : DB ⥤ DY} {Rphg' : SB ⥤ SY} {ΨY : DY ⥤ SY} (χp : Rp ⋙ ΨY ⟶ ΨP ⋙ Rp')
  (χphg : Rphg ⋙ ΨY ⟶ ΨB ⋙ Rphg') (conj : Rphg ≅ Rhg ⋙ Rp) (conj' : Rphg' ≅ Rhg' ⋙ Rp')
  (hcomp : ∀ E, χphg.app E ≫ conj'.hom.app (ΨB.obj E) =
    ΨY.map (conj.hom.app E) ≫ χp.app (Rhg.obj E) ≫ Rp'.map (χhg.app E))

include hα hχg hχhg hb hb' he he' hcomp in
/-- **The compact-support exchange of a compactification on proper pieces**: for
`ν_f = χ_p⁻¹ ∘ Rp'_*(ν_h)` (`χinv` a right inverse of `χ_p` at `h_! g_* N`), the composite
`ν_f(g_* N) : p'_* h'_! Ψ_C g_* N ⟶ Ψ_Y p_* h_! g_* N`, read through `e : h_! g_* ≅ (hg)_*` and
`(p(hg))_* ≅ p_* (hg)_*`, is the pushforward exchange of `p ∘ (h ∘ g)` after `p'_* h'_!(χ_g)`. -/
lemma compactSupportExchange_comp_aux (N : DB) [Mono (b'.app (ΨB.obj N))]
    (χinv : (ΨP ⋙ Rp').obj (Dh.obj (Rg.obj N)) ⟶ (Rp ⋙ ΨY).obj (Dh.obj (Rg.obj N)))
    (hχinv : χinv ≫ χp.app (Dh.obj (Rg.obj N)) = 𝟙 _) :
    Rp'.map ((lowerShriekExchangeOfInv adj adj' αh).app (Rg.obj N)) ≫ χinv ≫
        ΨY.map (Rp.map (e.app N) ≫ conj.inv.app N) ≫ χphg.app N =
      Rp'.map (Dh'.map (χg.app N) ≫ e'.app (ΨB.obj N)) ≫ conj'.inv.app (ΨB.obj N) := by
  have hB := lowerShriekExchangeOfInv_app_comp_aux adjg adjhg adjg' adjhg' c c' αg αh αhg hα χg
    hχg χhg hχhg b hb b' hb' adj adj' e he e' he' N
  have hc : ΨY.map (conj.inv.app N) ≫ χphg.app N =
      χp.app (Rhg.obj N) ≫ Rp'.map (χhg.app N) ≫ conj'.inv.app (ΨB.obj N) := by
    rw [← cancel_mono (conj'.hom.app (ΨB.obj N)), Category.assoc, hcomp, ← ΨY.map_comp_assoc,
      Iso.inv_hom_id_app, ΨY.map_id, Category.id_comp, Category.assoc, Category.assoc,
      Iso.inv_hom_id_app]
    exact congrArg (χp.app (Rhg.obj N) ≫ ·) (Category.comp_id (Rp'.map (χhg.app N))).symm
  have hn := χp.naturality (e.app N)
  simp only [Functor.comp_map] at hn
  rw [ΨY.map_comp, Category.assoc, hc, reassoc_of% hn, reassoc_of% hχinv, ← hB]
  simp only [Functor.map_comp, Category.assoc]

end Abstract
/-- The adjoint of the base change map of a square `(𝟙, g, hg, h)` with `L(𝟙)^* ≅ 𝟭`, in abstract
categories. -/
lemma map_exchangeRight_app_comp_counit_aux {DB DC DP : Type*} [Category DB] [Category DC]
    [Category DP] {Lg : DC ⥤ DB} {Rg : DB ⥤ DC} {Lh : DP ⥤ DC} {Lhg : DP ⥤ DB} {Rhg : DB ⥤ DP}
    {L1 : DB ⥤ DB} (adjg : Lg ⊣ Rg) (adjhg : Lhg ⊣ Rhg) (i1 : L1 ≅ 𝟭 DB)
    (θ : Lh ⋙ Lg ≅ Lhg ⋙ L1) (c : Lhg ≅ Lh ⋙ Lg)
    (hθ : ∀ K, θ.hom.app K ≫ i1.hom.app (Lhg.obj K) = c.inv.app K) (N : DB) :
    Lg.map ((Adjunction.exchangeRight adjhg adjg θ ≫ Functor.whiskerRight i1.hom Rg ≫
        (Functor.leftUnitor _).hom).app N) ≫ adjg.counit.app N =
      c.inv.app (Rhg.obj N) ≫ adjhg.counit.app N := by
  have h1 := mateEquiv_counit adjhg adjg (TwoSquare.mk _ _ _ _ θ.hom) N
  have h2 := adjg.counit.naturality (i1.hom.app N)
  have h3 := i1.hom.naturality (adjhg.counit.app N)
  simp only [Functor.comp_map, Functor.id_map, Functor.id_obj, Functor.comp_obj] at h2 h3
  rw [Adjunction.exchangeRight_eq_mateEquiv]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Functor.map_comp, Category.assoc, Functor.id_obj, Functor.comp_obj]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [h2]
  erw [reassoc_of% h1]
  rw [h3, ← hθ, Category.assoc]

set_option hygiene false in
/-- The derived category `D(X_proét, Λ) = D(Mod_{Λ_X})` of module objects over `Λ_X`. -/
local notation "𝔻(" X ")" =>
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

section Models

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {B C P : Scheme.{u}} {g : B ⟶ C} {h : C ⟶ P} {hg : B ⟶ P}

/-- The base change map `Lh^* R(hg)_* ⟶ Rg_*` of the square `(𝟙, g, hg, h)`, for `g ≫ h = hg`:
`ProEtale.CondensedRing.baseChangeMap` followed by `L(𝟙)^* ≅ 𝟭`. -/
noncomputable def closedBaseChange (w : g ≫ h = hg) :
    R((hg)_*⟦Λ⟧) ⋙ L((h)^*⟦Λ⟧) ⟶ R((g)_*⟦Λ⟧) :=
  baseChangeMap Λ (⟨by rw [Category.id_comp, w]⟩ : CommSq (𝟙 B) g hg h) ≫
    Functor.whiskerRight (leftDerivedUpperStarId Λ B).hom R((g)_*⟦Λ⟧) ≫
    (Functor.leftUnitor _).hom

lemma closedBaseChange_eq (w : g ≫ h = hg) :
    closedBaseChange Λ w = Adjunction.exchangeRight (derivedUpperStarLowerStarAdjunction Λ hg)
      (derivedUpperStarLowerStarAdjunction Λ g)
      (pullbackSquareComparison Λ (⟨by rw [Category.id_comp, w]⟩ : CommSq (𝟙 B) g hg h)) ≫
        Functor.whiskerRight (leftDerivedUpperStarId Λ B).hom R((g)_*⟦Λ⟧) ≫
        (Functor.leftUnitor _).hom :=
  rfl

lemma pullbackSquareComparison_hom_app_comp_leftDerivedUpperStarId (w : g ≫ h = hg)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology P) Ab.{u + 1})
      (condensedRingObj Λ P))) :
    (pullbackSquareComparison Λ (⟨by rw [Category.id_comp, w]⟩ : CommSq (𝟙 B) g hg h)).hom.app K ≫
      (leftDerivedUpperStarId Λ B).hom.app (L((hg)^*⟦Λ⟧).obj K) =
        (leftDerivedUpperStarCompOfEq Λ w).inv.app K := by
  subst w
  simp only [pullbackSquareComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    eqToIso.hom, Category.assoc, leftDerivedUpperStarComp_id_left_app, eqToHom_refl,
    Category.comp_id, NatTrans.id_app]
  rfl

/-- The adjoint of `closedBaseChange` is `Lg^* Lh^* R(hg)_* ≅ L(hg)^* R(hg)_* ⟶ 𝟭`. -/
lemma map_closedBaseChange_app_comp_counit (w : g ≫ h = hg)
    (N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1})
      (condensedRingObj Λ B))) :
    L((g)^*⟦Λ⟧).map ((closedBaseChange Λ w).app N) ≫
        (derivedUpperStarLowerStarAdjunction Λ g).counit.app N =
      (leftDerivedUpperStarCompOfEq Λ w).inv.app (R((hg)_*⟦Λ⟧).obj N) ≫
        (derivedUpperStarLowerStarAdjunction Λ hg).counit.app N := by
  have := map_exchangeRight_app_comp_counit_aux (derivedUpperStarLowerStarAdjunction Λ g)
    (derivedUpperStarLowerStarAdjunction Λ hg) (leftDerivedUpperStarId Λ B)
    (pullbackSquareComparison Λ _) (leftDerivedUpperStarCompOfEq Λ w)
    (pullbackSquareComparison_hom_app_comp_leftDerivedUpperStarId Λ w) N
  rw [closedBaseChange_eq]
  exact this

/-- For `h` weakly étale and mono (e.g. an open immersion), the square `(𝟙, g, g ≫ h, h)` is
cartesian, so its base change map is invertible. -/
instance isIso_closedBaseChange (w : g ≫ h = hg) [Mono h] [WeaklyEtale h] :
    IsIso (closedBaseChange Λ w) := by
  have := isIso_baseChangeMap_of_weaklyEtale Λ
    (IsPullback.of_horiz_isIso_mono (⟨by rw [Category.id_comp, w]⟩ : CommSq (𝟙 B) g hg h))
  unfold closedBaseChange
  infer_instance

variable {Λ} in
/-- The morphism `h_! g_* ⟶ (hg)_*` adjoint to the inverse of the base change map
`Lh^* R(hg)_* ⟶ Rg_*`, for an adjunction `h_! ⊣ Lh^*`. (It is invertible on complexes supported on
the closed subset `B`, but this is not needed.) -/
noncomputable def closedExtension {Dh : 𝔻(C) ⥤ 𝔻(P)} (adj : Dh ⊣ L((h)^*⟦Λ⟧))
    (w : g ≫ h = hg) [Mono h] [WeaklyEtale h] : R((g)_*⟦Λ⟧) ⋙ Dh ⟶ R((hg)_*⟦Λ⟧) :=
  Functor.whiskerRight (inv (closedBaseChange Λ w)) Dh ≫ (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ adj.counit ≫ (Functor.rightUnitor _).hom

variable {Λ} in
lemma unit_comp_closedExtension_app {Dh : 𝔻(C) ⥤ 𝔻(P)} (adj : Dh ⊣ L((h)^*⟦Λ⟧))
    (w : g ≫ h = hg) [Mono h] [WeaklyEtale h] (N : 𝔻(B)) :
    adj.unit.app (R((g)_*⟦Λ⟧).obj N) ≫ L((h)^*⟦Λ⟧).map ((closedExtension adj w).app N) ≫
      (closedBaseChange Λ w).app N = 𝟙 _ := by
  have : adj.unit.app (R((g)_*⟦Λ⟧).obj N) ≫ L((h)^*⟦Λ⟧).map ((closedExtension adj w).app N) =
      (inv (closedBaseChange Λ w)).app N := by
    simp only [closedExtension, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
      Category.id_comp]
    erw [Category.comp_id]
    rw [← Adjunction.homEquiv_counit]
    exact (adj.homEquiv_unit _ _ _).symm.trans ((adj.homEquiv _ _).apply_symm_apply _)
  rw [reassoc_of% this]
  simp

end Models
section ModelExchange

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  {B B' C C' P P' Y Y' : Scheme.{u}} {MB : NearbyCyclesModel B B'} {MC : NearbyCyclesModel C C'}
  {MP : NearbyCyclesModel P P'} {MY : NearbyCyclesModel Y Y'}
  {g : B ⟶ C} {g' : B' ⟶ C'} {h : C ⟶ P} {h' : C' ⟶ P'} {hg : B ⟶ P} {hg' : B' ⟶ P'}
  {p : P ⟶ Y} {p' : P' ⟶ Y'} {phg : B ⟶ Y} {phg' : B' ⟶ Y'}

/-- The composition isomorphism `R(fg)_* ≅ Rf_* ⋙ Rg_*` of a factorization `f ≫ g = fg`: the
conjugate of `ProEtale.CondensedRing.leftDerivedUpperStarCompOfEq`. -/
noncomputable abbrev lowerStarCompOfEq {X₀ X₁ X₂ : Scheme.{u}} {f : X₀ ⟶ X₁} {g : X₁ ⟶ X₂}
    {fg : X₀ ⟶ X₂} (w : f ≫ g = fg) : R((fg)_*⟦Λ⟧) ≅ R((f)_*⟦Λ⟧) ⋙ R((g)_*⟦Λ⟧) :=
  conjugateIsoEquiv (derivedUpperStarLowerStarAdjunction Λ fg)
    ((derivedUpperStarLowerStarAdjunction Λ g).comp (derivedUpperStarLowerStarAdjunction Λ f))
    (leftDerivedUpperStarCompOfEq Λ w).symm

/-- **The compact-support exchange of a compactification on proper pieces** (step (B) of
Varshavsky's argument), on the ambient derived categories: let `φ_h` be a morphism of models over
an open immersion `h` with invertible pullback exchange and `ν_h` the adjoint of `α_h⁻¹` for
adjunctions `h_! ⊣ Lh^*`, `φ_p` a morphism of models over `p` and `χinv` a right inverse of its
pushforward exchange `χ_p`. Let `φ_g` be a morphism of models over `g` such that `h ∘ g` underlies
a morphism of models `φ_{hg}` (the composite) and `φ_{p(hg)}` the composite with `φ_p`. Then
`χ_p⁻¹ ∘ Rp'_*(ν_h)` at `g_* N`, read through `closedExtension : h_! g_* ⟶ (hg)_*` and
`R(p(hg))_* ≅ R(hg)_* ⋙ Rp_*`, is the pushforward exchange of `p ∘ (h ∘ g)` after
`Rp'_* h'_!(χ_g)`. -/
theorem NearbyCyclesModel.Hom.compactSupportExchange_comp_app (φg : MB.Hom MC g g')
    (φh : MC.Hom MP h h') (φhg : MB.Hom MP hg hg') (φp : MP.Hom MY p p')
    (φphg : MB.Hom MY phg phg') (w : g ≫ h = hg) (w' : g' ≫ h' = hg')
    (htot : φg.total ≫ φh.total = φhg.total) (hgen : φg.generic ≫ φh.generic = φhg.generic)
    (v : hg ≫ p = phg) (v' : hg' ≫ p' = phg') (htot₂ : φhg.total ≫ φp.total = φphg.total)
    (hgen₂ : φhg.generic ≫ φp.generic = φphg.generic)
    {Dh : 𝔻(C) ⥤ 𝔻(P)} {Dh' : 𝔻(C') ⥤ 𝔻(P')} (adj : Dh ⊣ L((h)^*⟦Λ⟧))
    (adj' : Dh' ⊣ L((h')^*⟦Λ⟧)) [IsIso (φh.pullbackExchange Λ)]
    [Mono h] [WeaklyEtale h] [Mono h'] [WeaklyEtale h'] (N : 𝔻(B))
    (χinv : (MP.nearbyCycles Λ ⋙ R((p')_*⟦Λ⟧)).obj (Dh.obj (R((g)_*⟦Λ⟧).obj N)) ⟶
      (R((p)_*⟦Λ⟧) ⋙ MY.nearbyCycles Λ).obj (Dh.obj (R((g)_*⟦Λ⟧).obj N)))
    (hχinv : χinv ≫ (φp.pushforwardExchange Λ).app (Dh.obj (R((g)_*⟦Λ⟧).obj N)) = 𝟙 _) :
    R((p')_*⟦Λ⟧).map ((lowerShriekExchangeOfInv adj adj' (φh.pullbackExchange Λ)).app
        (R((g)_*⟦Λ⟧).obj N)) ≫ χinv ≫
        (MY.nearbyCycles Λ).map (R((p)_*⟦Λ⟧).map ((closedExtension adj w).app N) ≫
          (lowerStarCompOfEq (Λ := Λ) v).inv.app N) ≫ (φphg.pushforwardExchange Λ).app N =
      R((p')_*⟦Λ⟧).map (Dh'.map ((φg.pushforwardExchange Λ).app N) ≫
        (closedExtension adj' w').app ((MB.nearbyCycles Λ).obj N)) ≫
        (lowerStarCompOfEq (Λ := Λ) v').inv.app ((MB.nearbyCycles Λ).obj N) :=
  compactSupportExchange_comp_aux (derivedUpperStarLowerStarAdjunction Λ g)
    (derivedUpperStarLowerStarAdjunction Λ hg) (derivedUpperStarLowerStarAdjunction Λ g')
    (derivedUpperStarLowerStarAdjunction Λ hg') (leftDerivedUpperStarCompOfEq Λ w)
    (leftDerivedUpperStarCompOfEq Λ w') (φg.pullbackExchange Λ) (φh.pullbackExchange Λ)
    (φhg.pullbackExchange Λ) (φg.pullbackExchange_comp_app_of_eq Λ φh φhg w w' htot hgen)
    (φg.pushforwardExchange Λ) rfl (φhg.pushforwardExchange Λ) rfl (closedBaseChange Λ w)
    (map_closedBaseChange_app_comp_counit Λ w) (closedBaseChange Λ w')
    (map_closedBaseChange_app_comp_counit Λ w') adj adj' (closedExtension adj w)
    (unit_comp_closedExtension_app adj w) (closedExtension adj' w')
    (unit_comp_closedExtension_app adj' w')
    (φp.pushforwardExchange Λ) (φphg.pushforwardExchange Λ) (lowerStarCompOfEq v)
    (lowerStarCompOfEq v') (φhg.pushforwardExchange_comp_app_of_eq Λ φp φphg v v' htot₂ hgen₂)
    N χinv hχinv

end ModelExchange

end AlgebraicGeometry.ProEtale.CondensedRing
