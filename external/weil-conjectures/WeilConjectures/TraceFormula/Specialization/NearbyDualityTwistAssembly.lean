/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category

/-!

# The twist equation of the generic slice from the composition law

The algebra behind deducing the twist equation of the generic slice
(`NearbyCyclesModel.IsTraitModelOfGenericBase.TwistEquation`)
`p^* θ_M ≫ v = α ≫ Ψ_{M''}(u) ≫ κ ≫ θ_{M''} ▷ T`
for a model `M` with a proper coordinate `b : M ⟶ ℙ¹_S` from the same equation for `ℙ¹_S`, in
abstract categories.

* `NearbyCyclesModel.exists_twist_of_isIso`: the twist equation is formal when `θ`, the slice
  exchange `α` at `ω` and `θ''` are invertible, given some identification `u`: take
  `v = (p^* θ)⁻¹ ≫ α ≫ Ψ''(u) ≫ κ ≫ θ'' ▷ T`. This applies to the smooth model `ℙ¹_S` and its
  slice (`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.isIso_θ_of_smooth`), the slice
  exchange of a smooth model being invertible by smooth base change.
* `NearbyCyclesModel.exists_twist_of_composition_law`: the twist equation passes along the
  composition laws `Ψ_M(ρ) ≫ θ_M = β_b(ω_ℙ) ≫ b_s^!(θ_ℙ) ≫ ρ'`
  (`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.θ_comp_law`) for `M ⟶ ℙ¹_S` and for its
  slice `M'' ⟶ ℙ''`, given the slicing square of the exceptional exchanges
  (`NearbyCyclesModel.Hom.exceptionalExchange_slice_app`) with invertible base change maps `γ`
  of the exceptional inverse images at the dualizing complexes, and the compatibility of the
  exceptional exchange `β_{b''}` with the twist isomorphisms `κ` and the identifications
  `b''^!(- ⊗ T) ≅ b''^!(-) ⊗ T`. The identifications are
  `u = C(ρ⁻¹) ≪≫ γ_b ≪≫ J₂(u_ℙ) ≪≫ n ≪≫ ρ₂ ▷ T` and
  `v = P(ρ'⁻¹) ≪≫ γ_s ≪≫ J₂'(v_ℙ) ≪≫ m ≪≫ ρ₂' ▷ T`.
* `NearbyCyclesModel.exists_twist_of_composition_law_of_isIso`: both combined.

-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

namespace NearbyCyclesModel

/-- **The twist equation for invertible dualizing maps**: if `θ` and `α.app ω` are isomorphisms,
the equation `P(θ) ≫ v = α ≫ Ψ(u) ≫ κ` holds for any identification `u` and isomorphism `κ`, with
`v = P(θ)⁻¹ ≫ α ≫ Ψ(u) ≫ κ`. -/
lemma exists_twist_of_isIso {DX DS D₂ Ds : Type*} [Category DX] [Category DS] [Category D₂]
    [Category Ds] [MonoidalCategory Ds] {ΨM : DX ⥤ DS} {Ψ : D₂ ⥤ Ds} {C : DX ⥤ D₂}
    {P : DS ⥤ Ds} {ω : DX} {ω' : DS} {W : D₂} {ωs Ts : Ds}
    (θ : ΨM.obj ω ⟶ ω') [IsIso θ] (α : ΨM ⋙ P ⟶ C ⋙ Ψ) [IsIso (α.app ω)]
    (u : C.obj ω ≅ W) (κ : Ψ.obj W ≅ ωs ⊗ Ts) :
    ∃ (u : C.obj ω ≅ W) (v : P.obj ω' ≅ ωs ⊗ Ts),
      P.map θ ≫ v.hom = α.app ω ≫ Ψ.map u.hom ≫ κ.hom := by
  refine ⟨u, (P.mapIso (asIso θ)).symm ≪≫ asIso (α.app ω) ≪≫ Ψ.mapIso u ≪≫ κ, ?_⟩
  simp

/-- **The twist equation for invertible dualizing maps**, in the shape of
`NearbyCyclesModel.IsTraitModelOfGenericBase.TwistEquation`: if `θ`, `α.app ω` and
`θ''` are isomorphisms and `κ` is an isomorphism, then for any `u : C(ω) ≅ ω₂ ⊗ T₂` there is `v`
with `P(θ) ≫ v = α ≫ Ψ(u) ≫ κ ≫ θ'' ▷ T`. -/
lemma exists_twist_of_isIso' {DX DS D₂ Ds : Type*} [Category DX] [Category DS] [Category D₂]
    [Category Ds] [MonoidalCategory D₂] [MonoidalCategory Ds] {ΨM : DX ⥤ DS} {Ψ : D₂ ⥤ Ds}
    {C : DX ⥤ D₂} {P : DS ⥤ Ds} {ω : DX} {ω' : DS} {ω₂ T₂ : D₂} {ωs Ts : Ds}
    (θ : ΨM.obj ω ⟶ ω') [IsIso θ] (α : ΨM ⋙ P ⟶ C ⋙ Ψ) [IsIso (α.app ω)]
    (θ'' : Ψ.obj ω₂ ⟶ ωs) [IsIso θ''] (κ : Ψ.obj (ω₂ ⊗ T₂) ≅ Ψ.obj ω₂ ⊗ Ts)
    (u : C.obj ω ≅ ω₂ ⊗ T₂) :
    ∃ (u : C.obj ω ≅ ω₂ ⊗ T₂) (v : P.obj ω' ≅ ωs ⊗ Ts),
      P.map θ ≫ v.hom = α.app ω ≫ Ψ.map u.hom ≫ κ.hom ≫ θ'' ▷ Ts := by
  obtain ⟨u, v, h⟩ := exists_twist_of_isIso θ α u (κ ≪≫ whiskerRightIso (asIso θ'') Ts)
  exact ⟨u, v, h⟩

/-- **The twist equation and the composition law**, abstractly (the algebra behind deducing
`NearbyCyclesModel.IsTraitModelOfGenericBase.TwistEquation` for a model `M` with a
proper coordinate `b : M ⟶ ℙ¹_S` from the same equation for `ℙ¹_S`).

Notation: `ΨM`, `ΨP` are the nearby cycles of `M` and `ℙ¹_S`, `Ψ`, `ΨP''` those of their slices;
`J = Rb₁^!`, `J' = Rb₂^!`, `J₂ = Rb₁''^!`, `J₂' = Rb₂''^!` the exceptional inverse images;
`C`, `CP` the pullbacks along the slice base maps and `P`, `PP` along the slice special maps;
`β : J ⋙ ΨM ⟶ ΨP ⋙ J'` and `β'' : J₂ ⋙ Ψ ⟶ ΨP'' ⋙ J₂'` the exceptional exchanges;
`α`, `αP` the slice exchanges; `γb : J ⋙ C ⟶ CP ⋙ J₂`, `γs : J' ⋙ P ⟶ PP ⋙ J₂'` the base change
maps of the exceptional inverse images.

Hypotheses: the composition laws `hθ`, `hθ''`
(`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.θ_comp_law`), the slicing square `hsq`
(`NearbyCyclesModel.Hom.exceptionalExchange_slice_app`), invertibility of `γb`, `γs` at the
dualizing complexes, the compatibility `hκP` of `β''` with the twist isomorphisms and the
identifications `m : J₂'(- ⊗ T) ≅ J₂'(-) ⊗ T`, `n : J₂(ω₂P ⊗ T) ≅ J₂(ω₂P) ⊗ T`, and the twist
equation `H` for `ℙ¹_S`. Conclusion: the twist equation for `M`, with
`u = C(ρ⁻¹) ≪≫ γb ≪≫ J₂(uP) ≪≫ n ≪≫ ρ₂ ▷ T₂` and `v = P(ρ'⁻¹) ≪≫ γs ≪≫ J₂'(vP) ≪≫ m ≪≫ ρ₂' ▷ Ts`.
-/
lemma exists_twist_of_composition_law {DX DXP DS DSP D₂ D₂P Ds DsP : Type*}
    [Category DX] [Category DXP] [Category DS] [Category DSP] [Category D₂] [Category D₂P]
    [Category Ds] [Category DsP] [MonoidalCategory D₂] [MonoidalCategory D₂P]
    [MonoidalCategory Ds] [MonoidalCategory DsP]
    {ΨM : DX ⥤ DS} {ΨP : DXP ⥤ DSP} {Ψ : D₂ ⥤ Ds} {ΨP'' : D₂P ⥤ DsP}
    {J : DXP ⥤ DX} {J' : DSP ⥤ DS} {J₂ : D₂P ⥤ D₂} {J₂' : DsP ⥤ Ds}
    {C : DX ⥤ D₂} {CP : DXP ⥤ D₂P} {P : DS ⥤ Ds} {PP : DSP ⥤ DsP}
    {ωP : DXP} {ω : DX} {ω'P : DSP} {ω' : DS} {ω₂P : D₂P} {ω₂ : D₂} {ωsP : DsP} {ωs : Ds}
    {T₂P : D₂P} {T₂ : D₂} {TsP : DsP} {Ts : Ds}
    (θP : ΨP.obj ωP ⟶ ω'P) (θ : ΨM.obj ω ⟶ ω') (θP'' : ΨP''.obj ω₂P ⟶ ωsP)
    (θ'' : Ψ.obj ω₂ ⟶ ωs)
    (β : J ⋙ ΨM ⟶ ΨP ⋙ J') (ρ : J.obj ωP ≅ ω) (ρ' : J'.obj ω'P ≅ ω')
    (hθ : ΨM.map ρ.hom ≫ θ = β.app ωP ≫ J'.map θP ≫ ρ'.hom)
    (β'' : J₂ ⋙ Ψ ⟶ ΨP'' ⋙ J₂') (ρ₂ : J₂.obj ω₂P ≅ ω₂) (ρ₂' : J₂'.obj ωsP ≅ ωs)
    (hθ'' : Ψ.map ρ₂.hom ≫ θ'' = β''.app ω₂P ≫ J₂'.map θP'' ≫ ρ₂'.hom)
    (α : ΨM ⋙ P ⟶ C ⋙ Ψ) (αP : ΨP ⋙ PP ⟶ CP ⋙ ΨP'')
    (γb : J ⋙ C ⟶ CP ⋙ J₂) [IsIso (γb.app ωP)]
    (γs : J' ⋙ P ⟶ PP ⋙ J₂') [IsIso (γs.app ω'P)]
    (hsq : P.map (β.app ωP) ≫ γs.app (ΨP.obj ωP) ≫ J₂'.map (αP.app ωP) =
      α.app (J.obj ωP) ≫ Ψ.map (γb.app ωP) ≫ β''.app (CP.obj ωP))
    (m : ∀ Z : DsP, J₂'.obj (Z ⊗ TsP) ≅ J₂'.obj Z ⊗ Ts)
    (hm : ∀ {Z Z' : DsP} (f : Z ⟶ Z'),
      J₂'.map (f ▷ TsP) ≫ (m Z').hom = (m Z).hom ≫ J₂'.map f ▷ Ts)
    (n : J₂.obj (ω₂P ⊗ T₂P) ≅ J₂.obj ω₂P ⊗ T₂)
    (κP : ΨP''.obj (ω₂P ⊗ T₂P) ≅ ΨP''.obj ω₂P ⊗ TsP)
    (κ : ∀ A : D₂, Ψ.obj (A ⊗ T₂) ≅ Ψ.obj A ⊗ Ts)
    (hκ : ∀ {A B : D₂} (f : A ⟶ B), Ψ.map (f ▷ T₂) ≫ (κ B).hom = (κ A).hom ≫ Ψ.map f ▷ Ts)
    (hκP : β''.app (ω₂P ⊗ T₂P) ≫ J₂'.map κP.hom ≫ (m _).hom =
      Ψ.map n.hom ≫ (κ (J₂.obj ω₂P)).hom ≫ β''.app ω₂P ▷ Ts)
    (H : ∃ (uP : CP.obj ωP ≅ ω₂P ⊗ T₂P) (vP : PP.obj ω'P ≅ ωsP ⊗ TsP),
      PP.map θP ≫ vP.hom = αP.app ωP ≫ ΨP''.map uP.hom ≫ κP.hom ≫ θP'' ▷ TsP) :
    ∃ (u : C.obj ω ≅ ω₂ ⊗ T₂) (v : P.obj ω' ≅ ωs ⊗ Ts),
      P.map θ ≫ v.hom = α.app ω ≫ Ψ.map u.hom ≫ (κ ω₂).hom ≫ θ'' ▷ Ts := by
  obtain ⟨uP, vP, huv⟩ := H
  refine ⟨C.mapIso ρ.symm ≪≫ asIso (γb.app ωP) ≪≫ J₂.mapIso uP ≪≫ n ≪≫ whiskerRightIso ρ₂ T₂,
    P.mapIso ρ'.symm ≪≫ asIso (γs.app ω'P) ≪≫ J₂'.mapIso vP ≪≫ m ωsP ≪≫
      whiskerRightIso ρ₂' Ts, ?_⟩
  have hθ' : θ = ΨM.map ρ.inv ≫ β.app ωP ≫ J'.map θP ≫ ρ'.hom := by
    rw [← hθ]; simp
  -- naturality of `γs` at `θP`
  have h₁ : P.map (J'.map θP) ≫ γs.app ω'P = γs.app (ΨP.obj ωP) ≫ J₂'.map (PP.map θP) :=
    γs.naturality θP
  -- naturality of `α` at `ρ⁻¹`
  have h₂ : P.map (ΨM.map ρ.inv) ≫ α.app (J.obj ωP) = α.app ω ≫ Ψ.map (C.map ρ.inv) :=
    α.naturality ρ.inv
  -- naturality of `β''` at `uP`
  have h₃ : Ψ.map (J₂.map uP.hom) ≫ β''.app (ω₂P ⊗ T₂P) =
      β''.app (CP.obj ωP) ≫ J₂'.map (ΨP''.map uP.hom) := β''.naturality uP.hom
  -- the twist equation for `ℙ¹_S`, transported by `J₂'`
  have h₄ : J₂'.map (PP.map θP) ≫ J₂'.map vP.hom ≫ (m ωsP).hom ≫ ρ₂'.hom ▷ Ts =
      J₂'.map (αP.app ωP) ≫ J₂'.map (ΨP''.map uP.hom) ≫ J₂'.map κP.hom ≫ (m _).hom ≫
        (J₂'.map θP'' ≫ ρ₂'.hom) ▷ Ts := by
    rw [← J₂'.map_comp_assoc, huv]
    simp only [Functor.map_comp, Category.assoc, reassoc_of% (hm θP''), comp_whiskerRight]
  -- the twist and the composition law of the slice
  have h₅ : β''.app (ω₂P ⊗ T₂P) ≫ J₂'.map κP.hom ≫ (m _).hom ≫
      (J₂'.map θP'' ≫ ρ₂'.hom) ▷ Ts =
      Ψ.map n.hom ≫ Ψ.map (ρ₂.hom ▷ T₂) ≫ (κ ω₂).hom ≫ θ'' ▷ Ts := by
    rw [reassoc_of% hκP, reassoc_of% (hκ ρ₂.hom), ← comp_whiskerRight, ← comp_whiskerRight,
      hθ'']
  have h₆ : P.map ρ'.hom ≫ P.map ρ'.inv = 𝟙 _ := by
    rw [← P.map_comp, Iso.hom_inv_id, P.map_id]
  simp only [hθ', Functor.map_comp, Category.assoc, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_hom, whiskerRightIso_hom, reassoc_of% h₆, reassoc_of% h₁, h₄]
  rw [reassoc_of% hsq, reassoc_of% h₂, ← reassoc_of% h₃, h₅]

/-- **The twist equation from the composition law and the smooth model**: the hypotheses of
`NearbyCyclesModel.exists_twist_of_composition_law`, with the twist equation for `ℙ¹_S` replaced
by the invertibility of `θP` (`ℙ¹_S` is smooth and proper), of the slice exchange `αP` at `ωP`
(smooth base change) and of `θP''` (the slice of `ℙ¹_S` is smooth and proper), and by some
identification `uP : CP(ωP) ≅ ω₂P ⊗ T₂P`
(`NearbyCyclesModel.exists_twist_of_isIso'`). -/
lemma exists_twist_of_composition_law_of_isIso {DX DXP DS DSP D₂ D₂P Ds DsP : Type*}
    [Category DX] [Category DXP] [Category DS] [Category DSP] [Category D₂] [Category D₂P]
    [Category Ds] [Category DsP] [MonoidalCategory D₂] [MonoidalCategory D₂P]
    [MonoidalCategory Ds] [MonoidalCategory DsP]
    {ΨM : DX ⥤ DS} {ΨP : DXP ⥤ DSP} {Ψ : D₂ ⥤ Ds} {ΨP'' : D₂P ⥤ DsP}
    {J : DXP ⥤ DX} {J' : DSP ⥤ DS} {J₂ : D₂P ⥤ D₂} {J₂' : DsP ⥤ Ds}
    {C : DX ⥤ D₂} {CP : DXP ⥤ D₂P} {P : DS ⥤ Ds} {PP : DSP ⥤ DsP}
    {ωP : DXP} {ω : DX} {ω'P : DSP} {ω' : DS} {ω₂P : D₂P} {ω₂ : D₂} {ωsP : DsP} {ωs : Ds}
    {T₂P : D₂P} {T₂ : D₂} {TsP : DsP} {Ts : Ds}
    (θP : ΨP.obj ωP ⟶ ω'P) [IsIso θP] (θ : ΨM.obj ω ⟶ ω') (θP'' : ΨP''.obj ω₂P ⟶ ωsP)
    [IsIso θP''] (θ'' : Ψ.obj ω₂ ⟶ ωs)
    (β : J ⋙ ΨM ⟶ ΨP ⋙ J') (ρ : J.obj ωP ≅ ω) (ρ' : J'.obj ω'P ≅ ω')
    (hθ : ΨM.map ρ.hom ≫ θ = β.app ωP ≫ J'.map θP ≫ ρ'.hom)
    (β'' : J₂ ⋙ Ψ ⟶ ΨP'' ⋙ J₂') (ρ₂ : J₂.obj ω₂P ≅ ω₂) (ρ₂' : J₂'.obj ωsP ≅ ωs)
    (hθ'' : Ψ.map ρ₂.hom ≫ θ'' = β''.app ω₂P ≫ J₂'.map θP'' ≫ ρ₂'.hom)
    (α : ΨM ⋙ P ⟶ C ⋙ Ψ) (αP : ΨP ⋙ PP ⟶ CP ⋙ ΨP'') [IsIso (αP.app ωP)]
    (γb : J ⋙ C ⟶ CP ⋙ J₂) [IsIso (γb.app ωP)]
    (γs : J' ⋙ P ⟶ PP ⋙ J₂') [IsIso (γs.app ω'P)]
    (hsq : P.map (β.app ωP) ≫ γs.app (ΨP.obj ωP) ≫ J₂'.map (αP.app ωP) =
      α.app (J.obj ωP) ≫ Ψ.map (γb.app ωP) ≫ β''.app (CP.obj ωP))
    (m : ∀ Z : DsP, J₂'.obj (Z ⊗ TsP) ≅ J₂'.obj Z ⊗ Ts)
    (hm : ∀ {Z Z' : DsP} (f : Z ⟶ Z'),
      J₂'.map (f ▷ TsP) ≫ (m Z').hom = (m Z).hom ≫ J₂'.map f ▷ Ts)
    (n : J₂.obj (ω₂P ⊗ T₂P) ≅ J₂.obj ω₂P ⊗ T₂)
    (κP : ΨP''.obj (ω₂P ⊗ T₂P) ≅ ΨP''.obj ω₂P ⊗ TsP)
    (κ : ∀ A : D₂, Ψ.obj (A ⊗ T₂) ≅ Ψ.obj A ⊗ Ts)
    (hκ : ∀ {A B : D₂} (f : A ⟶ B), Ψ.map (f ▷ T₂) ≫ (κ B).hom = (κ A).hom ≫ Ψ.map f ▷ Ts)
    (hκP : β''.app (ω₂P ⊗ T₂P) ≫ J₂'.map κP.hom ≫ (m _).hom =
      Ψ.map n.hom ≫ (κ (J₂.obj ω₂P)).hom ≫ β''.app ω₂P ▷ Ts)
    (uP : CP.obj ωP ≅ ω₂P ⊗ T₂P) :
    ∃ (u : C.obj ω ≅ ω₂ ⊗ T₂) (v : P.obj ω' ≅ ωs ⊗ Ts),
      P.map θ ≫ v.hom = α.app ω ≫ Ψ.map u.hom ≫ (κ ω₂).hom ≫ θ'' ▷ Ts :=
  exists_twist_of_composition_law θP θ θP'' θ'' β ρ ρ' hθ β'' ρ₂ ρ₂' hθ'' α αP γb γs hsq m hm n
    κP κ hκ hκP (exists_twist_of_isIso' θP αP θP'' κP uP)

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
