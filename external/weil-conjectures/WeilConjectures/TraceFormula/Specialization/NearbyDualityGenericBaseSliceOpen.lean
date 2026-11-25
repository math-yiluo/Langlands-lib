/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceRebaseTwist
import all WeilConjectures.TraceFormula.Specialization.NearbyCyclesZeroTwist

/-!

# The twist equation of the generic slice and open sub-models

The twist equation of the generic slice
(`NearbyCyclesModel.IsTraitModelOfGenericBase.TwistEquation`) passes from a trait
model `M_c` over a generic base to its open sub-models `M`, for a coordinate `b = φ ≫ b_c` of `M`
restricted from `M_c`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_iso_map_θ_eq_twist_of_openSubmodel`). Every
trait model over a generic base is such an open sub-model of a proper one with full generic fibre
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_isProper_openSubmodel`), for which the
equation reduces to the re-based model
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_iso_map_θ_eq_twist_of_rebase`).

* `NearbyCyclesModel.exists_twist_of_openSubmodel`: the algebra of the reduction, in abstract
  categories: the dualizing maps of `M` and of its slice are restrictions of those of `M_c` and
  of its slice (open restriction), the slice exchanges are compatible with the restrictions, and
  so are the twist isomorphisms `κ`.
* `NearbyCyclesModel.Hom.genericSliceOpenHom`: the generic slice of `M` is the open sub-model of
  that of `M_c` over the open immersions `X₂ ⟶ X₂,c` and `𝒳''_s ⟶ 𝒳''_{c,s}`; the maps of bases
  and special fibres of the slices are compatible with the restrictions
  (`NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceBaseMap_comp_openSubmodel`, through
  the epimorphism `ε` of the slice model, and
  `NearbyCyclesModel.sliceSpecialMap_comp_openSubmodel`).
* `NearbyCyclesModel.boundedConstructiblePullbackExchange_square`: the square law of the pullback
  exchanges (`NearbyCyclesModel.Hom.pullbackExchange_square`) on bounded constructible complexes.
* `NearbyCyclesModel.Hom.liftExchange_zeroTwistIso`: the twist isomorphisms
  `κ : Ψ (A ⊗ ℚ̄_ℓ(0)[n]) ≅ Ψ A ⊗ ℚ̄_ℓ(0)[n]` are compatible with the pullback exchange of any
  morphism of models: the exchange is monoidal, and compatible with the specialization maps of
  `ℚ̄_ℓ(0)[n]` (`NearbyCyclesModel.Hom.pullbackExchange_ambientZeroTwistSpecializationMap`, from
  the unit law of the exchange in degree `0` and the commutation with the shifts).

## Implementation notes

As in `TraceFormula.Specialization.NearbyDualityGenericBaseSliceRebaseTwist`, the compatibilities
are proved for arbitrary models and morphisms and only instantiated at the generic slices, and
statements whose two sides spell objects differently are closed by `transport_exact`. The pullback
comparison of a square is wrapped in the irreducible
`NearbyCyclesModel.pullbackSquareComparison'`: otherwise the elaborator and the kernel unfold it
when comparing the components of its restriction to bounded constructible complexes with those of
the ambient one.

-/

@[expose] public section

universe u

set_option linter.unusedSectionVars false

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

section Abstract

/-- **The twist equation and open sub-models**, abstractly (the algebra behind
`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_iso_map_θ_eq_twist_of_openSubmodel`): if
`θ` and `θ''` are the restrictions of `θ_c` and `θ_c''` along invertible exchanges `β`, `β''`
(open restriction), the slice exchanges `α`, `α_c` are compatible with the restrictions
(`hsq`), and so are the twist isomorphisms `κ`, `κ_c` (`hκc`), then the twist equation for
`θ_c` implies it for `θ`, with `u = C(ρ⁻¹) ≪≫ e⁻¹ ≪≫ J₂(u_c) ≪≫ n ≪≫ ρ₂ ▷ T` and
`v = P(ρ'⁻¹) ≪≫ e'⁻¹ ≪≫ J₂'(v_c) ≪≫ m ≪≫ ρ₂' ▷ T`. -/
lemma exists_twist_of_openSubmodel {DXc DX DSc DS D₂c D₂ Dsc Ds : Type*} [Category DXc]
    [Category DX] [Category DSc] [Category DS] [Category D₂c] [Category D₂] [Category Dsc]
    [Category Ds] [MonoidalCategory D₂c] [MonoidalCategory D₂] [MonoidalCategory Dsc]
    [MonoidalCategory Ds]
    {ΨMc : DXc ⥤ DSc} {ΨM : DX ⥤ DS} {Ψc : D₂c ⥤ Dsc} {Ψ : D₂ ⥤ Ds}
    {J : DXc ⥤ DX} {J' : DSc ⥤ DS} {J₂ : D₂c ⥤ D₂} {J₂' : Dsc ⥤ Ds}
    {C : DX ⥤ D₂} {Cc : DXc ⥤ D₂c} {P : DS ⥤ Ds} {Pc : DSc ⥤ Dsc}
    {ωc : DXc} {ω : DX} {ωc' : DSc} {ω' : DS} {ω₂c : D₂c} {ω₂ : D₂} {ωsc : Dsc} {ωs : Ds}
    {T₂c : D₂c} {T₂ : D₂} {Tsc : Dsc} {Ts : Ds}
    (θc : ΨMc.obj ωc ⟶ ωc') (θ : ΨM.obj ω ⟶ ω') (θc'' : Ψc.obj ω₂c ⟶ ωsc)
    (θ'' : Ψ.obj ω₂ ⟶ ωs)
    (β : ΨMc ⋙ J' ⟶ J ⋙ ΨM) [IsIso (β.app ωc)] (ρ : J.obj ωc ≅ ω) (ρ' : J'.obj ωc' ≅ ω')
    (hres : J'.map θc ≫ ρ'.hom = β.app ωc ≫ ΨM.map ρ.hom ≫ θ)
    (β'' : Ψc ⋙ J₂' ⟶ J₂ ⋙ Ψ) (ρ₂ : J₂.obj ω₂c ≅ ω₂) (ρ₂' : J₂'.obj ωsc ≅ ωs)
    (hres₂ : J₂'.map θc'' ≫ ρ₂'.hom = β''.app ω₂c ≫ Ψ.map ρ₂.hom ≫ θ'')
    (α : ΨM ⋙ P ⟶ C ⋙ Ψ) (αc : ΨMc ⋙ Pc ⟶ Cc ⋙ Ψc)
    (e'₁ : J₂'.obj (Pc.obj (ΨMc.obj ωc)) ≅ P.obj (J'.obj (ΨMc.obj ωc)))
    (e'₂ : J₂'.obj (Pc.obj ωc') ≅ P.obj (J'.obj ωc'))
    (he' : J₂'.map (Pc.map θc) ≫ e'₂.hom = e'₁.hom ≫ P.map (J'.map θc))
    (e : J₂.obj (Cc.obj ωc) ≅ C.obj (J.obj ωc))
    (hsq : e'₁.hom ≫ P.map (β.app ωc) ≫ α.app (J.obj ωc) =
      J₂'.map (αc.app ωc) ≫ β''.app (Cc.obj ωc) ≫ Ψ.map e.hom)
    (m : ∀ Z : Dsc, J₂'.obj (Z ⊗ Tsc) ≅ J₂'.obj Z ⊗ Ts)
    (hm : ∀ {Z Z' : Dsc} (f : Z ⟶ Z'), J₂'.map (f ▷ Tsc) ≫ (m Z').hom = (m Z).hom ≫ J₂'.map f ▷ Ts)
    (n : J₂.obj (ω₂c ⊗ T₂c) ≅ J₂.obj ω₂c ⊗ T₂)
    (κc : Ψc.obj (ω₂c ⊗ T₂c) ≅ Ψc.obj ω₂c ⊗ Tsc) (κ : ∀ A : D₂, Ψ.obj (A ⊗ T₂) ≅ Ψ.obj A ⊗ Ts)
    (hκ : ∀ {A B : D₂} (f : A ⟶ B), Ψ.map (f ▷ T₂) ≫ (κ B).hom = (κ A).hom ≫ Ψ.map f ▷ Ts)
    (hκc : J₂'.map κc.hom ≫ (m _).hom ≫ β''.app ω₂c ▷ Ts =
      β''.app (ω₂c ⊗ T₂c) ≫ Ψ.map n.hom ≫ (κ (J₂.obj ω₂c)).hom)
    (H : ∃ (uc : Cc.obj ωc ≅ ω₂c ⊗ T₂c) (vc : Pc.obj ωc' ≅ ωsc ⊗ Tsc),
      Pc.map θc ≫ vc.hom = αc.app ωc ≫ Ψc.map uc.hom ≫ κc.hom ≫ θc'' ▷ Tsc) :
    ∃ (u : C.obj ω ≅ ω₂ ⊗ T₂) (v : P.obj ω' ≅ ωs ⊗ Ts),
      P.map θ ≫ v.hom = α.app ω ≫ Ψ.map u.hom ≫ (κ ω₂).hom ≫ θ'' ▷ Ts := by
  obtain ⟨uc, vc, huv⟩ := H
  refine ⟨C.mapIso ρ.symm ≪≫ e.symm ≪≫ J₂.mapIso uc ≪≫ n ≪≫ whiskerRightIso ρ₂ T₂,
    P.mapIso ρ'.symm ≪≫ e'₂.symm ≪≫ J₂'.mapIso vc ≪≫ m ωsc ≪≫
      whiskerRightIso ρ₂' Ts, ?_⟩
  have hθ : θ = ΨM.map ρ.inv ≫ inv (β.app ωc) ≫ J'.map θc ≫ ρ'.hom := by
    rw [hres]; simp
  have h₁ : P.map (J'.map θc) ≫ e'₂.inv = e'₁.inv ≫ J₂'.map (Pc.map θc) := by
    rw [← cancel_epi e'₁.hom, ← reassoc_of% he']
    simp
  have h₂ : J₂'.map (θc'' ▷ Tsc) ≫ (m ωsc).hom ≫ ρ₂'.hom ▷ Ts =
      (m _).hom ≫ (β''.app ω₂c ≫ Ψ.map ρ₂.hom ≫ θ'') ▷ Ts := by
    rw [reassoc_of% (hm θc''), ← comp_whiskerRight, hres₂]
  have h₃ : J₂'.map (αc.app ωc) ≫ β''.app (Cc.obj ωc) =
      e'₁.hom ≫ P.map (β.app ωc) ≫ α.app (J.obj ωc) ≫ Ψ.map e.inv := by
    rw [reassoc_of% hsq]; simp
  have h₄ : J₂'.map (Ψc.map uc.hom) ≫ β''.app (ω₂c ⊗ T₂c) =
      β''.app (Cc.obj ωc) ≫ Ψ.map (J₂.map uc.hom) := β''.naturality uc.hom
  have h₅ : P.map (ΨM.map ρ.inv) ≫ α.app (J.obj ωc) = α.app ω ≫ Ψ.map (C.map ρ.inv) :=
    α.naturality ρ.inv
  have h₆ := hκ ρ₂.hom
  have h₀ : P.map ρ'.hom ≫ P.map ρ'.inv = 𝟙 _ := by rw [← P.map_comp, Iso.hom_inv_id, P.map_id]
  have h₉ : P.map (inv (β.app ωc)) ≫ P.map (β.app ωc) = 𝟙 _ := by
    rw [← P.map_comp, IsIso.inv_hom_id, P.map_id]
  have h₇ : J₂'.map (Pc.map θc) ≫ J₂'.map vc.hom ≫ (m ωsc).hom ≫ ρ₂'.hom ▷ Ts =
      J₂'.map (αc.app ωc) ≫ J₂'.map (Ψc.map uc.hom) ≫ J₂'.map κc.hom ≫ (m _).hom ≫
        (β''.app ω₂c ≫ Ψ.map ρ₂.hom ≫ θ'') ▷ Ts := by
    rw [← J₂'.map_comp_assoc, huv]
    simp only [Functor.map_comp, Category.assoc, h₂]
  have h₈ : J₂'.map κc.hom ≫ (m _).hom ≫ (β''.app ω₂c ≫ Ψ.map ρ₂.hom ≫ θ'') ▷ Ts =
      β''.app (ω₂c ⊗ T₂c) ≫ Ψ.map n.hom ≫ Ψ.map (ρ₂.hom ▷ T₂) ≫ (κ ω₂).hom ≫ θ'' ▷ Ts := by
    rw [comp_whiskerRight, reassoc_of% hκc, reassoc_of% h₆, comp_whiskerRight]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    whiskerRightIso_hom, Functor.map_comp, Category.assoc]
  rw [hθ]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% h₀, reassoc_of% h₁, h₇, h₈, reassoc_of% h₄, reassoc_of% h₃,
    Iso.inv_hom_id_assoc, reassoc_of% h₉,
    reassoc_of% h₅]

/-- The compatibility of an exchange `β : Ψ_M ⋙ Lf' ⟶ Lf ⋙ Ψ_N` commuting with the shifts with
specialization maps in degree `n`, from degree `0`: if `σ_N = τ'⁻¹ ≫ Lf'(σ_M) ≫ β ≫ Ψ_N(τ)` in
degree `0` and the specialization maps in degree `n` are the shifts of those in degree `0`, the
same holds in degree `n` for the shifted comparisons `τ`, `τ'`. -/
lemma shift_specialization_exchange {C D C' D' : Type*} [Category C] [Category D] [Category C']
    [Category D'] [HasShift C ℤ] [HasShift D ℤ] [HasShift C' ℤ] [HasShift D' ℤ] {ΨM : C ⥤ D}
    {ΨN : C' ⥤ D'} {Lf : C ⥤ C'} {Lf' : D ⥤ D'} [ΨM.CommShift ℤ] [ΨN.CommShift ℤ]
    [Lf.CommShift ℤ] [Lf'.CommShift ℤ] (β : ΨM ⋙ Lf' ⟶ Lf ⋙ ΨN) [NatTrans.CommShift β ℤ]
    {TX : C} {TX' : D} {TY : C'} {TY' : D'} (σM₀ : TX' ⟶ ΨM.obj TX) (σN₀ : TY' ⟶ ΨN.obj TY)
    (τ₀ : Lf.obj TX ≅ TY) (τ₀' : Lf'.obj TX' ≅ TY')
    (h₀ : τ₀'.inv ≫ Lf'.map σM₀ ≫ β.app TX = σN₀ ≫ ΨN.map τ₀.inv) (n : ℤ)
    (σM : TX'⟦n⟧ ⟶ ΨM.obj (TX⟦n⟧)) (hM : σM ≫ (ΨM.commShiftIso n).hom.app TX = σM₀⟦n⟧')
    (σN : TY'⟦n⟧ ⟶ ΨN.obj (TY⟦n⟧)) (hN : σN ≫ (ΨN.commShiftIso n).hom.app TY = σN₀⟦n⟧') :
    ((Lf'.commShiftIso n).app TX' ≪≫ (shiftFunctor D' n).mapIso τ₀').inv ≫ Lf'.map σM ≫
        β.app (TX⟦n⟧) =
      σN ≫ ΨN.map ((Lf.commShiftIso n).app TX ≪≫ (shiftFunctor C' n).mapIso τ₀).inv := by
  replace hM : σM = σM₀⟦n⟧' ≫ (ΨM.commShiftIso n).inv.app TX := by rw [← hM]; simp
  replace hN : σN = σN₀⟦n⟧' ≫ (ΨN.commShiftIso n).inv.app TY := by rw [← hN]; simp
  have h₁ := congrArg (fun g ↦ g⟦n⟧') h₀
  simp only [Functor.map_comp] at h₁
  rw [hM, hN, NatTrans.app_shift β n TX]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc, Functor.map_comp,
    Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_inv_app, Functor.comp_obj]
  rw [← Functor.map_comp_assoc Lf' ((ΨM.commShiftIso n).inv.app TX), Iso.inv_hom_id_app]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← Functor.commShiftIso_inv_naturality_assoc,
    Iso.inv_hom_id_app_assoc, ← Functor.commShiftIso_inv_naturality_assoc ΨN, reassoc_of% h₁]

/-- **Twist isomorphisms and exchanges**, abstractly: for an exchange `β : Ψ_M ⋙ Lf' ⟶ Lf ⋙ Ψ_N`
compatible with the lax tensor maps of `Ψ_M`, `Ψ_N` and the monoidal structures of `Lf`, `Lf'`,
and compatible with specialization maps `σ_M : T_{X'} ⟶ Ψ_M T_X`, `σ_N : T_{Y'} ⟶ Ψ_N T_Y` along
`τ : Lf T_X ≅ T_Y`, `τ' : Lf' T_{X'} ≅ T_{Y'}`, the twist isomorphisms
`κ : Ψ (A ⊗ T) ≅ Ψ A ⊗ T'` with inverses `μ ∘ (Ψ A ◁ σ)` are compatible with `β`. -/
lemma twistIso_exchange {DX DY DX' DY' : Type*} [Category DX] [Category DY] [Category DX']
    [Category DY'] [MonoidalCategory DX] [MonoidalCategory DY] [MonoidalCategory DX']
    [MonoidalCategory DY'] {ΨM : DX ⥤ DX'} {ΨN : DY ⥤ DY'} {Lf : DX ⥤ DY} {Lf' : DX' ⥤ DY'}
    [Lf.Monoidal] [Lf'.Monoidal] (μM : ∀ A B : DX, ΨM.obj A ⊗ ΨM.obj B ⟶ ΨM.obj (A ⊗ B))
    (μN : ∀ A B : DY, ΨN.obj A ⊗ ΨN.obj B ⟶ ΨN.obj (A ⊗ B))
    (hμN : ∀ {A A' B B' : DY} (x : A ⟶ A') (y : B ⟶ B'),
      (ΨN.map x ⊗ₘ ΨN.map y) ≫ μN A' B' = μN A B ≫ ΨN.map (x ⊗ₘ y))
    (β : ΨM ⋙ Lf' ⟶ Lf ⋙ ΨN)
    (hβ : ∀ A B, (β.app A ⊗ₘ β.app B) ≫ μN _ _ ≫ ΨN.map (Functor.LaxMonoidal.μ Lf A B) =
      Functor.LaxMonoidal.μ Lf' _ _ ≫ Lf'.map (μM A B) ≫ β.app (A ⊗ B))
    {TX : DX} {TX' : DX'} {TY : DY} {TY' : DY'} (σM : TX' ⟶ ΨM.obj TX) (σN : TY' ⟶ ΨN.obj TY)
    (τ : Lf.obj TX ≅ TY) (τ' : Lf'.obj TX' ≅ TY')
    (hσ : τ'.inv ≫ Lf'.map σM ≫ β.app TX = σN ≫ ΨN.map τ.inv)
    (κM : ∀ A : DX, ΨM.obj (A ⊗ TX) ≅ ΨM.obj A ⊗ TX')
    (hκM : ∀ A, (κM A).inv = ΨM.obj A ◁ σM ≫ μM A TX)
    (κN : ∀ A : DY, ΨN.obj (A ⊗ TY) ≅ ΨN.obj A ⊗ TY')
    (hκN : ∀ A, (κN A).inv = ΨN.obj A ◁ σN ≫ μN A TY) (A : DX) :
    Lf'.map (κM A).hom ≫
        ((Functor.Monoidal.μIso Lf' (ΨM.obj A) TX').symm ≪≫
          whiskerLeftIso (Lf'.obj (ΨM.obj A)) τ').hom ≫ β.app A ▷ TY' =
      β.app (A ⊗ TX) ≫
        ΨN.map ((Functor.Monoidal.μIso Lf A TX).symm ≪≫ whiskerLeftIso (Lf.obj A) τ).hom ≫
        (κN (Lf.obj A)).hom := by
  -- the inverse equation
  have key : β.app A ▷ TY' ≫ (κN (Lf.obj A)).inv ≫ ΨN.map
        ((Functor.Monoidal.μIso Lf A TX).symm ≪≫ whiskerLeftIso (Lf.obj A) τ).inv =
      ((Functor.Monoidal.μIso Lf' (ΨM.obj A) TX').symm ≪≫
          whiskerLeftIso (Lf'.obj (ΨM.obj A)) τ').inv ≫ Lf'.map (κM A).inv ≫ β.app (A ⊗ TX) := by
    rw [hκN, hκM]
    simp only [Iso.trans_inv, Iso.symm_inv, whiskerLeftIso_inv, Functor.Monoidal.μIso_hom,
      Functor.map_comp, Category.assoc]
    have hN' : ΨN.obj (Lf.obj A) ◁ ΨN.map τ.inv ≫ μN (Lf.obj A) (Lf.obj TX) =
        μN _ _ ≫ ΨN.map (Lf.obj A ◁ τ.inv) := by
      simpa using hμN (𝟙 (Lf.obj A)) τ.inv
    rw [← Functor.LaxMonoidal.μ_natural_right_assoc Lf', ← hβ, ← reassoc_of% hN',
      ← whiskerLeft_comp_assoc, ← hσ]
    have hx := whisker_exchange (β.app A) (τ'.inv ≫ Lf'.map σM ≫ β.app TX)
    simp only [Functor.comp_obj] at hx
    rw [← reassoc_of% hx, tensorHom_def']
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rfl
  have k₂ := congrArg (fun g ↦ Lf'.map (κM A).hom ≫
    ((Functor.Monoidal.μIso Lf' (ΨM.obj A) TX').symm ≪≫
      whiskerLeftIso (Lf'.obj (ΨM.obj A)) τ').hom ≫ g ≫
    ΨN.map ((Functor.Monoidal.μIso Lf A TX).symm ≪≫ whiskerLeftIso (Lf.obj A) τ).hom ≫
    (κN (Lf.obj A)).hom) key
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc,
    ← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp] at k₂
  exact k₂

/-- The comparison `F (Z ⊗ T) ≅ F Z ⊗ T'` of a monoidal functor, for `τ : F T ≅ T'`, is natural
in `Z`. -/
lemma μIso_symm_trans_whiskerLeftIso_hom_naturality {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal] {T : C} {T' : D}
    (τ : F.obj T ≅ T') {Z Z' : C} (f : Z ⟶ Z') :
    F.map (f ▷ T) ≫ ((Functor.Monoidal.μIso F Z' T).symm ≪≫ whiskerLeftIso _ τ).hom =
      ((Functor.Monoidal.μIso F Z T).symm ≪≫ whiskerLeftIso _ τ).hom ≫ F.map f ▷ T' := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.Monoidal.μIso_inv, whiskerLeftIso_hom]
  rw [← Functor.OplaxMonoidal.δ_natural_left_assoc, ← whisker_exchange, Category.assoc]

end Abstract

section AmbientTwist

variable (ℓ : ℕ) [Fact ℓ.Prime] {X X' Y Y' : Scheme.{u}}

/-- The specialization map `σ : ℚ̄_ℓ,X'(0)[n] ⟶ Ψ (ℚ̄_ℓ,X(0)[n])` of a model on the ambient derived
categories (the underlying morphism of `NearbyCyclesModel.zeroTwistSpecializationMap`). -/
noncomputable abbrev ambientZeroTwistSpecializationMap (M : NearbyCyclesModel X X') (n : ℤ) :
    (shiftFunctor _ n).obj (tateTwistDerived X' ℓ 0) ⟶
      (M.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
        ((shiftFunctor _ n).obj (tateTwistDerived X ℓ 0)) :=
  ((shiftFunctor _ n).mapIso (leftDerivedUpperStarTateTwistDerivedZeroIso M.i ℓ).symm ≪≫
    ((L((M.i)^*⟦Profinite.padicAlgClRingObj ℓ⟧).commShiftIso n).app _).symm).hom ≫
      M.twistSpecializationMap _
        (((L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).commShiftIso n).app _) ≪≫
          (shiftFunctor _ n).mapIso (leftDerivedUpperStarTateTwistDerivedZeroIso M.ε ℓ ≪≫
            (leftDerivedUpperStarTateTwistDerivedZeroIso M.j ℓ).symm) ≪≫
          ((L((M.j)^*⟦Profinite.padicAlgClRingObj ℓ⟧).commShiftIso n).app _).symm)

/-- The pullback `Lf^* (ℚ̄_ℓ,X(0)[n]) ≅ ℚ̄_ℓ,Y(0)[n]` of the twist `ℚ̄_ℓ(0)[n]`. -/
noncomputable def tateTwistZeroShiftUpperStarIso (f : Y ⟶ X) (n : ℤ) :
    L((f)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj ((shiftFunctor _ n).obj (tateTwistDerived X ℓ 0)) ≅
      (shiftFunctor _ n).obj (tateTwistDerived Y ℓ 0) :=
  (L((f)^*⟦Profinite.padicAlgClRingObj ℓ⟧).commShiftIso n).app _ ≪≫
    (shiftFunctor _ n).mapIso (leftDerivedUpperStarTateTwistDerivedZeroIso f ℓ)

variable {ℓ} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'} {f : Y ⟶ X} {f' : Y' ⟶ X'}

/-- The unit law of the pullback exchange
(`NearbyCyclesModel.Hom.map_unit_comp_pullbackExchange_app`) for the specialization maps of
`ℚ̄_ℓ(0)` in degree `0`. -/
lemma Hom.pullbackExchange_zeroTwistSpecialization_zero (φ : N.Hom M f f') :
    (leftDerivedUpperStarTateTwistDerivedZeroIso f' ℓ).inv ≫
        L((f')^*⟦Profinite.padicAlgClRingObj ℓ⟧).map
          ((leftDerivedUpperStarTateTwistDerivedZeroIso M.i ℓ).inv ≫ M.twistSpecializationMap _
            (leftDerivedUpperStarTateTwistDerivedZeroIso M.ε ℓ ≪≫
              (leftDerivedUpperStarTateTwistDerivedZeroIso M.j ℓ).symm)) ≫
        (φ.pullbackExchange _).app (tateTwistDerived X ℓ 0) =
      ((leftDerivedUpperStarTateTwistDerivedZeroIso N.i ℓ).inv ≫ N.twistSpecializationMap _
          (leftDerivedUpperStarTateTwistDerivedZeroIso N.ε ℓ ≪≫
            (leftDerivedUpperStarTateTwistDerivedZeroIso N.j ℓ).symm)) ≫
        (N.nearbyCycles _).map (leftDerivedUpperStarTateTwistDerivedZeroIso f ℓ).inv := by
  -- Identify the zero twists with the units on small expressions before simplifying the exchange.
  have hM : (leftDerivedUpperStarTateTwistDerivedZeroIso M.i ℓ).inv ≫
      M.twistSpecializationMap _ (leftDerivedUpperStarTateTwistDerivedZeroIso M.ε ℓ ≪≫
        (leftDerivedUpperStarTateTwistDerivedZeroIso M.j ℓ).symm) = M.unit _ := by
    rw [twistSpecializationMap_tateTwistZero, leftDerivedUpperStarTateTwistDerivedZeroIso_eq,
      Iso.inv_hom_id_assoc]
  have hN : (leftDerivedUpperStarTateTwistDerivedZeroIso N.i ℓ).inv ≫
      N.twistSpecializationMap _ (leftDerivedUpperStarTateTwistDerivedZeroIso N.ε ℓ ≪≫
        (leftDerivedUpperStarTateTwistDerivedZeroIso N.j ℓ).symm) = N.unit _ := by
    rw [twistSpecializationMap_tateTwistZero, leftDerivedUpperStarTateTwistDerivedZeroIso_eq,
      Iso.inv_hom_id_assoc]
  have hf' : (leftDerivedUpperStarTateTwistDerivedZeroIso f' ℓ).inv =
      (leftDerivedUpperStarUnitIso (Profinite.padicAlgClRingObj ℓ) f').inv := by
    rw [leftDerivedUpperStarTateTwistDerivedZeroIso_eq]
  have hf : (leftDerivedUpperStarTateTwistDerivedZeroIso f ℓ).inv =
      (leftDerivedUpperStarUnitIso (Profinite.padicAlgClRingObj ℓ) f).inv := by
    rw [leftDerivedUpperStarTateTwistDerivedZeroIso_eq]
  have hu : (leftDerivedUpperStarUnitIso (Profinite.padicAlgClRingObj ℓ) f').inv ≫
      L((f')^*⟦Profinite.padicAlgClRingObj ℓ⟧).map (M.unit _) ≫
        (φ.pullbackExchange _).app (tateTwistDerived X ℓ 0) =
      N.unit _ ≫ (N.nearbyCycles _).map
        (leftDerivedUpperStarUnitIso (Profinite.padicAlgClRingObj ℓ) f).inv := by
    have hu0 : L((f')^*⟦Profinite.padicAlgClRingObj ℓ⟧).map (M.unit _) ≫
        (φ.pullbackExchange _).app (tateTwistDerived X ℓ 0) =
        (leftDerivedUpperStarUnitIso (Profinite.padicAlgClRingObj ℓ) f').hom ≫ N.unit _ ≫
          (N.nearbyCycles _).map (leftDerivedUpperStarUnitIso
            (Profinite.padicAlgClRingObj ℓ) f).inv := by
      transport_exact φ.map_unit_comp_pullbackExchange_app (Profinite.padicAlgClRingObj ℓ)
    rw [hu0, Iso.inv_hom_id_assoc]
  simpa only [hM, hN, hf', hf] using hu

-- the shifts of the derived categories of module objects unfold deeply
/-- The specialization map of `ℚ̄_ℓ(0)[n]` is the shift of that of `ℚ̄_ℓ(0)`
(`NearbyCyclesModel.twistSpecializationMap_shift_comp`). -/
lemma ambientZeroTwistSpecializationMap_comp_commShiftIso (M : NearbyCyclesModel X X') (n : ℤ) :
    ambientZeroTwistSpecializationMap ℓ M n ≫
        ((M.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).commShiftIso n).hom.app
          (tateTwistDerived X ℓ 0) =
      (shiftFunctor _ n).map ((leftDerivedUpperStarTateTwistDerivedZeroIso M.i ℓ).inv ≫
        M.twistSpecializationMap _ (leftDerivedUpperStarTateTwistDerivedZeroIso M.ε ℓ ≪≫
          (leftDerivedUpperStarTateTwistDerivedZeroIso M.j ℓ).symm)) := by
  unfold ambientZeroTwistSpecializationMap
  rw [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.symm_hom,
    Category.assoc, Category.assoc, twistSpecializationMap_shift_comp, ← Functor.map_comp]

/-- **The pullback exchange and the specialization maps of `ℚ̄_ℓ(0)[n]`** (ambient): the pullback
along `f'` of the specialization map of `M`, followed by the pullback exchange of `φ : N ⟶ M`, is
the specialization map of `N`, up to the pullbacks of the twists. In degree `0` this is the unit
law of the exchange (`NearbyCyclesModel.Hom.map_unit_comp_pullbackExchange_app`); in degree `n`
everything commutes with the shifts. -/
lemma Hom.pullbackExchange_ambientZeroTwistSpecializationMap (φ : N.Hom M f f') (n : ℤ) :
    (tateTwistZeroShiftUpperStarIso ℓ f' n).inv ≫
        L((f')^*⟦Profinite.padicAlgClRingObj ℓ⟧).map (ambientZeroTwistSpecializationMap ℓ M n) ≫
        (φ.pullbackExchange _).app ((shiftFunctor _ n).obj (tateTwistDerived X ℓ 0)) =
      ambientZeroTwistSpecializationMap ℓ N n ≫
        (N.nearbyCycles _).map (tateTwistZeroShiftUpperStarIso ℓ f n).inv := by
  unfold tateTwistZeroShiftUpperStarIso
  have key := shift_specialization_exchange (ΨM := M.nearbyCycles (Profinite.padicAlgClRingObj ℓ))
    (ΨN := N.nearbyCycles (Profinite.padicAlgClRingObj ℓ))
    (Lf := L((f)^*⟦Profinite.padicAlgClRingObj ℓ⟧))
    (Lf' := L((f')^*⟦Profinite.padicAlgClRingObj ℓ⟧))
    (TX := tateTwistDerived X ℓ 0) (TX' := tateTwistDerived X' ℓ 0)
    (TY := tateTwistDerived Y ℓ 0) (TY' := tateTwistDerived Y' ℓ 0)
    (φ.pullbackExchange _)
    ((leftDerivedUpperStarTateTwistDerivedZeroIso M.i ℓ).inv ≫ M.twistSpecializationMap _
      (leftDerivedUpperStarTateTwistDerivedZeroIso M.ε ℓ ≪≫
        (leftDerivedUpperStarTateTwistDerivedZeroIso M.j ℓ).symm))
    ((leftDerivedUpperStarTateTwistDerivedZeroIso N.i ℓ).inv ≫ N.twistSpecializationMap _
      (leftDerivedUpperStarTateTwistDerivedZeroIso N.ε ℓ ≪≫
        (leftDerivedUpperStarTateTwistDerivedZeroIso N.j ℓ).symm))
    (leftDerivedUpperStarTateTwistDerivedZeroIso f ℓ)
    (leftDerivedUpperStarTateTwistDerivedZeroIso f' ℓ)
    (by transport_exact φ.pullbackExchange_zeroTwistSpecialization_zero (ℓ := ℓ)) n
    (ambientZeroTwistSpecializationMap ℓ M n)
    (by transport_exact ambientZeroTwistSpecializationMap_comp_commShiftIso (ℓ := ℓ) M n)
    (ambientZeroTwistSpecializationMap ℓ N n)
    (by transport_exact ambientZeroTwistSpecializationMap_comp_commShiftIso (ℓ := ℓ) N n)
  transport_exact key

end AmbientTwist

section SquareIso

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The pullback comparison `Lj'^* Lp^* ≅ Lp'^* Lj^*` of a commutative square `p' ≫ j = j' ≫ p`
of schemes (`ProEtale.CondensedRing.pullbackSquareComparison`), as an irreducible definition:
otherwise the elaborator and the kernel unfold it when comparing its components with those of its
restrictions to bounded constructible complexes. -/
noncomputable irreducible_def pullbackSquareComparison' {X X' Y Y' : Scheme.{u}}
    {p : X' ⟶ X} {p' : Y' ⟶ Y} {j : Y ⟶ X} {j' : Y' ⟶ X'} (hs : p' ≫ j = j' ≫ p) :
    L((p)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙ L((j')^*⟦Profinite.padicAlgClRingObj ℓ⟧) ≅
      L((j)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙ L((p')^*⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  pullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) (⟨hs⟩ : CommSq p' j' j p)

variable {k₁ k₂ k₃ k₄ : Type u} [Field k₁] [Field k₂] [Field k₃] [Field k₄]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)] [Fact (ringChar k₃).Prime] [Fact (ringChar k₃ ≠ ℓ)]
  [Fact (ringChar k₄).Prime] [Fact (ringChar k₄ ≠ ℓ)]
  {X : Over (Spec (.of k₁))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k₂))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] {Y : Over (Spec (.of k₃))} [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] {Y' : Over (Spec (.of k₄))}
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {p : X'.left ⟶ X.left} {p' : Y'.left ⟶ Y.left} {j : Y.left ⟶ X.left} {j' : Y'.left ⟶ X'.left}

/-- The pullback comparison `Lj'^* Lp^* A ≅ Lp'^* Lj^* A` of a commutative square
`p' ≫ j = j' ≫ p` on bounded constructible complexes. -/
noncomputable def boundedConstructibleUpperStarSquareIso (hs : p' ≫ j = j' ≫ p)
    (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarOfMap ℓ (X := X') (Y := Y') j').obj
        ((boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') p).obj A) ≅
      (boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := Y') p').obj
        ((boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := Y) j).obj A) :=
  ObjectProperty.isoMk _ ((pullbackSquareComparison' ℓ hs).app A.obj)

omit [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)] [Fact (ringChar k₃).Prime] [Fact (ringChar k₃ ≠ ℓ)]
  [Fact (ringChar k₄).Prime] [Fact (ringChar k₄ ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom] in
lemma boundedConstructibleUpperStarSquareIso_hom_hom (hs : p' ≫ j = j' ≫ p)
    (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarSquareIso ℓ hs A).hom.hom =
      (pullbackSquareComparison' ℓ hs).hom.app A.obj :=
  rfl

omit [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)] [Fact (ringChar k₃).Prime] [Fact (ringChar k₃ ≠ ℓ)]
  [Fact (ringChar k₄).Prime] [Fact (ringChar k₄ ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom] in
/-- Naturality of `NearbyCyclesModel.boundedConstructibleUpperStarSquareIso`. -/
lemma boundedConstructibleUpperStarSquareIso_hom_naturality (hs : p' ≫ j = j' ≫ p)
    {A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (f : A ⟶ B) :
    (boundedConstructibleUpperStarOfMap ℓ (X := X') (Y := Y') j').map
        ((boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') p).map f) ≫
      (boundedConstructibleUpperStarSquareIso ℓ hs B).hom =
    (boundedConstructibleUpperStarSquareIso ℓ hs A).hom ≫
      (boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := Y') p').map
        ((boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := Y) j).map f) := by
  apply ObjectProperty.hom_ext
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    boundedConstructibleUpperStarSquareIso_hom_hom, boundedConstructibleUpperStarSquareIso_hom_hom]
  transport_exact (pullbackSquareComparison' ℓ hs).hom.naturality f.hom

end SquareIso


section AmbientSquare

variable (ℓ : ℕ) [Fact ℓ.Prime] {X X' X₁ X₁' Z Z' Z₁ Z₁' : Scheme.{u}}
  {M : NearbyCyclesModel X X'} {M₁ : NearbyCyclesModel X₁ X₁'} {P : NearbyCyclesModel Z Z'}
  {P₁ : NearbyCyclesModel Z₁ Z₁'} {g : X ⟶ X₁} {g' : X' ⟶ X₁'} {k : Z ⟶ Z₁} {k' : Z' ⟶ Z₁'}
  {e : Z₁ ⟶ X₁} {e' : Z₁' ⟶ X₁'} {f₀ : Z ⟶ X} {f₀' : Z' ⟶ X'}

/-- `NearbyCyclesModel.Hom.pullbackExchange_square` for comparisons `E₁`, `E₂` given as equal to
the pullback comparisons of the squares. -/
private lemma pullbackExchange_square_of_eq (φ₀ : P.Hom M f₀ f₀') (ψ : M.Hom M₁ g g')
    (ψ' : P.Hom P₁ k k') (φ₁ : P₁.Hom M₁ e e') (htot : φ₀.total ≫ ψ.total = ψ'.total ≫ φ₁.total)
    (hgen : φ₀.generic ≫ ψ.generic = ψ'.generic ≫ φ₁.generic) (hb : f₀ ≫ g = k ≫ e)
    (hs : f₀' ≫ g' = k' ≫ e')
    {E₁ : _} (h₁ : E₁ = pullbackSquareComparison (Profinite.padicAlgClRingObj ℓ)
      (⟨hs⟩ : CommSq f₀' k' g' e'))
    {E₂ : _} (h₂ : E₂ = pullbackSquareComparison (Profinite.padicAlgClRingObj ℓ)
      (⟨hb⟩ : CommSq f₀ k g e))
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X₁) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X₁))) :
    E₁.hom.app ((M₁.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj C) ≫
      L((f₀')^*⟦Profinite.padicAlgClRingObj ℓ⟧).map
        ((ψ.pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app C) ≫
      (φ₀.pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app
        (L((g)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C) =
    L((k')^*⟦Profinite.padicAlgClRingObj ℓ⟧).map
        ((φ₁.pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app C) ≫
      (ψ'.pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app
        (L((e)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C) ≫
      (P.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).map (E₂.hom.app C) := by
  subst h₁ h₂
  transport_exact Hom.pullbackExchange_square _ φ₀ ψ ψ' φ₁ htot hgen hb hs C

/-- `NearbyCyclesModel.Hom.pullbackExchange_square` with the irreducible comparisons
`NearbyCyclesModel.pullbackSquareComparison'`. -/
lemma pullbackExchange_square' (φ₀ : P.Hom M f₀ f₀') (ψ : M.Hom M₁ g g') (ψ' : P.Hom P₁ k k')
    (φ₁ : P₁.Hom M₁ e e') (htot : φ₀.total ≫ ψ.total = ψ'.total ≫ φ₁.total)
    (hgen : φ₀.generic ≫ ψ.generic = ψ'.generic ≫ φ₁.generic) (hb : f₀ ≫ g = k ≫ e)
    (hs : f₀' ≫ g' = k' ≫ e')
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X₁) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X₁))) :
    (pullbackSquareComparison' ℓ hs).hom.app
        ((M₁.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj C) ≫
      L((f₀')^*⟦Profinite.padicAlgClRingObj ℓ⟧).map
        ((ψ.pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app C) ≫
      (φ₀.pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app
        (L((g)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C) =
    L((k')^*⟦Profinite.padicAlgClRingObj ℓ⟧).map
        ((φ₁.pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app C) ≫
      (ψ'.pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app
        (L((e)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C) ≫
      (P.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).map
        ((pullbackSquareComparison' ℓ hb).hom.app C) :=
  pullbackExchange_square_of_eq ℓ φ₀ ψ ψ' φ₁ htot hgen hb hs
    (pullbackSquareComparison'_def ℓ hs) (pullbackSquareComparison'_def ℓ hb) C

end AmbientSquare

section SquareExchange

variable {ℓ : ℕ} [Fact ℓ.Prime] {kX kS k₂ ks : Type u} [Field kX] [Field kS] [Field k₂] [Field ks]
  [Fact (ringChar kX).Prime] [Fact (ringChar kX ≠ ℓ)] [Fact (ringChar kS).Prime]
  [Fact (ringChar kS ≠ ℓ)] [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ ℓ)]
  [Fact (ringChar ks).Prime] [Fact (ringChar ks ≠ ℓ)]
  {Xc X₁ : Over (Spec (.of kX))} [LocallyOfFiniteType Xc.hom] [QuasiCompact Xc.hom]
  [IsSeparated Xc.hom] [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  {Xc' X' : Over (Spec (.of kS))} [LocallyOfFiniteType Xc'.hom] [QuasiCompact Xc'.hom]
  [IsSeparated Xc'.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  {X₂c X₂ : Over (Spec (.of k₂))} [LocallyOfFiniteType X₂c.hom] [QuasiCompact X₂c.hom]
  [IsSeparated X₂c.hom] [LocallyOfFiniteType X₂.hom] [QuasiCompact X₂.hom] [IsSeparated X₂.hom]
  {Ysc Ys : Over (Spec (.of ks))} [LocallyOfFiniteType Ysc.hom] [QuasiCompact Ysc.hom]
  [IsSeparated Ysc.hom] [LocallyOfFiniteType Ys.hom] [QuasiCompact Ys.hom] [IsSeparated Ys.hom]
  {Mc : NearbyCyclesModel Xc.left Xc'.left} {M : NearbyCyclesModel X₁.left X'.left}
  {M₂c : NearbyCyclesModel X₂c.left Ysc.left} {M₂ : NearbyCyclesModel X₂.left Ys.left}
  {j : X₁ ⟶ Xc} {j' : X' ⟶ Xc'} {j₂ : X₂ ⟶ X₂c} {j₂' : Ys ⟶ Ysc}
  {c : X₂.left ⟶ X₁.left} {cc : X₂c.left ⟶ Xc.left} {p : Ys.left ⟶ X'.left}
  {pc : Ysc.left ⟶ Xc'.left}

private lemma boundedConstructibleNearbyCycles_map_hom'' {X X' : Scheme.{u}}
    {N : NearbyCyclesModel X X'}
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    {A B : Dᵇc(X)⟦Profinite.padicAlgClRingObj ℓ⟧} (f : A ⟶ B) :
    ((boundedConstructibleNearbyCycles hN).map f).hom =
      (N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).map f.hom :=
  rfl

/-- **The square law of the pullback exchanges** on bounded constructible complexes
(`NearbyCyclesModel.Hom.pullbackExchange_square`), for a commutative square of morphisms of
models `φ₀ : M₂ ⟶ M`, `ψ : M ⟶ M_c`, `ψ' : M₂ ⟶ M₂,c`, `φ₁ : M₂,c ⟶ M_c` in which `ψ` and `ψ'`
lie over morphisms over the base fields, and exchanges `α`, `α_c` of `φ₀`, `φ₁` given as equal to
`NearbyCyclesModel.liftExchange`. -/
lemma boundedConstructiblePullbackExchange_square (φ₀ : M₂.Hom M c p)
    (ψ : M.Hom Mc j.left j'.left) (ψ' : M₂.Hom M₂c j₂.left j₂'.left) (φ₁ : M₂c.Hom Mc cc pc)
    (htot : φ₀.total ≫ ψ.total = ψ'.total ≫ φ₁.total)
    (hgen : φ₀.generic ≫ ψ.generic = ψ'.generic ≫ φ₁.generic) (hb : c ≫ j.left = j₂.left ≫ cc)
    (hs : p ≫ j'.left = j₂'.left ≫ pc)
    (hMc : Mc.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hM₂c : M₂c.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hM₂ : M₂.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (α : boundedConstructibleNearbyCycles hM ⋙
        boundedConstructibleUpperStarOfMap ℓ (X := X') (Y := Ys) p ⟶
      boundedConstructibleUpperStarOfMap ℓ (X := X₁) (Y := X₂) c ⋙
        boundedConstructibleNearbyCycles hM₂)
    (hα : α = liftExchange (PY := boundedConstructible _) (PX := boundedConstructible _)
        (PY' := boundedConstructible _) (PX' := boundedConstructible _)
        (φ₀.pullbackExchange (Profinite.padicAlgClRingObj ℓ))
        (fun K ↦ hM K.obj K.property) (fun K ↦ hM₂ K.obj K.property)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ p K.obj K.property)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ c K.obj K.property))
    (αc : boundedConstructibleNearbyCycles hMc ⋙
        boundedConstructibleUpperStarOfMap ℓ (X := Xc') (Y := Ysc) pc ⟶
      boundedConstructibleUpperStarOfMap ℓ (X := Xc) (Y := X₂c) cc ⋙
        boundedConstructibleNearbyCycles hM₂c)
    (hαc : αc = liftExchange (PY := boundedConstructible _) (PX := boundedConstructible _)
        (PY' := boundedConstructible _) (PX' := boundedConstructible _)
        (φ₁.pullbackExchange (Profinite.padicAlgClRingObj ℓ))
        (fun K ↦ hMc K.obj K.property) (fun K ↦ hM₂c K.obj K.property)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ pc K.obj K.property)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ cc K.obj K.property))
    (A : Dᵇc(Xc.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarSquareIso ℓ (X := Xc') (X' := Ysc) (Y := X') (Y' := Ys) hs
        ((boundedConstructibleNearbyCycles hMc).obj A)).hom ≫
      (boundedConstructibleUpperStarOfMap ℓ (X := X') (Y := Ys) p).map
        ((ψ.boundedConstructiblePullbackExchange ℓ hM hMc).app A) ≫
      α.app ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj A) =
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j₂').map (αc.app A) ≫
      (ψ'.boundedConstructiblePullbackExchange ℓ hM₂ hM₂c).app
        ((boundedConstructibleUpperStarOfMap ℓ (X := Xc) (Y := X₂c) cc).obj A) ≫
      (boundedConstructibleNearbyCycles hM₂).map
        (boundedConstructibleUpperStarSquareIso ℓ (X := Xc) (X' := X₂c) (Y := X₁) (Y' := X₂) hb
          A).hom := by
  subst hα hαc
  apply ObjectProperty.hom_ext
  -- Simplify the underlying morphisms together to avoid repeated rewrite motive checks.
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleUpperStarOfMap_map,
    ObjectProperty.homMk_hom, boundedConstructibleUpperStar_map_hom, liftExchange_app_hom,
    Hom.boundedConstructiblePullbackExchange_app_hom,
    boundedConstructibleUpperStarSquareIso_hom_hom, boundedConstructibleNearbyCycles_map_hom'']
  transport_exact pullbackExchange_square' ℓ φ₀ ψ ψ' φ₁ htot hgen hb hs A.obj

end SquareExchange

section BoundedConstructibleTwist

attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

variable {ℓ : ℕ} [Fact ℓ.Prime] {kX kX' kY kY' : Type u} [Field kX] [Field kX'] [Field kY]
  [Field kY'] [Fact (ringChar kX).Prime] [Fact (ringChar kX ≠ ℓ)] [Fact (ringChar kX').Prime]
  [Fact (ringChar kX' ≠ ℓ)] [Fact (ringChar kY).Prime] [Fact (ringChar kY ≠ ℓ)]
  [Fact (ringChar kY').Prime] [Fact (ringChar kY' ≠ ℓ)]
  {X : Over (Spec (.of kX))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of kX'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] {Y : Over (Spec (.of kY))} [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] {Y' : Over (Spec (.of kY'))}
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {M : NearbyCyclesModel X.left X'.left} {N : NearbyCyclesModel Y.left Y'.left}
  {f : Y.left ⟶ X.left} {f' : Y'.left ⟶ X'.left}

variable (ℓ) in
/-- The pullback `Lf^* (ℚ̄_ℓ,X(0)[n]) ≅ ℚ̄_ℓ,Y(0)[n]` on bounded constructible complexes. -/
noncomputable def boundedConstructibleTateTwistZeroUpperStarIso (f : Y.left ⟶ X.left) (n : ℤ) :
    (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := Y) f).obj
        (boundedConstructibleTateTwist ℓ X 0 n) ≅ boundedConstructibleTateTwist ℓ Y 0 n :=
  ObjectProperty.isoMk _ (tateTwistZeroShiftUpperStarIso ℓ f n)

/-- **The pullback exchange and the specialization maps of `ℚ̄_ℓ(0)[n]`** on bounded
constructible complexes
(`NearbyCyclesModel.Hom.pullbackExchange_ambientZeroTwistSpecializationMap`),
for an exchange `β` given as equal to `NearbyCyclesModel.liftExchange` of the pullback exchange. -/
lemma Hom.liftExchange_zeroTwistSpecializationMap (φ : N.Hom M f f')
    (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (β : boundedConstructibleNearbyCycles hM ⋙
        boundedConstructibleUpperStarOfMap ℓ (X := X') (Y := Y') f' ⟶
      boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := Y) f ⋙
        boundedConstructibleNearbyCycles hN)
    (hβ : β = liftExchange (PY := boundedConstructible _) (PX := boundedConstructible _)
        (PY' := boundedConstructible _) (PX' := boundedConstructible _)
        (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))
        (fun K ↦ hM K.obj K.property) (fun K ↦ hN K.obj K.property)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ f' K.obj K.property)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ f K.obj K.property))
    (n : ℤ) :
    (boundedConstructibleTateTwistZeroUpperStarIso ℓ (X := X') (Y := Y') f' n).inv ≫
        (boundedConstructibleUpperStarOfMap ℓ (X := X') (Y := Y') f').map
          (M.zeroTwistSpecializationMap hM n) ≫ β.app (boundedConstructibleTateTwist ℓ X 0 n) =
      N.zeroTwistSpecializationMap hN n ≫ (boundedConstructibleNearbyCycles hN).map
        (boundedConstructibleTateTwistZeroUpperStarIso ℓ (X := X) (Y := Y) f n).inv := by
  subst hβ
  apply ObjectProperty.hom_ext
  -- Simplify the underlying morphisms together to avoid repeated rewrite motive checks.
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleUpperStarOfMap_map,
    ObjectProperty.homMk_hom, liftExchange_app_hom, boundedConstructibleNearbyCycles_map_hom'',
    boundedConstructibleTateTwistZeroUpperStarIso, ObjectProperty.isoMk_inv,
    zeroTwistSpecializationMap]
  transport_exact φ.pullbackExchange_ambientZeroTwistSpecializationMap (ℓ := ℓ) n

/-- **The twist isomorphisms `κ` and the pullback exchange** on bounded constructible complexes:
for a morphism of models `φ : N ⟶ M` and an exchange `β` given as equal to the restriction of the
pullback exchange, `Lf'^*(κ_M) ≫ (Lf'^* (Ψ_M A ⊗ T) ≅ Lf'^* Ψ_M A ⊗ T) ≫ β ▷ T` is
`β ≫ Ψ_N(Lf^* (A ⊗ T) ≅ Lf^* A ⊗ T) ≫ κ_N`, `T = ℚ̄_ℓ(0)[n]`. -/
lemma Hom.liftExchange_zeroTwistIso (φ : N.Hom M f f')
    (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (qM : M.total ⟶ trait kX') (qN : N.total ⟶ trait kY')
    (β : boundedConstructibleNearbyCycles hM ⋙
        boundedConstructibleUpperStarOfMap ℓ (X := X') (Y := Y') f' ⟶
      boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := Y) f ⋙
        boundedConstructibleNearbyCycles hN)
    (hβ : β = liftExchange (PY := boundedConstructible _) (PX := boundedConstructible _)
        (PY' := boundedConstructible _) (PX' := boundedConstructible _)
        (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))
        (fun K ↦ hM K.obj K.property) (fun K ↦ hN K.obj K.property)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ f' K.obj K.property)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ f K.obj K.property))
    (n : ℤ) (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarOfMap ℓ (X := X') (Y := Y') f').map
        (M.zeroTwistIso hM qM n A).hom ≫
      ((Functor.Monoidal.μIso (boundedConstructibleUpperStarOfMap ℓ (X := X') (Y := Y') f')
          ((boundedConstructibleNearbyCycles hM).obj A)
          (boundedConstructibleTateTwist ℓ X' 0 n)).symm ≪≫
        whiskerLeftIso _ (boundedConstructibleTateTwistZeroUpperStarIso ℓ (X := X') (Y := Y') f'
          n)).hom ≫ β.app A ▷ boundedConstructibleTateTwist ℓ Y' 0 n =
    β.app (A ⊗ boundedConstructibleTateTwist ℓ X 0 n) ≫
      (boundedConstructibleNearbyCycles hN).map
        ((Functor.Monoidal.μIso (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := Y) f) A
          (boundedConstructibleTateTwist ℓ X 0 n)).symm ≪≫
          whiskerLeftIso _ (boundedConstructibleTateTwistZeroUpperStarIso ℓ (X := X) (Y := Y) f
            n)).hom ≫
      (N.zeroTwistIso hN qN n ((boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := Y) f).obj
        A)).hom :=
  twistIso_exchange (boundedConstructibleTensorMap hM) (boundedConstructibleTensorMap hN)
    (fun x y ↦ boundedConstructibleTensorMap_natural hN x y) β
    (liftExchange_upperStarOfMap_tensor hN hM (φ.pullbackExchange _)
      (φ.map_tensorMap_comp_pullbackExchange_app _) β hβ)
    (M.zeroTwistSpecializationMap hM n) (N.zeroTwistSpecializationMap hN n)
    (boundedConstructibleTateTwistZeroUpperStarIso ℓ (X := X) (Y := Y) f n)
    (boundedConstructibleTateTwistZeroUpperStarIso ℓ (X := X') (Y := Y') f' n)
    (φ.liftExchange_zeroTwistSpecializationMap hM hN β hβ n) (M.zeroTwistIso hM qM n)
    (M.zeroTwistIso_inv hM qM n) (N.zeroTwistIso hN qN n) (N.zeroTwistIso_inv hN qN n) A

end BoundedConstructibleTwist

section Geometry

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K] (x : K)
  {T Tc : Scheme.{u}} {t : T ⟶ Tc} {b : T ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  {bc : Tc ⟶ 𝔸(ULift.{u} (Fin 1); trait k')} (hbb : t ≫ bc = b)

/-- The map of total spaces `𝒳 ×_{𝔸¹_S} Spec K⟦t⟧ ⟶ 𝒳_c ×_{𝔸¹_S} Spec K⟦t⟧` of the slices along
a coordinate `b = t ≫ b_c`. -/
noncomputable abbrev sliceTotalMap : pullback b (traitSlice x) ⟶ pullback bc (traitSlice x) :=
  pullback.map b (traitSlice x) bc (traitSlice x) t (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, hbb]) (by rw [Category.comp_id, Category.id_comp])

@[reassoc (attr := simp)]
lemma sliceTotalMap_snd :
    sliceTotalMap x hbb ≫ pullback.snd bc (traitSlice x) = pullback.snd b (traitSlice x) := by
  simp

@[reassoc (attr := simp)]
lemma sliceTotalMap_fst :
    sliceTotalMap x hbb ≫ pullback.fst bc (traitSlice x) = pullback.fst b (traitSlice x) ≫ t := by
  simp

/-- The slice of an open sub-scheme is the open sub-scheme of the slice. -/
lemma isPullback_sliceTotalMap :
    IsPullback (sliceTotalMap x hbb) (pullback.fst _ _) (pullback.fst _ _) t := by
  refine IsPullback.of_right ?_ (sliceTotalMap_fst x hbb) (IsPullback.of_hasPullback bc _).flip
  rw [sliceTotalMap_snd, hbb]
  exact (IsPullback.of_hasPullback b _).flip

/-- The map of fibres `𝒳'' ×_{K⟦t⟧} E ⟶ 𝒳''_c ×_{K⟦t⟧} E` of the slices along `γ : E ⟶ Spec K⟦t⟧`.
-/
noncomputable abbrev sliceFibreMap {E : Scheme.{u}} (γ : E ⟶ trait K) :
    pullback (pullback.snd b (traitSlice x)) γ ⟶ pullback (pullback.snd bc (traitSlice x)) γ :=
  pullback.map _ γ _ γ (sliceTotalMap x hbb) (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, sliceTotalMap_snd]) (by rw [Category.comp_id, Category.id_comp])

/-- The fibres of the slice of an open sub-scheme are open in those of the slice. -/
lemma isPullback_sliceFibreMap {E : Scheme.{u}} (γ : E ⟶ trait K) :
    IsPullback (sliceFibreMap x hbb γ) (pullback.fst _ _) (pullback.fst _ _)
      (sliceTotalMap x hbb) := by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback _ γ).flip
  have : sliceFibreMap x hbb γ ≫ pullback.snd _ γ = pullback.snd _ γ := by simp
  rw [this, sliceTotalMap_snd]
  exact (IsPullback.of_hasPullback _ γ).flip

/-- The slice of an open sub-scheme is an open sub-scheme of the slice. -/
lemma isOpenImmersion_sliceTotalMap [IsOpenImmersion t] :
    IsOpenImmersion (sliceTotalMap x hbb) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_sliceTotalMap x hbb).flip
    inferInstance

/-- The fibres of the slice of an open sub-scheme are open sub-schemes. -/
lemma isOpenImmersion_sliceFibreMap [IsOpenImmersion t] {E : Scheme.{u}} (γ : E ⟶ trait K) :
    IsOpenImmersion (sliceFibreMap x hbb γ) :=
  have := isOpenImmersion_sliceTotalMap x hbb
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_sliceFibreMap x hbb γ).flip
    inferInstance

end Geometry

section Models

variable {F : Type u} [Field F] {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]
  (x : K) {X₁ Xc : Over (Spec (.of F))} {X' Xc' : Over (Spec (.of k'))}
  {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {Mc : NearbyCyclesModel Xc.left Xc'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {qc : Mc.total ⟶ trait k'} {gc : Mc.generic ⟶ Spec (.of (traitGenericField k'))}
  {j : X₁ ⟶ Xc} {j' : X' ⟶ Xc'} (φ : M.Hom Mc j.left j'.left)
  {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')} {bc : Mc.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)
  (hbc : bc ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = qc) (hbb : φ.total ≫ bc = b)

namespace Hom

/-- The map of special fibres of the slices of an open sub-model, over `Spec K`. -/
noncomputable def genericSliceSpecialMap :
    NearbyCyclesModel.baseChangeSpecial b (traitSlice x) ⟶
      NearbyCyclesModel.baseChangeSpecial bc (traitSlice x) :=
  Over.homMk (sliceFibreMap x hbb (traitClosedPoint K))
    (by simp [NearbyCyclesModel.baseChangeSpecial])

instance [IsOpenImmersion φ.total] : IsOpenImmersion (φ.genericSliceSpecialMap x hbb).left :=
  isOpenImmersion_sliceFibreMap x hbb _

/-- The map `X₂ ⟶ X₂,c` of the bases of the generic slices of an open sub-model, through the
identifications `𝒳''_η ≅ X₂` of the generic fibres of the slices. -/
noncomputable def genericSliceBaseMap : genericSliceBase x hb ⟶ genericSliceBase x hbc :=
  Over.homMk ((genericSliceFibreIso x hb).inv ≫ sliceFibreMap x hbb (traitGenericSpec K) ≫
    (genericSliceFibreIso x hbc).hom) (by
      rw [Category.assoc, Category.assoc, genericSliceFibreIso_hom_over, Iso.inv_comp_eq,
        genericSliceFibreIso_hom_over]
      simp)

instance [IsOpenImmersion φ.total] : IsOpenImmersion (φ.genericSliceBaseMap x hb hbc hbb).left := by
  have := isOpenImmersion_sliceFibreMap x hbb (traitGenericSpec K)
  change IsOpenImmersion (_ ≫ _ ≫ _)
  infer_instance

/-- The morphism of generic slice models induced by an open sub-model. -/
noncomputable def genericSliceOpenHom :
    (genericSliceModel x hb).Hom (genericSliceModel x hbc)
      (φ.genericSliceBaseMap x hb hbc hbb).left
      (φ.genericSliceSpecialMap x hbb).left where
  total := sliceTotalMap x hbb
  generic := sliceFibreMap x hbb (traitGenericPoint K)
  comm_j := by simp
  comm_i := by simp [genericSliceSpecialMap]
  comm_ε := by
    simp only [genericSliceModel_ε, genericSliceBaseMap, Over.homMk_left, Category.assoc,
      Iso.hom_inv_id_assoc]
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    apply pullback.hom_ext <;> simp

@[simp]
lemma genericSliceOpenHom_total :
    (φ.genericSliceOpenHom x hb hbc hbb).total = sliceTotalMap x hbb := rfl

@[simp]
lemma genericSliceOpenHom_generic :
    (φ.genericSliceOpenHom x hb hbc hbb).generic = sliceFibreMap x hbb (traitGenericPoint K) := rfl

instance [IsOpenImmersion φ.total] : IsOpenImmersion (φ.genericSliceOpenHom x hb hbc hbb).total :=
  isOpenImmersion_sliceTotalMap x hbb

/-- The square of generic fibres of the slices of an open sub-model is cartesian. -/
lemma isPullback_genericSliceOpenHom :
    IsPullback (φ.genericSliceOpenHom x hb hbc hbb).generic (genericSliceModel x hb).j
      (genericSliceModel x hbc).j (φ.genericSliceOpenHom x hb hbc hbb).total :=
  isPullback_sliceFibreMap x hbb _

/-- The structure map to the trait of the slice of an open sub-model is the restriction. -/
lemma genericSliceOpenHom_q :
    pullback.snd b (traitSlice x) =
      (φ.genericSliceOpenHom x hb hbc hbb).total ≫ pullback.snd bc (traitSlice x) := by
  simp

/-- The structure map of the generic fibre of the slice of an open sub-model is the
restriction. -/
lemma genericSliceOpenHom_g :
    pullback.snd (pullback.snd b (traitSlice x)) (traitGenericPoint K) =
      (φ.genericSliceOpenHom x hb hbc hbb).generic ≫ pullback.snd _ _ := by
  simp

variable {φ x hb hbc hbb} in
/-- The maps of geometric generic fibres of the slices are compatible with an open sub-model. -/
lemma baseChangeGenericMap_comp_generic (hM : M.IsTraitModelOver q g)
    (hMc : Mc.IsTraitModelOver qc gc) (hg : g = φ.generic ≫ gc) :
    baseChangeGenericMap hM b hb (traitSlice x) (traitSlice_over x) ≫ φ.generic =
      (φ.genericSliceOpenHom x hb hbc hbb).generic ≫
        baseChangeGenericMap hMc bc hbc (traitSlice x) (traitSlice_over x) := by
  refine hMc.isPullback_j.hom_ext ?_ ?_
  · simp [φ.comm_j]
  · simp [← hg]

end Hom

variable {φ x hb hbc hbb}

/-- The map of bases of the generic slice of an open sub-model is the restriction of that of the
model: both satisfy the defining property of the map of bases, and the identification `ε` of the
slice model is an epimorphism. -/
lemma IsTraitModelOfGenericBase.genericSliceBaseMap_comp_openSubmodel
    (h : M.IsTraitModelOfGenericBase X₁ ι q g) (hc : Mc.IsTraitModelOfGenericBase Xc ι qc gc)
    (hg : g = φ.generic ≫ gc) :
    h.genericSliceBaseMap x hb ≫ j.left =
      (φ.genericSliceBaseMap x hb hbc hbb).left ≫ hc.genericSliceBaseMap x hbc := by
  have := h.epi_genericSliceModel_ε x hb
  refine (cancel_epi (genericSliceModel x hb).ε).1 ?_
  rw [reassoc_of% (h.genericSliceModel_ε_comp_genericSliceBaseMap x hb),
    ← φ.comm_ε, ← reassoc_of% (φ.genericSliceOpenHom x hb hbc hbb).comm_ε,
    hc.genericSliceModel_ε_comp_genericSliceBaseMap x hbc,
    reassoc_of% (Hom.baseChangeGenericMap_comp_generic h.isTraitModelOver hc.isTraitModelOver hg)]

/-- The map of special fibres of the slice of an open sub-model is the restriction of that of the
model. -/
lemma sliceSpecialMap_comp_openSubmodel (hM : M.IsTraitModelOver q g)
    (hMc : Mc.IsTraitModelOver qc gc) :
    sliceSpecialMap x hM hb ≫ j'.left =
      (φ.genericSliceSpecialMap x hbb).left ≫ sliceSpecialMap x hMc hbc := by
  refine hMc.isPullback_i.hom_ext ?_ ?_
  · simp [sliceSpecialMap, φ.comm_i, Hom.genericSliceSpecialMap]
  · simp [sliceSpecialMap, Hom.genericSliceSpecialMap]


end Models

section Main

attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

variable {F : Type u} [Field F] {k' : Type u} [Field k'] {X₁ : Over (Spec (.of F))}
  {X' : Over (Spec (.of k'))} {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [Fact (ringChar (traitSliceField k')).Prime] [Fact (ringChar (traitSliceField k') ≠ ℓ)]
  [Fact (ringChar (FractionRing (PowerSeries (traitSliceField k')))).Prime]
  [Fact (ringChar (FractionRing (PowerSeries (traitSliceField k'))) ≠ ℓ)]
  (h : M.IsTraitModelOfGenericBase X₁ ι q g) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)
  [LocallyOfFiniteType (genericSliceBase (traitSliceCoord k') hb).hom]
  [QuasiCompact (genericSliceBase (traitSliceCoord k') hb).hom]
  [IsSeparated (genericSliceBase (traitSliceCoord k') hb).hom]
  [LocallyOfFiniteType (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [QuasiCompact (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [IsSeparated (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  {Xc : Over (Spec (.of F))} [LocallyOfFiniteType Xc.hom] [QuasiCompact Xc.hom]
  [IsSeparated Xc.hom] {Xc' : Over (Spec (.of k'))} [LocallyOfFiniteType Xc'.hom]
  [QuasiCompact Xc'.hom] [IsSeparated Xc'.hom] {Mc : NearbyCyclesModel Xc.left Xc'.left}
  {qc : Mc.total ⟶ trait k'} {gc : Mc.generic ⟶ Spec (.of (traitGenericField k'))}
  (hc : Mc.IsTraitModelOfGenericBase Xc ι qc gc)
  {bc : Mc.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hbc : bc ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = qc)
  [LocallyOfFiniteType (genericSliceBase (traitSliceCoord k') hbc).hom]
  [QuasiCompact (genericSliceBase (traitSliceCoord k') hbc).hom]
  [IsSeparated (genericSliceBase (traitSliceCoord k') hbc).hom]
  [LocallyOfFiniteType (baseChangeSpecial bc (traitSlice (traitSliceCoord k'))).hom]
  [QuasiCompact (baseChangeSpecial bc (traitSlice (traitSliceCoord k'))).hom]
  [IsSeparated (baseChangeSpecial bc (traitSlice (traitSliceCoord k'))).hom]

namespace IsTraitModelOfGenericBase

/-- **The twist equation of the generic slice and open sub-models**: let `M` be an open sub-model
of a trait model `M_c` over the generic base, through open immersions `j : X₁ ⟶ X_c`,
`j' : X' ⟶ X'_c` and `φ : M ⟶ M_c` (as produced by
`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_isProper_openSubmodel`), and let the
coordinate `b` of `M` be the restriction `φ ≫ b_c` of a coordinate `b_c` of `M_c`. Then the twist
equation of `NearbyCyclesModel.IsTraitModelOfGenericBase.TwistEquation` for `M_c`
implies it for `M`.

The generic slice of `M` is the open sub-model of that of `M_c` over the open immersions
`X₂ ⟶ X₂,c` and `𝒳''_s ⟶ 𝒳''_{c,s}` (`NearbyCyclesModel.Hom.genericSliceOpenHom`); the
dualizing maps of `M` and of its slice are the restrictions of those of `M_c` and of its slice
(open restriction), the slice exchanges are compatible with the restrictions
(`NearbyCyclesModel.boundedConstructiblePullbackExchange_square`) and so are the twist
isomorphisms `κ` (`NearbyCyclesModel.Hom.liftExchange_zeroTwistIso`); the algebra is
`NearbyCyclesModel.exists_twist_of_openSubmodel`. -/
theorem exists_iso_map_θ_eq_twist_of_openSubmodel (D : NearbyDualizingDataOfGenericBase k' ℓ)
    (DK : NearbyDualizingDataOfGenericBase (traitSliceField k') ℓ) (j : X₁ ⟶ Xc)
    [IsOpenImmersion j.left] (j' : X' ⟶ Xc') [IsOpenImmersion j'.left]
    (φ : M.Hom Mc j.left j'.left) [IsOpenImmersion φ.total]
    (hφ : IsPullback φ.generic M.j Mc.j φ.total) (hq : q = φ.total ≫ qc)
    (hg : g = φ.generic ≫ gc) (hbb : φ.total ≫ bc = b)
    (H : ∃ (u : (genericSliceUpperStar (traitSliceCoord k') ℓ hc hbc).obj
          (dualizingComplex ℓ Xc) ≅
        dualizingComplex ℓ (genericSliceBase (traitSliceCoord k') hbc) ⊗
          boundedConstructibleTateTwist ℓ (genericSliceBase (traitSliceCoord k') hbc) 0 2)
      (v : (sliceSpecialUpperStar (traitSliceCoord k') ℓ hc hbc).obj (dualizingComplex ℓ Xc') ≅
        dualizingComplex ℓ (baseChangeSpecial bc (traitSlice (traitSliceCoord k'))) ⊗
          boundedConstructibleTateTwist ℓ
            (baseChangeSpecial bc (traitSlice (traitSliceCoord k'))) 0 2),
      (sliceSpecialUpperStar (traitSliceCoord k') ℓ hc hbc).map (D.θ hc) ≫ v.hom =
        (genericSliceExchange (traitSliceCoord k') ℓ hc hbc).app (dualizingComplex ℓ Xc) ≫
          (genericSliceNearbyCycles (traitSliceCoord k') ℓ hc hbc).map u.hom ≫
          (genericSliceTwistIso ℓ hc hbc _).hom ≫
          DK.θ (isTraitModelOfGenericBase_genericSliceModel (traitSliceCoord k') hbc
            hc.isTraitModelOver) ▷ _) :
    ∃ (u : (genericSliceUpperStar (traitSliceCoord k') ℓ h hb).obj (dualizingComplex ℓ X₁) ≅
        dualizingComplex ℓ (genericSliceBase (traitSliceCoord k') hb) ⊗
          boundedConstructibleTateTwist ℓ (genericSliceBase (traitSliceCoord k') hb) 0 2)
      (v : (sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb).obj (dualizingComplex ℓ X') ≅
        dualizingComplex ℓ (baseChangeSpecial b (traitSlice (traitSliceCoord k'))) ⊗
          boundedConstructibleTateTwist ℓ (baseChangeSpecial b (traitSlice (traitSliceCoord k')))
            0 2),
      (sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb).map (D.θ h) ≫ v.hom =
        (genericSliceExchange (traitSliceCoord k') ℓ h hb).app (dualizingComplex ℓ X₁) ≫
          (genericSliceNearbyCycles (traitSliceCoord k') ℓ h hb).map u.hom ≫
          (genericSliceTwistIso ℓ h hb _).hom ≫
          DK.θ (isTraitModelOfGenericBase_genericSliceModel (traitSliceCoord k') hb
            h.isTraitModelOver) ▷ _ := by
  have hM := h.isTraitModelOver
  have hMc := hc.isTraitModelOver
  have hs := sliceSpecialMap_comp_openSubmodel (x := traitSliceCoord k') (hb := hb) (hbc := hbc)
    (hbb := hbb) hM hMc
  have hb' := h.genericSliceBaseMap_comp_openSubmodel (x := traitSliceCoord k') (hb := hb)
    (hbc := hbc) (hbb := hbb) hc hg
  have hφ'' := Hom.isPullback_genericSliceOpenHom (traitSliceCoord k') φ hb hbc hbb
  have : IsIso (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ)) :=
    φ.isIso_pullbackExchange_of_isOpenImmersion _ hφ
  have : IsIso (φ.boundedConstructiblePullbackExchange ℓ
      (h.preservesBoundedConstructible (ℓ := ℓ)) (hc.preservesBoundedConstructible (ℓ := ℓ))) :=
    φ.isIso_boundedConstructiblePullbackExchange ℓ _ _
  have hres := D.map_θ_comp_dualizingComplexUpperStarIso hc h j j' φ hφ hq hg
  have hres₂ := DK.map_θ_comp_dualizingComplexUpperStarIso
    (isTraitModelOfGenericBase_genericSliceModel (traitSliceCoord k') hbc hMc)
    (isTraitModelOfGenericBase_genericSliceModel (traitSliceCoord k') hb hM)
    (φ.genericSliceBaseMap (traitSliceCoord k') hb hbc hbb)
    (φ.genericSliceSpecialMap (traitSliceCoord k') hbb)
    (φ.genericSliceOpenHom (traitSliceCoord k') hb hbc hbb) hφ''
    (Hom.genericSliceOpenHom_q _ _ _ _ _) (Hom.genericSliceOpenHom_g _ _ _ _ _)
  have hsq := boundedConstructiblePullbackExchange_square
    (h.genericSliceHom (traitSliceCoord k') hb) φ
    (φ.genericSliceOpenHom (traitSliceCoord k') hb hbc hbb)
    (hc.genericSliceHom (traitSliceCoord k') hbc) (by simp [genericSliceHom])
    (Hom.baseChangeGenericMap_comp_generic hM hMc hg) hb' hs
    (hc.preservesBoundedConstructible (ℓ := ℓ)) (h.preservesBoundedConstructible (ℓ := ℓ))
    ((isTraitModelOfGenericBase_genericSliceModel (traitSliceCoord k') hbc
      hMc).preservesBoundedConstructible (ℓ := ℓ))
    ((isTraitModelOfGenericBase_genericSliceModel (traitSliceCoord k') hb
      hM).preservesBoundedConstructible (ℓ := ℓ))
    (genericSliceExchange (traitSliceCoord k') ℓ h hb) rfl
    (genericSliceExchange (traitSliceCoord k') ℓ hc hbc) rfl (dualizingComplex ℓ Xc)
  have hκc := (φ.genericSliceOpenHom (traitSliceCoord k') hb hbc hbb).liftExchange_zeroTwistIso
    ((isTraitModelOfGenericBase_genericSliceModel (traitSliceCoord k') hbc
      hMc).preservesBoundedConstructible (ℓ := ℓ))
    ((isTraitModelOfGenericBase_genericSliceModel (traitSliceCoord k') hb
      hM).preservesBoundedConstructible (ℓ := ℓ))
    (pullback.snd bc (traitSlice (traitSliceCoord k')))
    (pullback.snd b (traitSlice (traitSliceCoord k')))
    ((φ.genericSliceOpenHom (traitSliceCoord k') hb hbc hbb).boundedConstructiblePullbackExchange ℓ
      ((isTraitModelOfGenericBase_genericSliceModel (traitSliceCoord k') hb
        hM).preservesBoundedConstructible (ℓ := ℓ))
      ((isTraitModelOfGenericBase_genericSliceModel (traitSliceCoord k') hbc
        hMc).preservesBoundedConstructible (ℓ := ℓ))) rfl 2
    (dualizingComplex ℓ (genericSliceBase (traitSliceCoord k') hbc))
  exact exists_twist_of_openSubmodel
    (J₂ := boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (φ.genericSliceBaseMap (traitSliceCoord k') hb hbc hbb))
    (J₂' := boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (φ.genericSliceSpecialMap (traitSliceCoord k') hbb))
    (D.θ hc) (D.θ h) _ _ _ _ _ hres _ _ _ hres₂ _ _
    (boundedConstructibleUpperStarSquareIso ℓ hs _) (boundedConstructibleUpperStarSquareIso ℓ hs _)
    (boundedConstructibleUpperStarSquareIso_hom_naturality ℓ hs (D.θ hc))
    (boundedConstructibleUpperStarSquareIso ℓ hb' _) (by transport_exact hsq)
    (fun Z ↦ (Functor.Monoidal.μIso (boundedConstructibleUpperStarOfMap ℓ
        (φ.genericSliceSpecialMap (traitSliceCoord k') hbb).left) Z _).symm ≪≫
      whiskerLeftIso _ (boundedConstructibleTateTwistZeroUpperStarIso ℓ
        (φ.genericSliceSpecialMap (traitSliceCoord k') hbb).left 2))
    (fun f ↦ μIso_symm_trans_whiskerLeftIso_hom_naturality _ _ f)
    ((Functor.Monoidal.μIso (boundedConstructibleUpperStarOfMap ℓ
        (φ.genericSliceBaseMap (traitSliceCoord k') hb hbc hbb).left) _ _).symm ≪≫
      whiskerLeftIso _ (boundedConstructibleTateTwistZeroUpperStarIso ℓ
        (φ.genericSliceBaseMap (traitSliceCoord k') hb hbc hbb).left 2))
    (genericSliceTwistIso ℓ hc hbc _) (genericSliceTwistIso ℓ h hb)
    (fun f ↦ zeroTwistIso_hom_naturality _ _ 2 f) (by transport_exact hκc) H

end IsTraitModelOfGenericBase

end Main

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing

