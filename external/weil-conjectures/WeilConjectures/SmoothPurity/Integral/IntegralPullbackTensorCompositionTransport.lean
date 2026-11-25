/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.NatIso

/-! # Transport of a system composition law along fully faithful reductions

Source: Stacks 07A4 and 0941; the transport step of the reduced integral
pullback/tensor composition equation
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced).

Integral pullbacks and tensors are related to system pullbacks and tensors by
natural comparisons with a reduction functor. If the integral tensor comparisons
are the reductions of the system comparisons conjugated by these natural
comparisons, and the integral compositor reduces to the system compositor, then
the system composition law transports to the reduced integral composition law.
-/

@[expose] public section

open CategoryTheory

namespace WeilConjectures

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {CY : Type u₁} {CX : Type u₂} {CZ : Type u₃} {DY : Type u₄} {DX : Type u₅}
  {DZ : Type u₆} [Category.{v₁} CY] [Category.{v₂} CX] [Category.{v₃} CZ]
  [Category.{v₄} DY] [Category.{v₅} DX] [Category.{v₆} DZ]

/-- A functor applied to a map of the form `F.map φ` is conjugate, through a natural
comparison `F ⋙ R ≅ R' ⋙ P`, to `P` applied to the reduction of `φ`.
Source: naturality of the comparison
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced). -/
theorem map_map_eq_of_comparison {A B D D' : Type*} [Category A] [Category B]
    [Category D] [Category D'] {F : A ⥤ B} {R : B ⥤ D'} {R' : A ⥤ D} {P : D ⥤ D'}
    (β : F ⋙ R ≅ R' ⋙ P) {M N : A} (φ : M ⟶ N) :
    R.map (F.map φ) = β.hom.app M ≫ P.map (R'.map φ) ≫ β.inv.app N := by
  have h := β.hom.naturality φ
  dsimp only [Functor.comp_map] at h
  rw [← reassoc_of% h]
  simp

/-- Transport of the system composition law for pullback/tensor comparisons to the
reduction of the integral composition law.

The data are reductions `RW`, integral pullbacks `F`, system pullbacks `P`, integral
and system tensors `T` and `S`, comparisons `β` of pullbacks and `γ` of tensors with
reduction, system tensor comparisons `σ`, the system compositor `a`, the integral
compositor `c` and integral tensor comparisons `κ`.
Source: Stacks 07A4 and 0941
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced).
Proof: expand every reduced integral map through its natural comparison. Replace the
reduction of `c` using its compatibility with `a`, apply the system composition law,
and move `a`, `β_h` and `σ_h` across the remaining maps by naturality. The two tensor
comparisons `γ_X` cancel. -/
theorem reducedPullbackTensorComposition_of_systemLaw
    (RY : CY ⥤ DY) (RX : CX ⥤ DX) (RZ : CZ ⥤ DZ)
    (Ff : CY ⥤ CX) (Fh : CX ⥤ CZ) (Fhf : CY ⥤ CZ)
    (Pf : DY ⥤ DX) (Ph : DX ⥤ DZ) (Phf : DY ⥤ DZ)
    (TY : CY × CY ⥤ CY) (TX : CX × CX ⥤ CX) (TZ : CZ × CZ ⥤ CZ)
    (SY : DY × DY ⥤ DY) (SX : DX × DX ⥤ DX) (SZ : DZ × DZ ⥤ DZ)
    (βf : Ff ⋙ RX ≅ RY ⋙ Pf) (βh : Fh ⋙ RZ ≅ RX ⋙ Ph) (βhf : Fhf ⋙ RZ ≅ RY ⋙ Phf)
    (γY : TY ⋙ RY ≅ RY.prod RY ⋙ SY) (γX : TX ⋙ RX ≅ RX.prod RX ⋙ SX)
    (γZ : TZ ⋙ RZ ≅ RZ.prod RZ ⋙ SZ)
    (σf : SY ⋙ Pf ≅ Pf.prod Pf ⋙ SX) (σh : SX ⋙ Ph ≅ Ph.prod Ph ⋙ SZ)
    (σhf : SY ⋙ Phf ≅ Phf.prod Phf ⋙ SZ)
    (a : Phf ≅ Pf ⋙ Ph) (c : Fhf ≅ Ff ⋙ Fh)
    (hc : ∀ K : CY, RZ.map (c.hom.app K) ≫ βh.hom.app (Ff.obj K) ≫ Ph.map (βf.hom.app K) =
      βhf.hom.app K ≫ a.hom.app (RY.obj K))
    (κf : ∀ M N : CY, Ff.obj (TY.obj (M, N)) ≅ TX.obj (Ff.obj M, Ff.obj N))
    (κh : ∀ M N : CX, Fh.obj (TX.obj (M, N)) ≅ TZ.obj (Fh.obj M, Fh.obj N))
    (κhf : ∀ M N : CY, Fhf.obj (TY.obj (M, N)) ≅ TZ.obj (Fhf.obj M, Fhf.obj N))
    (hκf : ∀ M N : CY, RX.map (κf M N).hom =
      βf.hom.app (TY.obj (M, N)) ≫ Pf.map (γY.hom.app (M, N)) ≫
        σf.hom.app (RY.obj M, RY.obj N) ≫
        SX.map (Prod.mkHom (βf.inv.app M) (βf.inv.app N)) ≫ γX.inv.app (Ff.obj M, Ff.obj N))
    (hκh : ∀ M N : CX, RZ.map (κh M N).hom =
      βh.hom.app (TX.obj (M, N)) ≫ Ph.map (γX.hom.app (M, N)) ≫
        σh.hom.app (RX.obj M, RX.obj N) ≫
        SZ.map (Prod.mkHom (βh.inv.app M) (βh.inv.app N)) ≫ γZ.inv.app (Fh.obj M, Fh.obj N))
    (hκhf : ∀ M N : CY, RZ.map (κhf M N).hom =
      βhf.hom.app (TY.obj (M, N)) ≫ Phf.map (γY.hom.app (M, N)) ≫
        σhf.hom.app (RY.obj M, RY.obj N) ≫
        SZ.map (Prod.mkHom (βhf.inv.app M) (βhf.inv.app N)) ≫
        γZ.inv.app (Fhf.obj M, Fhf.obj N))
    (hσ : ∀ A B : DY, σhf.hom.app (A, B) ≫ SZ.map (Prod.mkHom (a.hom.app A) (a.hom.app B)) =
      a.hom.app (SY.obj (A, B)) ≫ Ph.map (σf.hom.app (A, B)) ≫
        σh.hom.app (Pf.obj A, Pf.obj B))
    (M N : CY) :
    RZ.map ((κhf M N).hom ≫ TZ.map (Prod.mkHom (c.hom.app M) (c.hom.app N))) =
      RZ.map (c.hom.app (TY.obj (M, N)) ≫ Fh.map (κf M N).hom ≫
        (κh (Ff.obj M) (Ff.obj N)).hom) := by
  have hcK (K : CY) : RZ.map (c.hom.app K) = βhf.hom.app K ≫ a.hom.app (RY.obj K) ≫
      Ph.map (βf.inv.app K) ≫ βh.inv.app (Ff.obj K) := by
    rw [← reassoc_of% (hc K)]
    simp only [Functor.comp_obj, ← Ph.map_comp_assoc, Iso.hom_inv_id_app,
      Functor.map_id, Category.id_comp, Iso.hom_inv_id_app, Category.comp_id]
  have hT := map_map_eq_of_comparison γZ (Prod.mkHom (c.hom.app M) (c.hom.app N))
  have hF := map_map_eq_of_comparison βh (κf M N).hom
  have ha := a.hom.naturality (γY.hom.app (M, N))
  have hs := σh.hom.naturality (Prod.mkHom (βf.inv.app M) (βf.inv.app N))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.comp_obj, Functor.prod_obj] at hT hF ha hs
  simp only [Functor.map_comp, hT, hF, hκhf, hκf, hκh, hcK, Category.assoc]
  have hS : SZ.map (Prod.mkHom (βhf.inv.app M) (βhf.inv.app N)) ≫
      SZ.map (Prod.mkHom
        (βhf.hom.app M ≫ a.hom.app (RY.obj M) ≫ Ph.map (βf.inv.app M) ≫ βh.inv.app (Ff.obj M))
        (βhf.hom.app N ≫ a.hom.app (RY.obj N) ≫ Ph.map (βf.inv.app N) ≫
          βh.inv.app (Ff.obj N))) =
      SZ.map (Prod.mkHom (a.hom.app (RY.obj M)) (a.hom.app (RY.obj N))) ≫
        SZ.map (Prod.mkHom (Ph.map (βf.inv.app M)) (Ph.map (βf.inv.app N))) ≫
        SZ.map (Prod.mkHom (βh.inv.app (Ff.obj M)) (βh.inv.app (Ff.obj N))) := by
    simp only [← SZ.map_comp, prod_comp, Iso.inv_hom_id_app_assoc]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% hS, reassoc_of% (hσ (RY.obj M) (RY.obj N)), ← reassoc_of% hs,
    reassoc_of% ha]
  simp only [← Ph.map_comp_assoc, Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc]
  erw [Category.comp_id]

/-- Reduction of a comparison obtained by conjugating a system comparison with total limits.
Let `μ : F ≅ R_Y ⋙ P' ⋙ L_X` and `t_W : T_W ≅ (R_W × R_W) ⋙ S_W ⋙ L_W` be realizations
through right adjoints `L_W` with counits `ε_W`, and let `σ` be a system comparison for `P'`.
The reduction of the composite comparison `κ` built from these data, with the counits
inverted at the system level, is the conjugate of `σ` (transported along `b : P' ≅ P`) by
the comparisons `β` and `γ` defined from `μ`, `t` and the counits.
Source: Stacks 0941 (blueprint: lem-pur-pullback-tensor-integral-composition-reduced).
Proof: by naturality of the counit, the reduction of a total limit `L_X(ψ)` is `ψ`
conjugated by counits; the counits then assemble with `μ` and `t` into `β` and `γ`. -/
theorem reduction_limitConjugate_eq {AY AX DY DX : Type*} [Category AY] [Category AX]
    [Category DY] [Category DX]
    (RY : AY ⥤ DY) (RX : AX ⥤ DX) (LY : DY ⥤ AY) (LX : DX ⥤ AX)
    (εY : LY ⋙ RY ⟶ 𝟭 DY) (εX : LX ⋙ RX ⟶ 𝟭 DX)
    (F : AY ⥤ AX) {P' P : DY ⥤ DX} (b : P' ≅ P)
    (TY : AY × AY ⥤ AY) (TX : AX × AX ⥤ AX) (SY : DY × DY ⥤ DY) (SX : DX × DX ⥤ DX)
    (μ : F ≅ RY ⋙ P' ⋙ LX)
    (tY : TY ≅ (RY.prod RY) ⋙ SY ⋙ LY) (tX : TX ≅ (RX.prod RX) ⋙ SX ⋙ LX)
    (σ : SY ⋙ P' ≅ (P'.prod P') ⋙ SX) (M N : AY)
    [IsIso (εY.app (SY.obj (RY.obj M, RY.obj N)))]
    [IsIso (εX.app (P'.obj (RY.obj M)))] [IsIso (εX.app (P'.obj (RY.obj N)))]
    [IsIso (εX.app (SX.obj (RX.obj (F.obj M), RX.obj (F.obj N))))]
    (βT : RX.obj (F.obj (TY.obj (M, N))) ≅ P.obj (RY.obj (TY.obj (M, N))))
    (hβT : βT.hom = RX.map (μ.hom.app (TY.obj (M, N)) ≫
      LX.map (b.hom.app (RY.obj (TY.obj (M, N))))) ≫ εX.app (P.obj (RY.obj (TY.obj (M, N)))))
    (βM : RX.obj (F.obj M) ≅ P.obj (RY.obj M))
    (hβM : βM.hom = RX.map (μ.hom.app M ≫ LX.map (b.hom.app (RY.obj M))) ≫
      εX.app (P.obj (RY.obj M)))
    (βN : RX.obj (F.obj N) ≅ P.obj (RY.obj N))
    (hβN : βN.hom = RX.map (μ.hom.app N ≫ LX.map (b.hom.app (RY.obj N))) ≫
      εX.app (P.obj (RY.obj N)))
    (γY : RY.obj (TY.obj (M, N)) ≅ SY.obj (RY.obj M, RY.obj N))
    (hγY : γY.hom = RY.map (tY.hom.app (M, N)) ≫ εY.app (SY.obj (RY.obj M, RY.obj N)))
    (γX : RX.obj (TX.obj (F.obj M, F.obj N)) ≅ SX.obj (RX.obj (F.obj M), RX.obj (F.obj N)))
    (hγX : γX.hom = RX.map (tX.hom.app (F.obj M, F.obj N)) ≫
      εX.app (SX.obj (RX.obj (F.obj M), RX.obj (F.obj N)))) :
    RX.map (μ.app (TY.obj (M, N)) ≪≫
        (RY ⋙ P' ⋙ LX).mapIso (tY.app (M, N)) ≪≫
        (LX.mapIso (P'.mapIso (asIso (εY.app (SY.obj (RY.obj M, RY.obj N))))) ≪≫
          LX.mapIso (σ.app (RY.obj M, RY.obj N)) ≪≫
          LX.mapIso (SX.mapIso (Iso.prod (asIso (εX.app (P'.obj (RY.obj M)))).symm
            (asIso (εX.app (P'.obj (RY.obj N)))).symm))) ≪≫
        ((RX.prod RX) ⋙ SX ⋙ LX).mapIso (Iso.prod (μ.app M).symm (μ.app N).symm) ≪≫
        (tX.app (F.obj M, F.obj N)).symm).hom =
      βT.hom ≫ P.map γY.hom ≫
        (b.inv.app (SY.obj (RY.obj M, RY.obj N)) ≫ σ.hom.app (RY.obj M, RY.obj N) ≫
          SX.map (Prod.mkHom (b.hom.app (RY.obj M)) (b.hom.app (RY.obj N)))) ≫
        SX.map (Prod.mkHom βM.inv βN.inv) ≫ γX.inv := by
  have hβ' (K : AY) (βK : RX.obj (F.obj K) ≅ P.obj (RY.obj K))
      (hβ : βK.hom = RX.map (μ.hom.app K ≫ LX.map (b.hom.app (RY.obj K))) ≫
        εX.app (P.obj (RY.obj K))) : RX.map (μ.hom.app K) ≫ εX.app (P'.obj (RY.obj K)) =
      βK.hom ≫ b.inv.app (RY.obj K) := by
    rw [hβ, Functor.map_comp, Category.assoc]
    have := εX.naturality (b.hom.app (RY.obj K))
    dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at this
    simp only [Category.assoc]
    rw [reassoc_of% this, Iso.hom_inv_id_app, Category.comp_id]
  have hβinv (K : AY) [IsIso (εX.app (P'.obj (RY.obj K)))]
      (βK : RX.obj (F.obj K) ≅ P.obj (RY.obj K))
      (hβ : βK.hom = RX.map (μ.hom.app K ≫ LX.map (b.hom.app (RY.obj K))) ≫
        εX.app (P.obj (RY.obj K))) :
      b.hom.app (RY.obj K) ≫ βK.inv =
        inv (εX.app (P'.obj (RY.obj K))) ≫ RX.map (μ.inv.app K) := by
    have := εX.naturality (b.hom.app (RY.obj K))
    dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at this
    rw [Iso.comp_inv_eq, hβ, RX.map_comp]
    calc b.hom.app (RY.obj K) = inv (εX.app (P'.obj (RY.obj K))) ≫
          εX.app (P'.obj (RY.obj K)) ≫ b.hom.app (RY.obj K) := by simp
      _ = inv (εX.app (P'.obj (RY.obj K))) ≫ RX.map (LX.map (b.hom.app (RY.obj K))) ≫
          εX.app (P.obj (RY.obj K)) := by rw [this]
      _ = inv (εX.app (P'.obj (RY.obj K))) ≫ RX.map (μ.inv.app K) ≫ RX.map (μ.hom.app K) ≫
          RX.map (LX.map (b.hom.app (RY.obj K))) ≫ εX.app (P.obj (RY.obj K)) := by
        rw [← RX.map_comp_assoc (μ.inv.app K) (μ.hom.app K), Iso.inv_hom_id_app, RX.map_id,
          Category.id_comp]
      _ = _ := by simp only [Category.assoc]
  have hγX' : inv (εX.app (SX.obj (RX.obj (F.obj M), RX.obj (F.obj N)))) ≫
      RX.map (tX.inv.app (F.obj M, F.obj N)) = γX.inv := by
    rw [← cancel_epi γX.hom, Iso.hom_inv_id, hγX, Category.assoc, IsIso.hom_inv_id_assoc,
      ← RX.map_comp, Iso.hom_inv_id_app, RX.map_id]
  let ψ : P'.obj (RY.obj (TY.obj (M, N))) ⟶ SX.obj (RX.obj (F.obj M), RX.obj (F.obj N)) :=
    P'.map (RY.map (tY.hom.app (M, N))) ≫ P'.map (εY.app (SY.obj (RY.obj M, RY.obj N))) ≫
      σ.hom.app (RY.obj M, RY.obj N) ≫
      SX.map (Prod.mkHom (inv (εX.app (P'.obj (RY.obj M))))
        (inv (εX.app (P'.obj (RY.obj N))))) ≫
      SX.map (Prod.mkHom (RX.map (μ.inv.app M)) (RX.map (μ.inv.app N)))
  have hL : RX.map (LX.map ψ) = εX.app _ ≫ ψ ≫
      inv (εX.app (SX.obj (RX.obj (F.obj M), RX.obj (F.obj N)))) := by
    have hn := εX.naturality ψ
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    rw [← reassoc_of% hn, IsIso.hom_inv_id, Category.comp_id]
  have hl : RX.map (μ.app (TY.obj (M, N)) ≪≫
        (RY ⋙ P' ⋙ LX).mapIso (tY.app (M, N)) ≪≫
        (LX.mapIso (P'.mapIso (asIso (εY.app (SY.obj (RY.obj M, RY.obj N))))) ≪≫
          LX.mapIso (σ.app (RY.obj M, RY.obj N)) ≪≫
          LX.mapIso (SX.mapIso (Iso.prod (asIso (εX.app (P'.obj (RY.obj M)))).symm
            (asIso (εX.app (P'.obj (RY.obj N)))).symm))) ≪≫
        ((RX.prod RX) ⋙ SX ⋙ LX).mapIso (Iso.prod (μ.app M).symm (μ.app N).symm) ≪≫
        (tX.app (F.obj M, F.obj N)).symm).hom =
      RX.map (μ.hom.app (TY.obj (M, N))) ≫ RX.map (LX.map ψ) ≫
        RX.map (tX.inv.app (F.obj M, F.obj N)) := by
    simp [ψ]
  have hb := b.inv.naturality (RY.map (tY.hom.app (M, N)) ≫ εY.app (SY.obj (RY.obj M, RY.obj N)))
  have hS : SX.map (Prod.mkHom (b.hom.app (RY.obj M)) (b.hom.app (RY.obj N))) ≫
      SX.map (Prod.mkHom βM.inv βN.inv) =
      SX.map (Prod.mkHom (inv (εX.app (P'.obj (RY.obj M))))
        (inv (εX.app (P'.obj (RY.obj N))))) ≫
      SX.map (Prod.mkHom (RX.map (μ.inv.app M)) (RX.map (μ.inv.app N))) := by
    simp only [← SX.map_comp, prod_comp, hβinv M βM hβM, hβinv N βN hβN]
  rw [hl, hL]
  simp only [Category.assoc]
  rw [reassoc_of% (hβ' (TY.obj (M, N)) βT hβT), hγX', hγY, reassoc_of% hS, reassoc_of% hb]
  simp only [ψ, Functor.map_comp, Category.assoc]

end WeilConjectures
