/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeCoherence
public import WeilConjectures.SixFunctors.NearbyCycles.Kunneth

/-!

# The Künneth map of nearby cycles and direct images

The Künneth map of nearby cycles `Π_{A,B} : Ψ_M A ⊠ Ψ_N B ⟶ Ψ_P (A ⊠ B)`
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.kunnethMap`) is compatible with
direct images (blueprint `lemma-kunneth-map-proper-direct-image--1`): for morphisms of models
`M ⟶ M₁` over `g`, `N ⟶ N₁` over `h` and `P ⟶ P₁` over `k`, compatible with the morphisms `P ⟶ M, N`
and `P₁ ⟶ M₁, N₁`, the square
```
Ψ_{M₁} Rg_* A ⊠ Ψ_{N₁} Rh_* B --Π--> Ψ_{P₁} (Rg_* A ⊠ Rh_* B) --Ψ(κ)--> Ψ_{P₁} Rk_* (A ⊠ B)
        |χ ⊠ χ                                                               |χ
Rg'_* Ψ_M A ⊠ Rh'_* Ψ_N B --κ--> Rk'_* (Ψ_M A ⊠ Ψ_N B) --Rk'_* Π--> Rk'_* Ψ_P (A ⊠ B)
```
commutes, where `κ` are the ordinary Künneth maps
(`AlgebraicGeometry.ProEtale.CondensedRing.lowerStarKunnethMap'`) and `χ` the pushforward
exchanges (`NearbyCyclesModel.pushforwardExchange`)
(`NearbyCyclesModel.kunnethMap_comp_pushforwardExchange`). For proper `g`, `h`, `k` the maps `χ`
are the proper exchange isomorphisms, and the square identifies `R(g × h)_* Π_{A,B}` with
`Π_{Rg_* A, Rh_* B}`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Abstract computation -/

section Abstract

variable {DX DY DZ DX1 DY1 DZ1 SX SY SZ SX1 SY1 SZ1 : Type*} [Category DX] [Category DY]
  [Category DZ] [Category DX1] [Category DY1] [Category DZ1] [Category SX] [Category SY]
  [Category SZ] [Category SX1] [Category SY1] [Category SZ1] [MonoidalCategory DZ]
  [MonoidalCategory DZ1] [MonoidalCategory SZ] [MonoidalCategory SZ1]
  {ΨM : DX ⥤ SX} {ΨN : DY ⥤ SY} {ΨP : DZ ⥤ SZ} {ΨM1 : DX1 ⥤ SX1} {ΨN1 : DY1 ⥤ SY1}
  {ΨP1 : DZ1 ⥤ SZ1}
  {f₁ : DX ⥤ DZ} {f₂ : DY ⥤ DZ} {e₁ : DX1 ⥤ DZ1} {e₂ : DY1 ⥤ DZ1} {g : DX1 ⥤ DX}
  {h : DY1 ⥤ DY} {k : DZ1 ⥤ DZ}
  {f₁' : SX ⥤ SZ} {f₂' : SY ⥤ SZ} {e₁' : SX1 ⥤ SZ1} {e₂' : SY1 ⥤ SZ1} {g' : SX1 ⥤ SX}
  {h' : SY1 ⥤ SY} {k' : SZ1 ⥤ SZ}
  {Rg : DX ⥤ DX1} {Rh : DY ⥤ DY1} {Rk : DZ ⥤ DZ1} {Rg' : SX ⥤ SX1} {Rh' : SY ⥤ SY1}
  {Rk' : SZ ⥤ SZ1} [k.OplaxMonoidal] [k'.OplaxMonoidal]

/-- The compatibility of the Künneth maps with direct images, in abstract categories: both sides
have the same adjoint for `k'^* ⊣ Rk'_*`, by the square law of the pullback exchanges `α` and the
monoidality of `α_{ψ_P}`. -/
lemma kunnethMap_comp_pushforwardExchange_aux (ag : g ⊣ Rg) (ah : h ⊣ Rh) (ak : k ⊣ Rk)
    (ag' : g' ⊣ Rg') (ah' : h' ⊣ Rh') (ak' : k' ⊣ Rk')
    (μP : ∀ U V, ΨP.obj U ⊗ ΨP.obj V ⟶ ΨP.obj (U ⊗ V))
    (μP1 : ∀ U V, ΨP1.obj U ⊗ ΨP1.obj V ⟶ ΨP1.obj (U ⊗ V))
    (hμP : ∀ {U U' V V' : DZ} (x : U ⟶ U') (y : V ⟶ V'),
      (ΨP.map x ⊗ₘ ΨP.map y) ≫ μP U' V' = μP U V ≫ ΨP.map (x ⊗ₘ y))
    (αφ₁ : ΨM ⋙ f₁' ⟶ f₁ ⋙ ΨP) (αφ₂ : ΨN ⋙ f₂' ⟶ f₂ ⋙ ΨP)
    (αφ₁' : ΨM1 ⋙ e₁' ⟶ e₁ ⋙ ΨP1) (αφ₂' : ΨN1 ⋙ e₂' ⟶ e₂ ⋙ ΨP1)
    (αψM : ΨM1 ⋙ g' ⟶ g ⋙ ΨM) (αψN : ΨN1 ⋙ h' ⟶ h ⋙ ΨN) (αψP : ΨP1 ⋙ k' ⟶ k ⋙ ΨP)
    (χψM : Rg ⋙ ΨM1 ⟶ ΨM ⋙ Rg') (χψN : Rh ⋙ ΨN1 ⟶ ΨN ⋙ Rh') (χψP : Rk ⋙ ΨP1 ⟶ ΨP ⋙ Rk')
    (hχψM : ∀ A, g'.map (χψM.app A) ≫ ag'.counit.app (ΨM.obj A) =
      αψM.app (Rg.obj A) ≫ ΨM.map (ag.counit.app A))
    (hχψN : ∀ B, h'.map (χψN.app B) ≫ ah'.counit.app (ΨN.obj B) =
      αψN.app (Rh.obj B) ≫ ΨN.map (ah.counit.app B))
    (hχψP : ∀ V, k'.map (χψP.app V) ≫ ak'.counit.app (ΨP.obj V) =
      αψP.app (Rk.obj V) ≫ ΨP.map (ak.counit.app V))
    (θ₁ : e₁ ⋙ k ⟶ g ⋙ f₁) (θ₂ : e₂ ⋙ k ⟶ h ⋙ f₂) (θ₁' : e₁' ⋙ k' ⟶ g' ⋙ f₁')
    (θ₂' : e₂' ⋙ k' ⟶ h' ⋙ f₂')
    (bc₁ : Rg ⋙ e₁ ⟶ f₁ ⋙ Rk) (bc₂ : Rh ⋙ e₂ ⟶ f₂ ⋙ Rk) (bc₁' : Rg' ⋙ e₁' ⟶ f₁' ⋙ Rk')
    (bc₂' : Rh' ⋙ e₂' ⟶ f₂' ⋙ Rk')
    (hbc₁ : ∀ A, k.map (bc₁.app A) ≫ ak.counit.app (f₁.obj A) =
      θ₁.app (Rg.obj A) ≫ f₁.map (ag.counit.app A))
    (hbc₂ : ∀ B, k.map (bc₂.app B) ≫ ak.counit.app (f₂.obj B) =
      θ₂.app (Rh.obj B) ≫ f₂.map (ah.counit.app B))
    (hbc₁' : ∀ C, k'.map (bc₁'.app C) ≫ ak'.counit.app (f₁'.obj C) =
      θ₁'.app (Rg'.obj C) ≫ f₁'.map (ag'.counit.app C))
    (hbc₂' : ∀ D, k'.map (bc₂'.app D) ≫ ak'.counit.app (f₂'.obj D) =
      θ₂'.app (Rh'.obj D) ≫ f₂'.map (ah'.counit.app D))
    (μk : ∀ U V, Rk.obj U ⊗ Rk.obj V ⟶ Rk.obj (U ⊗ V))
    (μk' : ∀ U V, Rk'.obj U ⊗ Rk'.obj V ⟶ Rk'.obj (U ⊗ V))
    (hμk : ∀ U V, k.map (μk U V) ≫ ak.counit.app (U ⊗ V) =
      Functor.OplaxMonoidal.δ k _ _ ≫ (ak.counit.app U ⊗ₘ ak.counit.app V))
    (hμk' : ∀ U V, k'.map (μk' U V) ≫ ak'.counit.app (U ⊗ V) =
      Functor.OplaxMonoidal.δ k' _ _ ≫ (ak'.counit.app U ⊗ₘ ak'.counit.app V))
    (hSQ₁ : ∀ C, θ₁'.app (ΨM1.obj C) ≫ f₁'.map (αψM.app C) ≫ αφ₁.app (g.obj C) =
      k'.map (αφ₁'.app C) ≫ αψP.app (e₁.obj C) ≫ ΨP.map (θ₁.app C))
    (hSQ₂ : ∀ C, θ₂'.app (ΨN1.obj C) ≫ f₂'.map (αψN.app C) ≫ αφ₂.app (h.obj C) =
      k'.map (αφ₂'.app C) ≫ αψP.app (e₂.obj C) ≫ ΨP.map (θ₂.app C))
    (hαψP : ∀ U V, k'.map (μP1 U V) ≫ αψP.app (U ⊗ V) ≫ ΨP.map (Functor.OplaxMonoidal.δ k U V) =
      Functor.OplaxMonoidal.δ k' _ _ ≫ (αψP.app U ⊗ₘ αψP.app V) ≫ μP (k.obj U) (k.obj V))
    (A : DX) (B : DY) :
    (e₁'.map (χψM.app A) ⊗ₘ e₂'.map (χψN.app B)) ≫
        ((bc₁'.app (ΨM.obj A) ⊗ₘ bc₂'.app (ΨN.obj B)) ≫ μk' _ _) ≫
        Rk'.map ((αφ₁.app A ⊗ₘ αφ₂.app B) ≫ μP _ _) =
      ((αφ₁'.app (Rg.obj A) ⊗ₘ αφ₂'.app (Rh.obj B)) ≫ μP1 _ _) ≫
        ΨP1.map ((bc₁.app A ⊗ₘ bc₂.app B) ≫ μk _ _) ≫ χψP.app _ := by
  have hL₁ : k'.map (e₁'.map (χψM.app A)) ≫ k'.map (bc₁'.app (ΨM.obj A)) ≫
      ak'.counit.app _ ≫ αφ₁.app A = k'.map (αφ₁'.app (Rg.obj A)) ≫ αψP.app _ ≫
        ΨP.map (θ₁.app _ ≫ f₁.map (ag.counit.app A)) := by
    have n₁ := θ₁'.naturality (χψM.app A)
    have n₂ := αφ₁.naturality (ag.counit.app A)
    simp only [Functor.comp_obj, Functor.comp_map] at n₁ n₂
    rw [reassoc_of% (hbc₁' (ΨM.obj A)), reassoc_of% n₁, ← f₁'.map_comp_assoc, hχψM,
      f₁'.map_comp_assoc]
    erw [n₂]
    rw [reassoc_of% (hSQ₁ (Rg.obj A)), ΨP.map_comp]
  have hL₂ : k'.map (e₂'.map (χψN.app B)) ≫ k'.map (bc₂'.app (ΨN.obj B)) ≫
      ak'.counit.app _ ≫ αφ₂.app B = k'.map (αφ₂'.app (Rh.obj B)) ≫ αψP.app _ ≫
        ΨP.map (θ₂.app _ ≫ f₂.map (ah.counit.app B)) := by
    have n₁ := θ₂'.naturality (χψN.app B)
    have n₂ := αφ₂.naturality (ah.counit.app B)
    simp only [Functor.comp_obj, Functor.comp_map] at n₁ n₂
    rw [reassoc_of% (hbc₂' (ΨN.obj B)), reassoc_of% n₁, ← f₂'.map_comp_assoc, hχψN,
      f₂'.map_comp_assoc]
    erw [n₂]
    rw [reassoc_of% (hSQ₂ (Rh.obj B)), ΨP.map_comp]
  have hR : k.map ((bc₁.app A ⊗ₘ bc₂.app B) ≫ μk _ _) ≫ ak.counit.app _ =
      Functor.OplaxMonoidal.δ k _ _ ≫ ((θ₁.app _ ≫ f₁.map (ag.counit.app A)) ⊗ₘ
        (θ₂.app _ ≫ f₂.map (ah.counit.app B))) := by
    rw [k.map_comp, Category.assoc, hμk]
    erw [← Functor.OplaxMonoidal.δ_natural_assoc]
    rw [tensorHom_comp_tensorHom, hbc₁, hbc₂]
    rfl
  have nR := αψP.naturality ((bc₁.app A ⊗ₘ bc₂.app B) ≫ μk _ _)
  have nL := ak'.counit.naturality ((αφ₁.app A ⊗ₘ αφ₂.app B) ≫ μP _ _)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at nR nL
  apply (ak'.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  conv_lhs =>
    rw [k'.map_comp, k'.map_comp, Category.assoc, Category.assoc, nL, k'.map_comp,
      Category.assoc, reassoc_of% (hμk' _ _)]
  conv_rhs =>
    rw [k'.map_comp, k'.map_comp, k'.map_comp, Category.assoc, Category.assoc,
      Category.assoc, hχψP, reassoc_of% nR, ← ΨP.map_comp, hR, ΨP.map_comp,
      reassoc_of% (hαψP _ _), ← hμP]
  erw [← Functor.OplaxMonoidal.δ_natural_assoc, ← Functor.OplaxMonoidal.δ_natural_assoc,
    ← Functor.OplaxMonoidal.δ_natural_assoc]
  simp only [tensorHom_comp_tensorHom_assoc]
  rw [hL₁, hL₂]
  rfl

end Abstract

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

namespace NearbyCyclesModel

variable {X X' Y Y' Z Z' X₁ X₁' Y₁ Y₁' Z₁ Z₁' : Scheme.{u}} {M : NearbyCyclesModel X X'}
  {N : NearbyCyclesModel Y Y'} {P : NearbyCyclesModel Z Z'} {M₁ : NearbyCyclesModel X₁ X₁'}
  {N₁ : NearbyCyclesModel Y₁ Y₁'} {P₁ : NearbyCyclesModel Z₁ Z₁'}
  {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'} {e₁ : Z₁ ⟶ X₁} {e₁' : Z₁' ⟶ X₁'}
  {e₂ : Z₁ ⟶ Y₁} {e₂' : Z₁' ⟶ Y₁'} {g : X ⟶ X₁} {g' : X' ⟶ X₁'} {h : Y ⟶ Y₁} {h' : Y' ⟶ Y₁'}
  {k : Z ⟶ Z₁} {k' : Z' ⟶ Z₁'}

/-- **The Künneth map of nearby cycles and direct images** (blueprint
`lemma-kunneth-map-proper-direct-image--1`): for morphisms of models `ψ_M : M ⟶ M₁`, `ψ_N : N ⟶ N₁`,
`ψ_P : P ⟶ P₁` compatible with `φ₁ : P ⟶ M`, `φ₂ : P ⟶ N`, `φ₁' : P₁ ⟶ M₁`, `φ₂' : P₁ ⟶ N₁`, the
Künneth maps `Π` of nearby cycles, the ordinary Künneth maps `κ` and the pushforward exchanges `χ`
form a commutative square `Rk'_* Π_{A,B} ∘ κ ∘ (χ ⊠ χ) = χ ∘ Ψ_{P₁}(κ) ∘ Π_{Rg_* A, Rh_* B}`. For
proper morphisms the exchanges `χ` are the proper exchange isomorphisms, and this identifies
`R(g × h)_* Π_{A,B}` with `Π_{Rg_* A, Rh_* B}`. -/
lemma kunnethMap_comp_pushforwardExchange (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    (φ₁' : P₁.Hom M₁ e₁ e₁') (φ₂' : P₁.Hom N₁ e₂ e₂') (ψM : M.Hom M₁ g g')
    (ψN : N.Hom N₁ h h') (ψP : P.Hom P₁ k k')
    (htot₁ : φ₁.total ≫ ψM.total = ψP.total ≫ φ₁'.total)
    (hgen₁ : φ₁.generic ≫ ψM.generic = ψP.generic ≫ φ₁'.generic)
    (htot₂ : φ₂.total ≫ ψN.total = ψP.total ≫ φ₂'.total)
    (hgen₂ : φ₂.generic ≫ ψN.generic = ψP.generic ≫ φ₂'.generic)
    (hb₁ : f₁ ≫ g = k ≫ e₁) (hs₁ : f₁' ≫ g' = k' ≫ e₁') (hb₂ : f₂ ≫ h = k ≫ e₂)
    (hs₂ : f₂' ≫ h' = k' ≫ e₂')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (L((e₁')^*⟦Λ⟧).map ((ψM.pushforwardExchange Λ).app A) ⊗ₘ
        L((e₂')^*⟦Λ⟧).map ((ψN.pushforwardExchange Λ).app B)) ≫
        lowerStarKunnethMap' Λ ⟨hs₁⟩ ⟨hs₂⟩ ((M.nearbyCycles Λ).obj A)
          ((N.nearbyCycles Λ).obj B) ≫
        R((k')_*⟦Λ⟧).map (kunnethMap Λ φ₁ φ₂ A B) =
      kunnethMap Λ φ₁' φ₂' (R((g)_*⟦Λ⟧).obj A) (R((h)_*⟦Λ⟧).obj B) ≫
        (P₁.nearbyCycles Λ).map (lowerStarKunnethMap' Λ ⟨hb₁⟩ ⟨hb₂⟩ A B) ≫
        (ψP.pushforwardExchange Λ).app _ := by
  have hμ : ∀ {U U' V V' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))} (x : U ⟶ U') (y : V ⟶ V'),
      ((P.nearbyCycles Λ).map x ⊗ₘ (P.nearbyCycles Λ).map y) ≫ P.tensorMap Λ U' V' =
        P.tensorMap Λ U V ≫ (P.nearbyCycles Λ).map (x ⊗ₘ y) :=
    fun x y ↦ P.tensorMap_natural Λ x y
  have h := kunnethMap_comp_pushforwardExchange_aux (derivedUpperStarLowerStarAdjunction Λ g)
    (derivedUpperStarLowerStarAdjunction Λ h) (derivedUpperStarLowerStarAdjunction Λ k)
    (derivedUpperStarLowerStarAdjunction Λ g') (derivedUpperStarLowerStarAdjunction Λ h')
    (derivedUpperStarLowerStarAdjunction Λ k') (P.tensorMap Λ) (P₁.tensorMap Λ) hμ
    (φ₁.pullbackExchange Λ) (φ₂.pullbackExchange Λ) (φ₁'.pullbackExchange Λ)
    (φ₂'.pullbackExchange Λ) (ψM.pullbackExchange Λ) (ψN.pullbackExchange Λ)
    (ψP.pullbackExchange Λ) (ψM.pushforwardExchange Λ) (ψN.pushforwardExchange Λ)
    (ψP.pushforwardExchange Λ) (ψM.map_pushforwardExchange_app_comp_counit_app Λ)
    (ψN.map_pushforwardExchange_app_comp_counit_app Λ)
    (ψP.map_pushforwardExchange_app_comp_counit_app Λ)
    (pullbackSquareComparison Λ ⟨hb₁⟩).hom (pullbackSquareComparison Λ ⟨hb₂⟩).hom
    (pullbackSquareComparison Λ ⟨hs₁⟩).hom (pullbackSquareComparison Λ ⟨hs₂⟩).hom
    (baseChangeMap Λ ⟨hb₁⟩) (baseChangeMap Λ ⟨hb₂⟩) (baseChangeMap Λ ⟨hs₁⟩)
    (baseChangeMap Λ ⟨hs₂⟩)
    (Adjunction.exchangeRight_app_comp_counit' _ _ _ _ rfl)
    (Adjunction.exchangeRight_app_comp_counit' _ _ _ _ rfl)
    (Adjunction.exchangeRight_app_comp_counit' _ _ _ _ rfl)
    (Adjunction.exchangeRight_app_comp_counit' _ _ _ _ rfl)
    (lowerStarTensorMap' Λ k) (lowerStarTensorMap' Λ k')
    (fun U V ↦ lowerStarTensorMap'_comp_counit Λ k U V)
    (fun U V ↦ lowerStarTensorMap'_comp_counit Λ k' U V)
    (fun C ↦ Hom.pullbackExchange_square Λ φ₁ ψM ψP φ₁' htot₁ hgen₁ hb₁ hs₁ C)
    (fun C ↦ Hom.pullbackExchange_square Λ φ₂ ψN ψP φ₂' htot₂ hgen₂ hb₂ hs₂ C)
    (fun U V ↦ ψP.map_tensorMap_comp_pullbackExchange_app Λ U V) A B
  convert h using 3 <;> rfl

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
