/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeCoherence
public import WeilConjectures.SixFunctors.NearbyCycles.Kunneth

/-!

# The Künneth map of nearby cycles and pullbacks

The Künneth map of nearby cycles `Π_{A,B} : Ψ_M A ⊠ Ψ_N B ⟶ Ψ_P (A ⊠ B)`
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.kunnethMap`) is compatible with the
pullback exchanges `α`: for morphisms of models `ρ_M : M' ⟶ M`, `ρ_N : N' ⟶ N`, `ρ_P : P' ⟶ P`
compatible with `φ₁ : P ⟶ M`, `φ₂ : P ⟶ N` and `φ₁' : P' ⟶ M'`, `φ₂' : P' ⟶ N'`, the square
```
Lρ_P'^* (Lf₁'^* Ψ_M A ⊗ Lf₂'^* Ψ_N B) --Lρ'^* Π--> Lρ_P'^* Ψ_P (A ⊠ B)
        | (α_{ρ_M} ⊗ α_{ρ_N}) ∘ m                     | m ∘ α_{ρ_P}
Le₁'^* Ψ_{M'} Lρ_M^* A ⊗ Le₂'^* Ψ_{N'} Lρ_N^* B --Π--> Ψ_{P'} (Lρ_M^* A ⊠ Lρ_N^* B)
```
commutes up to the tensor and pullback comparisons `m`
(`NearbyCyclesModel.map_kunnethMap_comp_pullbackExchange`). It follows from the square law of
the pullback exchanges (`NearbyCyclesModel.Hom.pullbackExchange_square`) and their monoidality
(`NearbyCyclesModel.Hom.map_tensorMap_comp_pullbackExchange_app`). In particular, when the
exchanges `α_ρ` are invertible (e.g. for open immersions,
`WeilConjectures.SixFunctors.NearbyCycles.OpenExchange`), `Lρ_P'^* Π_{A,B}` is invertible if and
only if `Π_{Lρ_M^* A, Lρ_N^* B}` is
(`NearbyCyclesModel.isIso_map_kunnethMap_iff_of_isKunnethRestriction`).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

/-! ### Abstract computation -/

section Abstract

variable {DX DY DZ DXU DYU DZU SX SY SZ SXU SYU SZU : Type*} [Category DX] [Category DY]
  [Category DZ] [Category DXU] [Category DYU] [Category DZU] [Category SX] [Category SY]
  [Category SZ] [Category SXU] [Category SYU] [Category SZU] [MonoidalCategory DZ]
  [MonoidalCategory DZU] [MonoidalCategory SZ] [MonoidalCategory SZU]
  {ΨM : DX ⥤ SX} {ΨN : DY ⥤ SY} {ΨP : DZ ⥤ SZ} {ΨMU : DXU ⥤ SXU} {ΨNU : DYU ⥤ SYU}
  {ΨPU : DZU ⥤ SZU} {f₁ : DX ⥤ DZ} {f₂ : DY ⥤ DZ} {f₁' : SX ⥤ SZ} {f₂' : SY ⥤ SZ}
  {e₁ : DXU ⥤ DZU} {e₂ : DYU ⥤ DZU} {e₁' : SXU ⥤ SZU} {e₂' : SYU ⥤ SZU}
  {ρM : DX ⥤ DXU} {ρN : DY ⥤ DYU} {ρP : DZ ⥤ DZU} {ρM' : SX ⥤ SXU} {ρN' : SY ⥤ SYU}
  {ρP' : SZ ⥤ SZU} [ρP.OplaxMonoidal] [ρP'.OplaxMonoidal]

/-- The compatibility of the Künneth maps with pullbacks, in abstract categories. -/
lemma map_kunnethMap_comp_pullbackExchange_aux
    (μP : ∀ U V, ΨP.obj U ⊗ ΨP.obj V ⟶ ΨP.obj (U ⊗ V))
    (μPU : ∀ U V, ΨPU.obj U ⊗ ΨPU.obj V ⟶ ΨPU.obj (U ⊗ V))
    (hμPU : ∀ {U U' V V' : DZU} (x : U ⟶ U') (y : V ⟶ V'),
      (ΨPU.map x ⊗ₘ ΨPU.map y) ≫ μPU U' V' = μPU U V ≫ ΨPU.map (x ⊗ₘ y))
    (αφ₁ : ΨM ⋙ f₁' ⟶ f₁ ⋙ ΨP) (αφ₂ : ΨN ⋙ f₂' ⟶ f₂ ⋙ ΨP)
    (αφ₁U : ΨMU ⋙ e₁' ⟶ e₁ ⋙ ΨPU) (αφ₂U : ΨNU ⋙ e₂' ⟶ e₂ ⋙ ΨPU)
    (αρM : ΨM ⋙ ρM' ⟶ ρM ⋙ ΨMU) (αρN : ΨN ⋙ ρN' ⟶ ρN ⋙ ΨNU) (αρP : ΨP ⋙ ρP' ⟶ ρP ⋙ ΨPU)
    (θ₁ : f₁ ⋙ ρP ⟶ ρM ⋙ e₁) (θ₂ : f₂ ⋙ ρP ⟶ ρN ⋙ e₂)
    (θ₁' : f₁' ⋙ ρP' ⟶ ρM' ⋙ e₁') (θ₂' : f₂' ⋙ ρP' ⟶ ρN' ⋙ e₂')
    (hSQ₁ : ∀ C, θ₁'.app (ΨM.obj C) ≫ e₁'.map (αρM.app C) ≫ αφ₁U.app (ρM.obj C) =
      ρP'.map (αφ₁.app C) ≫ αρP.app (f₁.obj C) ≫ ΨPU.map (θ₁.app C))
    (hSQ₂ : ∀ C, θ₂'.app (ΨN.obj C) ≫ e₂'.map (αρN.app C) ≫ αφ₂U.app (ρN.obj C) =
      ρP'.map (αφ₂.app C) ≫ αρP.app (f₂.obj C) ≫ ΨPU.map (θ₂.app C))
    (hαρP : ∀ U V, ρP'.map (μP U V) ≫ αρP.app (U ⊗ V) ≫
        ΨPU.map (Functor.OplaxMonoidal.δ ρP U V) =
      Functor.OplaxMonoidal.δ ρP' _ _ ≫ (αρP.app U ⊗ₘ αρP.app V) ≫ μPU (ρP.obj U) (ρP.obj V))
    (A : DX) (B : DY) :
    ρP'.map ((αφ₁.app A ⊗ₘ αφ₂.app B) ≫ μP _ _) ≫ αρP.app (f₁.obj A ⊗ f₂.obj B) ≫
        ΨPU.map (Functor.OplaxMonoidal.δ ρP _ _ ≫ (θ₁.app A ⊗ₘ θ₂.app B)) =
      Functor.OplaxMonoidal.δ ρP' _ _ ≫
        ((θ₁'.app (ΨM.obj A) ≫ e₁'.map (αρM.app A)) ⊗ₘ
          (θ₂'.app (ΨN.obj B) ≫ e₂'.map (αρN.app B))) ≫
        ((αφ₁U.app (ρM.obj A) ⊗ₘ αφ₂U.app (ρN.obj B)) ≫ μPU _ _) := by
  have h₁ := hSQ₁ A
  have h₂ := hSQ₂ B
  have hδ := Functor.OplaxMonoidal.δ_natural ρP' (αφ₁.app A) (αφ₂.app B)
  simp only [Functor.comp_obj] at h₁ h₂ hδ ⊢
  rw [Functor.map_comp, Category.assoc, ΨPU.map_comp, reassoc_of% (hαρP _ _),
    ← hμPU, ← reassoc_of% hδ]
  simp only [tensorHom_comp_tensorHom_assoc, Category.assoc, h₁, h₂]

end Abstract

/-! ### The compatibility -/

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' Y Y' Z Z' XU XU' YU YU' ZU ZU' : Scheme.{u}} {M : NearbyCyclesModel X X'}
  {N : NearbyCyclesModel Y Y'} {P : NearbyCyclesModel Z Z'} {MU : NearbyCyclesModel XU XU'}
  {NU : NearbyCyclesModel YU YU'} {PU : NearbyCyclesModel ZU ZU'}
  {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'} {e₁ : ZU ⟶ XU}
  {e₁' : ZU' ⟶ XU'} {e₂ : ZU ⟶ YU} {e₂' : ZU' ⟶ YU'} {r₁ : XU ⟶ X} {r₁' : XU' ⟶ X'}
  {r₂ : YU ⟶ Y} {r₂' : YU' ⟶ Y'} {r : ZU ⟶ Z} {r' : ZU' ⟶ Z'}

set_option maxHeartbeats 800000 in
-- the instantiation unfolds the Künneth maps of the two products
/-- **The Künneth map of nearby cycles and pullbacks**: for morphisms of models
`ρ_M : M' ⟶ M`, `ρ_N : N' ⟶ N`, `ρ_P : P' ⟶ P` with `φ₁' ≫ ρ_M = ρ_P ≫ φ₁` and
`φ₂' ≫ ρ_N = ρ_P ≫ φ₂`, the pullback of the Künneth map `Π_{A,B}` followed by the pullback
exchange `α_{ρ_P}` is, up to the tensor and pullback comparisons, the Künneth map
`Π_{Lρ_M^* A, Lρ_N^* B}` precomposed with the pullback exchanges `α_{ρ_M} ⊗ α_{ρ_N}`. -/
lemma map_kunnethMap_comp_pullbackExchange (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    (φ₁U : PU.Hom MU e₁ e₁') (φ₂U : PU.Hom NU e₂ e₂') (ρM : MU.Hom M r₁ r₁')
    (ρN : NU.Hom N r₂ r₂') (ρP : PU.Hom P r r')
    (htot₁ : φ₁U.total ≫ ρM.total = ρP.total ≫ φ₁.total)
    (hgen₁ : φ₁U.generic ≫ ρM.generic = ρP.generic ≫ φ₁.generic)
    (htot₂ : φ₂U.total ≫ ρN.total = ρP.total ≫ φ₂.total)
    (hgen₂ : φ₂U.generic ≫ ρN.generic = ρP.generic ≫ φ₂.generic)
    (hb₁ : e₁ ≫ r₁ = r ≫ f₁) (hs₁ : e₁' ≫ r₁' = r' ≫ f₁') (hb₂ : e₂ ≫ r₂ = r ≫ f₂)
    (hs₂ : e₂' ≫ r₂' = r' ≫ f₂')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    L((r')^*⟦Λ⟧).map (kunnethMap Λ φ₁ φ₂ A B) ≫
        (ρP.pullbackExchange Λ).app (L((f₁)^*⟦Λ⟧).obj A ⊗ L((f₂)^*⟦Λ⟧).obj B) ≫
        (PU.nearbyCycles Λ).map (Functor.OplaxMonoidal.δ L((r)^*⟦Λ⟧) _ _ ≫
          ((pullbackSquareComparison Λ (⟨hb₁⟩ : CommSq e₁ r r₁ f₁)).hom.app A ⊗ₘ
            (pullbackSquareComparison Λ (⟨hb₂⟩ : CommSq e₂ r r₂ f₂)).hom.app B)) =
      Functor.OplaxMonoidal.δ L((r')^*⟦Λ⟧) _ _ ≫
        (((pullbackSquareComparison Λ (⟨hs₁⟩ : CommSq e₁' r' r₁' f₁')).hom.app
            ((M.nearbyCycles Λ).obj A) ≫ L((e₁')^*⟦Λ⟧).map ((ρM.pullbackExchange Λ).app A)) ⊗ₘ
          ((pullbackSquareComparison Λ (⟨hs₂⟩ : CommSq e₂' r' r₂' f₂')).hom.app
            ((N.nearbyCycles Λ).obj B) ≫ L((e₂')^*⟦Λ⟧).map ((ρN.pullbackExchange Λ).app B))) ≫
        kunnethMap Λ φ₁U φ₂U (L((r₁)^*⟦Λ⟧).obj A) (L((r₂)^*⟦Λ⟧).obj B) := by
  have h := map_kunnethMap_comp_pullbackExchange_aux (P.tensorMap Λ) (PU.tensorMap Λ)
    (fun x y ↦ PU.tensorMap_natural Λ x y)
    (φ₁.pullbackExchange Λ) (φ₂.pullbackExchange Λ) (φ₁U.pullbackExchange Λ)
    (φ₂U.pullbackExchange Λ) (ρM.pullbackExchange Λ) (ρN.pullbackExchange Λ)
    (ρP.pullbackExchange Λ)
    (pullbackSquareComparison Λ (⟨hb₁⟩ : CommSq e₁ r r₁ f₁)).hom
    (pullbackSquareComparison Λ (⟨hb₂⟩ : CommSq e₂ r r₂ f₂)).hom
    (pullbackSquareComparison Λ (⟨hs₁⟩ : CommSq e₁' r' r₁' f₁')).hom
    (pullbackSquareComparison Λ (⟨hs₂⟩ : CommSq e₂' r' r₂' f₂')).hom
    (fun C ↦ Hom.pullbackExchange_square Λ φ₁U ρM ρP φ₁ htot₁ hgen₁ hb₁ hs₁ C)
    (fun C ↦ Hom.pullbackExchange_square Λ φ₂U ρN ρP φ₂ htot₂ hgen₂ hb₂ hs₂ C)
    (fun U V ↦ ρP.map_tensorMap_comp_pullbackExchange_app Λ U V) A B
  convert h using 3 <;> rfl

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
