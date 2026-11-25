/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeCoherence

/-!

# The square law of the pushforward exchanges

For a commutative square of morphisms of models `φ₀ : P ⟶ M`, `ψ : M ⟶ M₁`, `ψ' : P ⟶ P₁`,
`φ₁ : P₁ ⟶ M₁`, the pullback exchanges of `φ₀`, `φ₁` and the pushforward exchanges of `ψ`, `ψ'`
satisfy the square law (`NearbyCyclesModel.pushforwardExchange_square_aux`, in abstract
categories)
```
e'^*(χ_ψ) ∘ bc' ∘ Rk'_*(α_{φ₀}) = α_{φ₁}(Rg_*) ∘ Ψ_{P₁}(bc) ∘ χ_{ψ'}(f₀^*),
```
where `bc`, `bc'` are the base change morphisms of the squares of bases and of special fibres.
Consequently `Rk'_*` of the pullback exchange of `φ₀` is invertible at `A` as soon as the other
five maps are invertible at the relevant objects
(`NearbyCyclesModel.Hom.isIso_map_pullbackExchange_app_of_square`), and the pullback exchange
itself is invertible if moreover `Rk'_*` reflects isomorphisms
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_square`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

section Abstract

variable {DX DX1 DZ DZ1 SX SX1 SZ SZ1 : Type*} [Category DX] [Category DX1] [Category DZ]
  [Category DZ1] [Category SX] [Category SX1] [Category SZ] [Category SZ1]
  {ΨM : DX ⥤ SX} {ΨM1 : DX1 ⥤ SX1} {ΨP : DZ ⥤ SZ} {ΨP1 : DZ1 ⥤ SZ1}
  {f : DX ⥤ DZ} {e : DX1 ⥤ DZ1} {g : DX1 ⥤ DX} {k : DZ1 ⥤ DZ}
  {f' : SX ⥤ SZ} {e' : SX1 ⥤ SZ1} {g' : SX1 ⥤ SX} {k' : SZ1 ⥤ SZ}
  {Rg : DX ⥤ DX1} {Rk : DZ ⥤ DZ1} {Rg' : SX ⥤ SX1} {Rk' : SZ ⥤ SZ1}

/-- **The square law of the pushforward exchanges**, in abstract categories: for a commutative
square of morphisms of models `φ : P ⟶ M`, `ψ_M : M ⟶ M₁`, `ψ_P : P ⟶ P₁`, `φ' : P₁ ⟶ M₁`
(pullback exchanges `α`, pushforward exchanges `χ` the mates of `α`), with the base change
morphisms `bc`, `bc'` of the squares of bases and of special fibres,
`Rk'_*(α_φ) ∘ bc' ∘ e'^*(χ_{ψ_M}) = χ_{ψ_P} ∘ Ψ_{P₁}(bc) ∘ α_{φ'}`. Both sides have the same
adjoint for `k'^* ⊣ Rk'_*`, by the square law of the pullback exchanges. -/
lemma pushforwardExchange_square_aux (ag : g ⊣ Rg) (ak : k ⊣ Rk) (ag' : g' ⊣ Rg')
    (ak' : k' ⊣ Rk') (αφ : ΨM ⋙ f' ⟶ f ⋙ ΨP) (αφ' : ΨM1 ⋙ e' ⟶ e ⋙ ΨP1)
    (αψM : ΨM1 ⋙ g' ⟶ g ⋙ ΨM) (αψP : ΨP1 ⋙ k' ⟶ k ⋙ ΨP)
    (χψM : Rg ⋙ ΨM1 ⟶ ΨM ⋙ Rg') (χψP : Rk ⋙ ΨP1 ⟶ ΨP ⋙ Rk')
    (hχψM : ∀ A, g'.map (χψM.app A) ≫ ag'.counit.app (ΨM.obj A) =
      αψM.app (Rg.obj A) ≫ ΨM.map (ag.counit.app A))
    (hχψP : ∀ V, k'.map (χψP.app V) ≫ ak'.counit.app (ΨP.obj V) =
      αψP.app (Rk.obj V) ≫ ΨP.map (ak.counit.app V))
    (θ : e ⋙ k ⟶ g ⋙ f) (θ' : e' ⋙ k' ⟶ g' ⋙ f')
    (bc : Rg ⋙ e ⟶ f ⋙ Rk) (bc' : Rg' ⋙ e' ⟶ f' ⋙ Rk')
    (hbc : ∀ A, k.map (bc.app A) ≫ ak.counit.app (f.obj A) =
      θ.app (Rg.obj A) ≫ f.map (ag.counit.app A))
    (hbc' : ∀ C, k'.map (bc'.app C) ≫ ak'.counit.app (f'.obj C) =
      θ'.app (Rg'.obj C) ≫ f'.map (ag'.counit.app C))
    (hSQ : ∀ C, θ'.app (ΨM1.obj C) ≫ f'.map (αψM.app C) ≫ αφ.app (g.obj C) =
      k'.map (αφ'.app C) ≫ αψP.app (e.obj C) ≫ ΨP.map (θ.app C))
    (A : DX) :
    e'.map (χψM.app A) ≫ bc'.app (ΨM.obj A) ≫ Rk'.map (αφ.app A) =
      αφ'.app (Rg.obj A) ≫ ΨP1.map (bc.app A) ≫ χψP.app (f.obj A) := by
  have hL : k'.map (e'.map (χψM.app A)) ≫ k'.map (bc'.app (ΨM.obj A)) ≫
      ak'.counit.app _ ≫ αφ.app A = k'.map (αφ'.app (Rg.obj A)) ≫ αψP.app _ ≫
        ΨP.map (θ.app _ ≫ f.map (ag.counit.app A)) := by
    have n₁ := θ'.naturality (χψM.app A)
    have n₂ := αφ.naturality (ag.counit.app A)
    simp only [Functor.comp_obj, Functor.comp_map] at n₁ n₂
    rw [reassoc_of% (hbc' (ΨM.obj A)), reassoc_of% n₁, ← f'.map_comp_assoc, hχψM,
      f'.map_comp_assoc]
    erw [n₂]
    rw [reassoc_of% (hSQ (Rg.obj A)), ΨP.map_comp]
  have nR := αψP.naturality (bc.app A)
  have nL := ak'.counit.naturality (αφ.app A)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at nR nL
  apply (ak'.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  simp only [Functor.map_comp, Category.assoc]
  erw [nL, hχψP, reassoc_of% nR]
  rw [← ΨP.map_comp, hbc]
  exact hL

end Abstract

section Square

variable {X X' X₁ X₁' Z Z' Z₁ Z₁' : Scheme.{u}} {M : NearbyCyclesModel X X'}
  {M₁ : NearbyCyclesModel X₁ X₁'} {P : NearbyCyclesModel Z Z'} {P₁ : NearbyCyclesModel Z₁ Z₁'}
  {f₀ : Z ⟶ X} {f₀' : Z' ⟶ X'} {g : X ⟶ X₁} {g' : X' ⟶ X₁'} {k : Z ⟶ Z₁} {k' : Z' ⟶ Z₁'}
  {e : Z₁ ⟶ X₁} {e' : Z₁' ⟶ X₁'}
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **The pullback exchange through a square of pushforward exchanges**: for a commutative
square of morphisms of models `φ₀ : P ⟶ M`, `ψ : M ⟶ M₁`, `ψ' : P ⟶ P₁`, `φ₁ : P₁ ⟶ M₁`, if the
pushforward exchanges of `ψ` and `ψ'`, the base change morphisms of the squares of bases and of
special fibres and the pullback exchange of `φ₁` are invertible at the relevant objects, then
`Rk'_*` of the pullback exchange of `φ₀` is invertible at `A`. This is the square law of the
pushforward exchanges (`NearbyCyclesModel.pushforwardExchange_square_aux`). -/
theorem Hom.isIso_map_pullbackExchange_app_of_square (φ₀ : P.Hom M f₀ f₀')
    (ψ : M.Hom M₁ g g') (ψ' : P.Hom P₁ k k') (φ₁ : P₁.Hom M₁ e e')
    (htot : φ₀.total ≫ ψ.total = ψ'.total ≫ φ₁.total)
    (hgen : φ₀.generic ≫ ψ.generic = ψ'.generic ≫ φ₁.generic) (hb : f₀ ≫ g = k ≫ e)
    (hs : f₀' ≫ g' = k' ≫ e')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (hχ : IsIso ((ψ.pushforwardExchange Λ).app A))
    (hbc' : IsIso ((baseChangeMap Λ ⟨hs⟩).app ((M.nearbyCycles Λ).obj A)))
    (hα₁ : IsIso ((φ₁.pullbackExchange Λ).app (R((g)_*⟦Λ⟧).obj A)))
    (hbc : IsIso ((baseChangeMap Λ ⟨hb⟩).app A))
    (hχ' : IsIso ((ψ'.pushforwardExchange Λ).app (L((f₀)^*⟦Λ⟧).obj A))) :
    IsIso (R((k')_*⟦Λ⟧).map ((φ₀.pullbackExchange Λ).app A)) := by
  have hSQ := fun C ↦ Hom.pullbackExchange_square Λ φ₀ ψ ψ' φ₁ htot hgen hb hs C
  have key := pushforwardExchange_square_aux
    (derivedUpperStarLowerStarAdjunction Λ g) (derivedUpperStarLowerStarAdjunction Λ k)
    (derivedUpperStarLowerStarAdjunction Λ g') (derivedUpperStarLowerStarAdjunction Λ k')
    (φ₀.pullbackExchange Λ) (φ₁.pullbackExchange Λ) (ψ.pullbackExchange Λ)
    (ψ'.pullbackExchange Λ) (ψ.pushforwardExchange Λ) (ψ'.pushforwardExchange Λ)
    (ψ.map_pushforwardExchange_app_comp_counit_app Λ)
    (ψ'.map_pushforwardExchange_app_comp_counit_app Λ)
    (pullbackSquareComparison Λ ⟨hb⟩).hom (pullbackSquareComparison Λ ⟨hs⟩).hom
    (baseChangeMap Λ ⟨hb⟩) (baseChangeMap Λ ⟨hs⟩)
    (Adjunction.exchangeRight_app_comp_counit' _ _ _ _ rfl)
    (Adjunction.exchangeRight_app_comp_counit' _ _ _ _ rfl) hSQ A
  have hcomp : IsIso (L((e')^*⟦Λ⟧).map ((ψ.pushforwardExchange Λ).app A) ≫
      (baseChangeMap Λ ⟨hs⟩).app _ ≫ R((k')_*⟦Λ⟧).map ((φ₀.pullbackExchange Λ).app A)) := by
    rw [key]
    exact IsIso.comp_isIso' hα₁ (IsIso.comp_isIso' (Functor.map_isIso _ _) hχ')
  have := hχ
  have := hbc'
  have h₁ := IsIso.of_isIso_comp_left (L((e')^*⟦Λ⟧).map ((ψ.pushforwardExchange Λ).app A))
    ((baseChangeMap Λ ⟨hs⟩).app _ ≫ R((k')_*⟦Λ⟧).map ((φ₀.pullbackExchange Λ).app A))
  exact IsIso.of_isIso_comp_left ((baseChangeMap Λ ⟨hs⟩).app _)
    (R((k')_*⟦Λ⟧).map ((φ₀.pullbackExchange Λ).app A))

/-- **Invertibility of a pullback exchange through a square of pushforward exchanges**: for a
commutative square of morphisms of models `φ₀ : P ⟶ M`, `ψ : M ⟶ M₁`, `ψ' : P ⟶ P₁`,
`φ₁ : P₁ ⟶ M₁`, if the pushforward exchanges of `ψ` and `ψ'`, the base change morphisms of the
squares of bases and of special fibres and the pullback exchange of `φ₁` are invertible at the
relevant objects, and `Rk'_*` reflects isomorphisms, then the pullback exchange of `φ₀` is
invertible at `A` (`NearbyCyclesModel.Hom.isIso_map_pullbackExchange_app_of_square`). -/
theorem Hom.isIso_pullbackExchange_app_of_square (φ₀ : P.Hom M f₀ f₀') (ψ : M.Hom M₁ g g')
    (ψ' : P.Hom P₁ k k') (φ₁ : P₁.Hom M₁ e e')
    (htot : φ₀.total ≫ ψ.total = ψ'.total ≫ φ₁.total)
    (hgen : φ₀.generic ≫ ψ.generic = ψ'.generic ≫ φ₁.generic) (hb : f₀ ≫ g = k ≫ e)
    (hs : f₀' ≫ g' = k' ≫ e')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (hχ : IsIso ((ψ.pushforwardExchange Λ).app A))
    (hbc' : IsIso ((baseChangeMap Λ ⟨hs⟩).app ((M.nearbyCycles Λ).obj A)))
    (hα₁ : IsIso ((φ₁.pullbackExchange Λ).app (R((g)_*⟦Λ⟧).obj A)))
    (hbc : IsIso ((baseChangeMap Λ ⟨hb⟩).app A))
    (hχ' : IsIso ((ψ'.pushforwardExchange Λ).app (L((f₀)^*⟦Λ⟧).obj A)))
    (hR : ∀ {U V : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z') Ab.{u + 1})
      (condensedRingObj Λ Z'))} (a : U ⟶ V), IsIso (R((k')_*⟦Λ⟧).map a) → IsIso a) :
    IsIso ((φ₀.pullbackExchange Λ).app A) :=
  hR _ (φ₀.isIso_map_pullbackExchange_app_of_square Λ ψ ψ' φ₁ htot hgen hb hs A hχ hbc' hα₁ hbc
    hχ')

end Square

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
