/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.Exchange
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste
public import WeilConjectures.CategoryTheory.Adjunction.MatePasting

/-!

# The pushforward exchange of nearby cycles through base change morphisms

Let `φ : M ⟶ N` be a morphism of models (`NearbyCyclesModel.Hom`) over `f : X ⟶ Y` and
`f' : X' ⟶ Y'`, with morphism `t` of total spaces and `g` of geometric generic fibres. The
pushforward exchange `χ_f : Ψ_N Rf_* ⟶ Rf'_* Ψ_M` (`NearbyCyclesModel.Hom.pushforwardExchange`) is
the mate of the pullback exchange, which is the pasting of the squares of identifications, of
geometric generic fibres and of special fibres. Its component at `K` is therefore the composite
(`NearbyCyclesModel.Hom.pushforwardExchange_app`)
```
Li_N^* Rj_{N*} Lε_N^* Rf_* K ⟶ Li_N^* Rj_{N*} Rg_* Lε_M^* K      (base change of the ε-square)
  ⟶ Li_N^* Rt_* Rj_{M*} Lε_M^* K                                (composition of direct images)
  ⟶ Rf'_* Li_M^* Rj_{M*} Lε_M^* K                               (base change of the special fibres)
```
as in the proof of blueprint `prose-E-03` (2). The middle arrow
(`NearbyCyclesModel.Hom.lowerStarExchange`) is the iterated mate of the pullback comparison of the
square of geometric generic fibres, hence invertible. So `χ_f` is invertible at `K` as soon as the
two base change morphisms are
(`NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isIso_baseChangeMap`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

namespace NearbyCyclesModel.Hom

variable {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f f')

/-- The comparison `Rj_{N*} Rg_* ⟶ Rt_* Rj_{M*}` of the direct images along the two sides of the
square of geometric generic fibres `g ≫ j_N = j_M ≫ t` of a morphism of models: the mate, along
`Lg^* ⊣ Rg_*` and `Lt^* ⊣ Rt_*`, of the base change morphism `Lt^* Rj_{N*} ⟶ Rj_{M*} Lg^*` used
in the pullback exchange. It is invertible
(`NearbyCyclesModel.Hom.isIso_lowerStarExchange`). -/
noncomputable def lowerStarExchange :
    R((φ.generic)_*⟦Λ⟧) ⋙ R((N.j)_*⟦Λ⟧) ⟶ R((M.j)_*⟦Λ⟧) ⋙ R((φ.total)_*⟦Λ⟧) :=
  (mateEquiv (derivedUpperStarLowerStarAdjunction Λ φ.generic)
    (derivedUpperStarLowerStarAdjunction Λ φ.total)
    (mateEquiv (derivedUpperStarLowerStarAdjunction Λ N.j)
      (derivedUpperStarLowerStarAdjunction Λ M.j)
      (pullbackSquareComparison Λ φ.commSq_j).hom))

/-- The comparison `Rj_{N*} Rg_* ⟶ Rt_* Rj_{M*}` is invertible: it is the conjugate of the
pullback comparison `Lt^* Lj_M^* ≅ Lj_N^* Lg^*`
(`CategoryTheory.iterated_mateEquiv_conjugateEquiv`). -/
instance isIso_lowerStarExchange : IsIso (φ.lowerStarExchange Λ) := by
  rw [lowerStarExchange, iterated_mateEquiv_conjugateEquiv]
  infer_instance

/-- **The pushforward exchange through base change morphisms** (proof of blueprint
`prose-E-03` (2)): the component of `χ_f : Ψ_N Rf_* ⟶ Rf'_* Ψ_M` at `K` is
`Li_N^* Rj_{N*}` of the base change morphism `Lε_N^* Rf_* K ⟶ Rg_* Lε_M^* K` of the square of
identifications, followed by `Li_N^*` of the comparison `Rj_{N*} Rg_* ⟶ Rt_* Rj_{M*}`
(`NearbyCyclesModel.Hom.lowerStarExchange`) and by the base change morphism
`Li_N^* Rt_* ⟶ Rf'_* Li_M^*` of the square of special fibres at `Rj_{M*} Lε_M^* K`. -/
theorem pushforwardExchange_app
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (φ.pushforwardExchange Λ).app K =
      L((N.i)^*⟦Λ⟧).map (R((N.j)_*⟦Λ⟧).map ((baseChangeMap Λ φ.commSq_ε).app K)) ≫
        L((N.i)^*⟦Λ⟧).map ((φ.lowerStarExchange Λ).app (L((M.ε)^*⟦Λ⟧).obj K)) ≫
          (baseChangeMap Λ φ.commSq_i).app (R((M.j)_*⟦Λ⟧).obj (L((M.ε)^*⟦Λ⟧).obj K)) :=
  app_eq_comp_of_eq_mateEquiv_pasting (derivedUpperStarLowerStarAdjunction Λ f)
    (derivedUpperStarLowerStarAdjunction Λ φ.generic)
    (derivedUpperStarLowerStarAdjunction Λ φ.total) (derivedUpperStarLowerStarAdjunction Λ f')
    (pullbackSquareComparison Λ φ.commSq_ε).hom
    (mateEquiv (derivedUpperStarLowerStarAdjunction Λ N.j)
      (derivedUpperStarLowerStarAdjunction Λ M.j) (pullbackSquareComparison Λ φ.commSq_j).hom)
    (pullbackSquareComparison Λ φ.commSq_i).hom (φ.pullbackExchange Λ) rfl
    (φ.pushforwardExchange Λ) rfl (baseChangeMap Λ φ.commSq_ε)
    (Adjunction.exchangeRight_eq_mateEquiv _ _ _) (φ.lowerStarExchange Λ) rfl
    (baseChangeMap Λ φ.commSq_i) (Adjunction.exchangeRight_eq_mateEquiv _ _ _) K

/-- The pushforward exchange `χ_f : Ψ_N Rf_* ⟶ Rf'_* Ψ_M` is invertible at `K` if the base change
morphism `Lε_N^* Rf_* ⟶ Rg_* Lε_M^*` of the square of identifications is invertible at `K` and
the base change morphism `Li_N^* Rt_* ⟶ Rf'_* Li_M^*` of the square of special fibres is
invertible at `Rj_{M*} Lε_M^* K` (`NearbyCyclesModel.Hom.pushforwardExchange_app`). -/
theorem isIso_pushforwardExchange_app_of_isIso_baseChangeMap
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (hε : IsIso ((baseChangeMap Λ φ.commSq_ε).app K))
    (hi : IsIso ((baseChangeMap Λ φ.commSq_i).app
      (R((M.j)_*⟦Λ⟧).obj (L((M.ε)^*⟦Λ⟧).obj K)))) :
    IsIso ((φ.pushforwardExchange Λ).app K) := by
  rw [pushforwardExchange_app]
  infer_instance

end NearbyCyclesModel.Hom

end AlgebraicGeometry.ProEtale.CondensedRing
