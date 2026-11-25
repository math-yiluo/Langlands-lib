/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegersSheafLowerStar

/-!
# Derived pushforward of the limit of a tower of étale sheaves

Let `g : T ⟶ Y` be quasi-compact and quasi-separated and `L : ℕᵒᵖ ⥤ Sh(T_ét, Ab)` a tower of
étale abelian sheaves with epimorphic transitions (for instance the reductions `Lₙ = L₀ ⧸ ℓⁿ⁺¹`
of an `𝒪_E`-lattice `L₀` in a lisse `ℓ`-adic sheaf). In the derived category of abelian sheaves
on the pro-étale sites:

- `AlgebraicGeometry.ProEtale.isHomotopyLimit_singleFunctor_mapCone_comparisonUpperStar`: the
  limit `lim_n ν^* Lₙ` is the derived limit `R lim_n ν^* Lₙ`, by repleteness of the pro-étale
  topos;
- `AlgebraicGeometry.ProEtale.isHomotopyLimit_rightDerivedLowerStar_comparisonUpperStarTower`:
  hence `Rg_* (lim_n ν^* Lₙ) ≅ R lim_n ν^* Rg_*^{ét} Lₙ`, the derived pushforward being a
  triangulated right adjoint and `Rg_* ν^* ≅ ν^* Rg_*^{ét}`
  (`AlgebraicGeometry.ProEtale.comparisonUpperStarCompRightDerivedLowerStarIso`).

This generalises the case of the constant tower `𝒪_E ⧸ ℓⁿ`
(`isHomotopyLimit_comparisonUpperStar_rightDerivedLowerStar_constantSheafTower`, in the
namespace `AlgebraicGeometry.ProEtale`) to the towers of reductions of lattices, as needed for the
finiteness theorem for lisse sheaves
(`AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor_of_isAffine`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {T Y : Scheme.{u}} (L : ℕᵒᵖ ⥤ Sheaf T.smallEtaleTopology Ab.{u + 1})
  (hL : ∀ n : ℕ, Epi (L.map (homOfLE n.le_succ).op))
  {c : Cone (L ⋙ ν^*(T)[Ab.{u + 1}])} (hc : IsLimit c)

include hL hc in
/-- **`lim_n ν^* Lₙ ≅ R lim_n ν^* Lₙ`** for a tower of étale abelian sheaves with epimorphic
transitions: the comparison pullback `ν^*` preserves epimorphisms, and the pro-étale topos is
replete. -/
theorem isHomotopyLimit_singleFunctor_mapCone_comparisonUpperStar :
    IsHomotopyLimit ((DerivedCategory.singleFunctor _ 0).mapCone c) :=
  DerivedCategory.isHomotopyLimit_mapCone_singleFunctor_of_epiπAppZeroOfEpi
    Scheme.ProEt.epi_π_app_zero_of_epi_ab (fun n ↦ by
      have := hL n
      exact inferInstanceAs (Epi ((ν^*(T)[Ab.{u + 1}]).map (L.map (homOfLE n.le_succ).op))))
    hc

variable (g : T ⟶ Y) [QuasiCompact g] [QuasiSeparated g]

/-- The tower `n ↦ Rg_* ν^* Lₙ` is the tower `n ↦ ν^* Rg_*^{ét} Lₙ`. -/
noncomputable def rightDerivedLowerStarComparisonUpperStarTowerIso :
    ((L ⋙ ν^*(T)[Ab.{u + 1}]) ⋙ DerivedCategory.singleFunctor _ 0) ⋙
        (ProEtale.lowerStar Ab.{u + 1} g).rightDerivedFunctor ≅
      L ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (Etale.lowerStar Ab.{u + 1} g).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.ι ⋙ (comparisonUpperStar Ab.{u + 1} Y).mapDerivedCategory :=
  Functor.associator _ _ _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft L (comparisonUpperStarCompRightDerivedLowerStarIso g)

include hL hc in
/-- **`Rg_* (lim_n ν^* Lₙ) ≅ R lim_n ν^* Rg_*^{ét} Lₙ`**: for `g` quasi-compact and
quasi-separated and a tower `L` of étale abelian sheaves on `T` with epimorphic transitions, the
derived pushforward of `lim_n ν^* Lₙ` is the derived limit of the tower
`n ↦ ν^* Rg_*^{ét} Lₙ` of comparison pullbacks of derived étale pushforwards. -/
theorem isHomotopyLimit_rightDerivedLowerStar_comparisonUpperStarTower :
    IsHomotopyLimit ((Cone.postcompose
      (rightDerivedLowerStarComparisonUpperStarTowerIso L g).hom).obj
      ((ProEtale.lowerStar Ab.{u + 1} g).rightDerivedFunctor.mapCone
        ((DerivedCategory.singleFunctor _ 0).mapCone c))) :=
  have := ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} g)
    |>.mapDerivedCategoryRightDerivedAdjunction).isRightAdjoint
  ((isHomotopyLimit_singleFunctor_mapCone_comparisonUpperStar L hL hc).map _).of_iso
    (rightDerivedLowerStarComparisonUpperStarTowerIso L g) _ (Iso.refl _) fun n ↦ by simp

end AlgebraicGeometry.ProEtale
