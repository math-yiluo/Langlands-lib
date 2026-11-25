/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarFilteredColimit
public import WeilConjectures.SixFunctors.ProEtale.Adic.SubfieldSheafColimit
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantSheafColimit

/-!
# Higher direct images of `E_T` and `ℚ̄_ℓ,T` as colimits

For a quasi-compact quasi-separated morphism `g : T ⟶ Y`, the higher direct images `Rⁱg_*` of
abelian pro-étale sheaves commute with filtered colimits
(`AlgebraicGeometry.ProEtale.preservesColimitsOfShape_rightDerived_lowerStar`). Applied to
`E_T = 𝒪_{E,T}[1/ℓ]` and `ℚ̄_ℓ,T = colim_E E_T`:

- `AlgebraicGeometry.ProEtale.isColimitRightDerivedLowerStarPadicSubfieldSheafCocone`:
  `Rⁱg_* E_T = colim (Rⁱg_* 𝒪_{E,T} --ℓ--> Rⁱg_* 𝒪_{E,T} --ℓ--> ⋯) = (Rⁱg_* 𝒪_{E,T})[1/ℓ]`;
- `AlgebraicGeometry.ProEtale.isColimitRightDerivedLowerStarAdicConstantSheafCocone`:
  `Rⁱg_* ℚ̄_ℓ,T = colim_E Rⁱg_* E_T` for the abelian sheaf underlying `ℚ̄_ℓ,T`.
-/

@[expose] public section

universe u

open CategoryTheory Limits PadicAlgCl

namespace AlgebraicGeometry.ProEtale

variable {T Y : Scheme.{u}} (g : T ⟶ Y) [QuasiCompact g] [QuasiSeparated g] (l : ℕ) [Fact l.Prime]

/-- `Rⁱg_*` preserves colimits indexed by `ℕ`. -/
instance (n : ℕ) : PreservesColimitsOfShape ℕ
    ((ProEtale.lowerStar AddCommGrpCat.{u + 1} g).rightDerived n) :=
  preservesColimitsOfShape_rightDerived_lowerStar g ℕ n

/-- `Rⁱg_*` preserves colimits over the finite subextensions of `ℚ̄_ℓ`. -/
instance (n : ℕ) : PreservesColimitsOfShape (FiniteIntermediateField l)
    ((ProEtale.lowerStar AddCommGrpCat.{u + 1} g).rightDerived n) :=
  preservesColimitsOfShape_rightDerived_lowerStar g (FiniteIntermediateField l) n

/-- **`Rⁱg_* E_T = (Rⁱg_* 𝒪_{E,T})[1/ℓ]`**: the higher direct images of `E_T` are the colimit of
those of `𝒪_{E,T}` along multiplication by `ℓ`. -/
noncomputable def isColimitRightDerivedLowerStarPadicSubfieldSheafCocone (E : Type) [Field E]
    [Algebra E (PadicAlgCl l)] (n : ℕ) :
    letI := normedFieldOfAlgebra l E
    IsColimit (((ProEtale.lowerStar AddCommGrpCat.{u + 1} g).rightDerived n).mapCocone
      (padicSubfieldSheafCocone T l E)) :=
  letI := normedFieldOfAlgebra l E
  isColimitOfPreserves _ (isColimitPadicSubfieldSheafCocone T l E)

/-- **`Rⁱg_* ℚ̄_ℓ,T = colim_E Rⁱg_* E_T`**: the higher direct images of the abelian sheaf
underlying `ℚ̄_ℓ,T` are the colimit of those of the `E_T`. -/
noncomputable def isColimitRightDerivedLowerStarAdicConstantSheafCocone (n : ℕ) :
    IsColimit (((ProEtale.lowerStar AddCommGrpCat.{u + 1} g).rightDerived n).mapCocone
      ((padicAlgClSheafCocone T l).extend (padicAlgClSheafIsoAdicConstantSheaf T l).hom)) :=
  isColimitOfPreserves _ (isColimitPadicAlgClSheafCoconeExtend T l)

end AlgebraicGeometry.ProEtale
