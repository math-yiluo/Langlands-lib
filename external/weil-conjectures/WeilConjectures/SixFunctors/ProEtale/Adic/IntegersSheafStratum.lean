/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegersSheafHomologyTower
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LocallyClosedUpperStarHomotopyLimit
public import WeilConjectures.SixFunctors.ProEtale.Comparison.UniversalCoverIntegralIdentification

/-!
# `Rg_* 𝒪_{E,T}` restricted to a stratum, on the universal covers

Let `g : T ⟶ Y` be quasi-compact and quasi-separated, `E` a finite extension of `ℚ_ℓ` and
`j : S ⟶ Y` a locally closed immersion (a stratum). Restricting
`Rg_* 𝒪_{E,T} ≅ R lim_n ν^* Rg_*^{ét}(𝒪_E ⧸ ℓⁿ)` to `S`:

- `AlgebraicGeometry.ProEtale.isHomotopyLimit_upperStar_rightDerivedLowerStar_integersStratum`:
  `j^* Rg_* 𝒪_{E,T} ≅ R lim_n j^* ν^* Rg_*^{ét}(𝒪_E ⧸ ℓⁿ)`, the pullback to a stratum commuting
  with `R lim`
  (`AlgebraicGeometry.ProEtale.isHomotopyLimit_upperStar_mapDerivedCategory_mapCone_comp`);
- `AlgebraicGeometry.ProEtale.homologyIntegersStratumTowerIso`: the cohomology towers of the
  restricted tower are the abelian sheaves underlying `ν^* j^* Hᵏ(Rg_* (Λ ⧸ ℓⁿ))`,
  `Λ = Shrink 𝒪_E`;
- `AlgebraicGeometry.ProEtale.nonempty_iso_homologyUpperStar_integersStratum`: hence, when these
  towers are `IsSetFLC` on `S` in degrees `k - 1` and `k` (as given by the uniform stratification,
  `AlgebraicGeometry.Etale.isSetFLC_upperStar_higherDirectImageQuotPowTower_obj`), the pullback of
  `Hᵏ(j^* Rg_* 𝒪_{E,T})` to the universal cover `Ỹ_y` of `S` is `C(-, lim_n Gₙ)`, `Gₙ` the stalks
  of `j^* Hᵏ(Rg_* (Λ ⧸ ℓⁿ))`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite PadicAlgCl Pretriangulated

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl l)]
  {T Y S : Scheme.{u}} (g : T ⟶ Y) (j : S ⟶ Y)

/-- The tower `n ↦ j^* ν^* Rg_*^{ét}(𝒪_E ⧸ ℓⁿ)` of complexes of abelian pro-étale sheaves on a
stratum `j : S ⟶ Y`. -/
noncomputable abbrev integersStratumTower :
    ℕᵒᵖ ⥤ DerivedCategory (Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1}) :=
  (constantSheafTower T (integersModPowTransition l E) ⋙
    DerivedCategory.Plus.singleFunctor _ 0 ⋙
    (Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.ι ⋙ (comparisonUpperStar AddCommGrpCat.{u + 1} Y).mapDerivedCategory) ⋙
    (ProEtale.upperStar AddCommGrpCat.{u + 1} j).mapDerivedCategory

/-- **The cohomology towers on a stratum**: `Hᵏ(j^* ν^* Rg_*^{ét}(𝒪_E ⧸ ℓⁿ))` is, naturally in
`n`, the abelian sheaf underlying `ν^* j^* Hᵏ(Rg_* (Λ ⧸ ℓⁿ))`. -/
noncomputable def homologyIntegersStratumTowerIso (k : ℤ) :
    integersStratumTower l E g j ⋙ DerivedCategory.homologyFunctor _ k ≅
      (Etale.higherDirectImageQuotPowTower (integersShrinkIdeal.{u} l E) g k ⋙
          Etale.upperStar (ModuleCat.{u + 1} (integersShrink.{u} l E)) j) ⋙
        comparisonUpperStar _ S ⋙ sheafCompose (ProEt.topology S)
          (forget₂ (ModuleCat.{u + 1} (integersShrink.{u} l E)) AddCommGrpCat.{u + 1}) :=
  let Λ := integersShrink.{u} l E
  let H := Etale.higherDirectImageQuotPowTower (integersShrinkIdeal.{u} l E) g k
  Functor.isoWhiskerLeft (constantSheafTower T (integersModPowTransition l E) ⋙
      DerivedCategory.Plus.singleFunctor _ 0 ⋙
      (Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.ι ⋙ (comparisonUpperStar AddCommGrpCat.{u + 1} Y).mapDerivedCategory)
      ((ProEtale.upperStar AddCommGrpCat.{u + 1} j).mapDerivedCategoryHomologyFunctorIso k).symm ≪≫
    Functor.isoWhiskerRight (homologyIntegersTowerIso l E g k)
      (ProEtale.upperStar AddCommGrpCat.{u + 1} j) ≪≫
    Functor.isoWhiskerLeft (H ⋙ comparisonUpperStar (ModuleCat.{u + 1} Λ) Y)
      (sheafComposeForget₂CompUpperStarIso Λ j) ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft H
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) j))
      (sheafCompose (ProEt.topology S) (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))

variable [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]
  [QuasiCompact g] [QuasiSeparated g]

/-- The cone exhibiting `Rg_* 𝒪_{E,T}` as `R lim_n ν^* Rg_*^{ét}(𝒪_E ⧸ ℓⁿ)`. -/
noncomputable abbrev integersCone :=
  letI := normedFieldOfAlgebra l E
  (Cone.postcompose
    (rightDerivedLowerStarContinuousMapAbSheafTowerIso g (integersModPowTransition l E)).hom).obj
      ((ProEtale.lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctor.mapCone
        ((DerivedCategory.singleFunctor _ 0).mapCone
          (continuousMapAbSheafCone T (integersModPowTransition l E)
            (fun _ ↦ continuous_of_discreteTopology) (integersModPowMk l E)
            (continuous_integersModPowMk l E) (integersModPowTransition_comp l E))))

/-- **`j^* Rg_* 𝒪_{E,T} ≅ R lim_n j^* ν^* Rg_*^{ét}(𝒪_E ⧸ ℓⁿ)`** for a locally closed immersion
`j = i ≫ o`, `i : S ⟶ U` a closed immersion with quasi-compact open complement in a
quasi-compact quasi-separated `U` and `o : U ⟶ Y` an open immersion. -/
theorem isHomotopyLimit_upperStar_rightDerivedLowerStar_integersStratum {U V : Scheme.{u}}
    [CompactSpace U] [QuasiSeparatedSpace U] (i : S ⟶ U) [IsClosedImmersion i] (jc : V ⟶ U)
    [IsOpenImmersion jc] [QuasiCompact jc] (hij : IsCompl (Set.range i.base) (Set.range jc.base))
    (o : U ⟶ Y) [IsOpenImmersion o] :
    IsHomotopyLimit ((ProEtale.upperStar AddCommGrpCat.{u + 1} (i ≫ o)).mapDerivedCategory.mapCone
      (integersCone l E g)) :=
  isHomotopyLimit_upperStar_mapDerivedCategory_mapCone_comp i jc hij o
    (isHomotopyLimit_comparisonUpperStar_rightDerivedLowerStar_constantSheafTower g l E)

/-- **The integral identification on the universal covers of a stratum.** Let `j = i ≫ o` be a
locally closed immersion as in
`AlgebraicGeometry.ProEtale.isHomotopyLimit_upperStar_rightDerivedLowerStar_integersStratum`, and
suppose that the restricted towers `n ↦ j^* Hᵐ(Rg_* (Λ ⧸ ℓⁿ))` are `IsSetFLC` for `m = k - 1, k`.
Then on the universal cover `Ỹ_y` of `S`, the pullback of `Hᵏ(j^* Rg_* 𝒪_{E,T})` is
`C(-, lim_n Gₙ)`, `Gₙ` the (finite) stalks of `j^* Hᵏ(Rg_* (Λ ⧸ ℓⁿ))` at the base point. -/
theorem nonempty_iso_homologyUpperStar_integersStratum {U V : Scheme.{u}}
    [CompactSpace U] [QuasiSeparatedSpace U] (i : S ⟶ U) [IsClosedImmersion i] (jc : V ⟶ U)
    [IsOpenImmersion jc] [QuasiCompact jc] (hij : IsCompl (Set.range i.base) (Set.range jc.base))
    (o : U ⟶ Y) [IsOpenImmersion o] {Ω : Type u} [Field Ω] (Ũ : Scheme.UniversalCovers S Ω)
    (y : Spec (.of (AlgebraicClosure Ω)) ⟶ S) (k : ℤ)
    (hH : ∀ n : ℕ, IsSetFLC ((Etale.upperStar (ModuleCat.{u + 1} (integersShrink.{u} l E))
      (i ≫ o)).obj ((Etale.higherDirectImageQuotPowTower (integersShrinkIdeal.{u} l E) g
        (k - 1)).obj (op n))))
    (hH' : ∀ n : ℕ, IsSetFLC ((Etale.upperStar (ModuleCat.{u + 1} (integersShrink.{u} l E))
      (i ≫ o)).obj ((Etale.higherDirectImageQuotPowTower (integersShrinkIdeal.{u} l E) g
        k).obj (op n)))) :
    let H' := Etale.higherDirectImageQuotPowTower (integersShrinkIdeal.{u} l E) g k ⋙
      Etale.upperStar (ModuleCat.{u + 1} (integersShrink.{u} l E)) (i ≫ o)
    let St := (pointSmallEtale (Ũ.pt y ≫ Ũ.proj y)).sheafFiber
      (A := ModuleCat.{u + 1} (integersShrink.{u} l E))
    have (n : ℕ) : Finite (St.obj (H'.obj (op n))) := (hH' n).finite_sheafFiber _
    Nonempty ((DerivedCategory.homologyFunctor _ k).obj
        ((ProEtale.upperStar AddCommGrpCat.{u + 1} (Ũ.proj y)).mapDerivedCategory.obj
          ((ProEtale.upperStar AddCommGrpCat.{u + 1} (i ≫ o)).mapDerivedCategory.obj
            (integersCone l E g).pt)) ≅
      ProEtale.continuousMapAddSheaf (Ũ.cover y)
        (ProEtale.towerLimitAddSubgroup (Qs := fun n ↦ DiscreteShrink (St.obj (H'.obj (op n))))
          (fun n ↦ DiscreteShrink.map
            (St.map (H'.map (homOfLE (n.le_add_right 1)).op)).hom.toAddMonoidHom))) := by
  exact Ũ.nonempty_iso_homologyUpperStar_continuousMapAddSheaf' y
    (isHomotopyLimit_upperStar_rightDerivedLowerStar_integersStratum l E g i jc hij o) k
    _ _ hH hH' (homologyIntegersStratumTowerIso l E g (i ≫ o) (k - 1))
    (homologyIntegersStratumTowerIso l E g (i ≫ o) k)

end AlgebraicGeometry.ProEtale
