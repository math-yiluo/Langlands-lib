/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ExtensionTowerLocallyConstant
public import WeilConjectures.SixFunctors.ProEtale.Adic.ComparisonTowerLowerStar
public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegersSheafStratum

/-!
# The integral identification on a stratum for a tower of étale sheaves of modules

Let `Λ` be a ring, `M : ℕᵒᵖ ⥤ Sh(T_ét, Λ)` a tower of étale sheaves of `Λ`-modules whose
underlying abelian tower has epimorphic transitions (for instance the reductions
`Mₙ = L₀ ⧸ ℓⁿ⁺¹` of an `𝒪_E`-lattice in a lisse `ℓ`-adic sheaf), `c` a limit cone of
`n ↦ ν^* Mₙ` (as abelian pro-étale sheaves), `g : T ⟶ Y` quasi-compact and quasi-separated and
`j = i ≫ o : S ⟶ Y` a stratum. This file generalises
`WeilConjectures.SixFunctors.ProEtale.Adic.IntegersSheafStratum` from the constant tower
`Λ ⧸ ℓⁿ` to `M`:

- `AlgebraicGeometry.ProEtale.homologyModuleTowerStratumIso`: the cohomology towers of
  `n ↦ j^* ν^* Rg_*^{ét} Mₙ` are the abelian sheaves underlying `ν^* j^* Hᵏ(Rg_* Mₙ)`;
- `AlgebraicGeometry.ProEtale.isHomotopyLimit_upperStar_rightDerivedLowerStar_moduleTowerStratum`:
  `j^* Rg_* (lim_n ν^* Mₙ) ≅ R lim_n j^* ν^* Rg_*^{ét} Mₙ`;
- `AlgebraicGeometry.ProEtale.nonempty_iso_homologyUpperStar_moduleTowerStratum`: when the
  towers `n ↦ j^* Hᵐ(Rg_* Mₙ)` are `IsSetFLC` for `m = k - 1, k` (as given by
  `AlgebraicGeometry.Etale.isSetFLC_upperStar_homology_rightDerived_of_tower`), the pullback of
  `Hᵏ(j^* Rg_* (lim_n ν^* Mₙ))` to the universal cover `Ỹ_y` of `S` is `C(-, lim_n Gₙ)`, `Gₙ` the
  stalks of `j^* Hᵏ(Rg_* Mₙ)` at the base point.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] {T Y S : Scheme.{u}} (g : T ⟶ Y)

/-- `Hᵏ(ν^* Rg_*^{ét} M) ≅ ν^* Hᵏ(Rg_* M)` for a sheaf `M` of `Λ`-modules, on the underlying
abelian sheaves, as an isomorphism of functors: taking underlying abelian sheaves commutes with
derived direct images, with `ν^*` and with cohomology. -/
noncomputable def moduleAbelianHomologyComparisonIso (k : ℤ) :
    Etale.moduleAbelianForget Λ T ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (Etale.lowerStar Ab.{u + 1} g).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.ι ⋙ (comparisonUpperStar Ab.{u + 1} Y).mapDerivedCategory ⋙
          DerivedCategory.homologyFunctor _ k ≅
      DerivedCategory.singleFunctor _ 0 ⋙
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctor ⋙
          DerivedCategory.homologyFunctor _ k ⋙ comparisonUpperStar _ Y ⋙
            sheafCompose (ProEt.topology Y) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1}) :=
  let fT := Etale.moduleAbelianForget Λ T
  let fY := Etale.moduleAbelianForget Λ Y
  let ν := comparisonUpperStar Ab.{u + 1} Y
  let e₂ : fT ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (Etale.lowerStar Ab.{u + 1} g).rightDerivedFunctorPlus ≅
      DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctorPlus ⋙
          fY.mapDerivedCategoryPlus :=
    Functor.isoWhiskerRight (fT.mapDerivedCategoryPlusSingleFunctor 0).symm _ ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
        (Etale.moduleAbelianDerivedLowerStarIso Λ g).symm
  let e₃ : fY.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι ⋙ ν.mapDerivedCategory ⋙
        DerivedCategory.homologyFunctor _ k ≅
      DerivedCategory.Plus.ι ⋙ DerivedCategory.homologyFunctor _ k ⋙ fY ⋙ ν :=
    Functor.isoWhiskerLeft (fY.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι)
        (ν.mapDerivedCategoryHomologyFunctorIso k).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft DerivedCategory.Plus.ι
          (fY.mapDerivedCategoryHomologyFunctorIso k).symm) ν
  let e₅ : DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.ι ≅
      DerivedCategory.singleFunctor _ 0 ⋙
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctor :=
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctorPlusCompatibility ≪≫
      Functor.isoWhiskerRight (DerivedCategory.Plus.singleFunctorιIso _ 0) _
  let Hk := DerivedCategory.homologyFunctor (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) k
  let fP := sheafCompose (ProEt.topology Y) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})
  let e₄ : (DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctorPlus) ⋙
        fY.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι ⋙ ν.mapDerivedCategory ⋙
          DerivedCategory.homologyFunctor _ k ≅
      (DerivedCategory.singleFunctor _ 0 ⋙
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctor) ⋙ Hk ⋙
          comparisonUpperStar _ Y ⋙ fP :=
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctorPlus) e₃ ≪≫
      Functor.isoWhiskerRight e₅ (Hk ⋙ fY ⋙ ν) ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.singleFunctor _ 0 ⋙
          (Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctor ⋙ Hk)
        (sheafComposeForget₂CompComparisonUpperStarIso Λ Y)
  Functor.isoWhiskerRight e₂ (DerivedCategory.Plus.ι ⋙ ν.mapDerivedCategory ⋙
    DerivedCategory.homologyFunctor _ k) ≪≫ e₄

variable {Λ} (M : ℕᵒᵖ ⥤ Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (j : S ⟶ Y)

/-- The tower `n ↦ j^* ν^* Rg_*^{ét} Mₙ` of complexes of abelian pro-étale sheaves on a stratum
`j : S ⟶ Y`, for a tower `M` of étale sheaves of `Λ`-modules on `T`. -/
noncomputable abbrev moduleTowerStratum :
    ℕᵒᵖ ⥤ DerivedCategory (Sheaf (ProEt.topology S) Ab.{u + 1}) :=
  ((M ⋙ Etale.moduleAbelianForget Λ T) ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙
    (Etale.lowerStar Ab.{u + 1} g).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.ι ⋙ (comparisonUpperStar Ab.{u + 1} Y).mapDerivedCategory) ⋙
    (ProEtale.upperStar Ab.{u + 1} j).mapDerivedCategory

/-- **The cohomology towers on a stratum**: `Hᵏ(j^* ν^* Rg_*^{ét} Mₙ)` is, naturally in `n`, the
abelian sheaf underlying `ν^* j^* Hᵏ(Rg_* Mₙ)`. -/
noncomputable def homologyModuleTowerStratumIso (k : ℤ) :
    moduleTowerStratum g M j ⋙ DerivedCategory.homologyFunctor _ k ≅
      (M ⋙ Etale.upperStarHomologyRightDerived g j k) ⋙ comparisonUpperStar _ S ⋙
        sheafCompose (ProEt.topology S) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1}) :=
  let H := M ⋙ DerivedCategory.singleFunctor _ 0 ⋙
    (Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor _ k
  Functor.isoWhiskerLeft ((M ⋙ Etale.moduleAbelianForget Λ T) ⋙
      DerivedCategory.Plus.singleFunctor _ 0 ⋙
      (Etale.lowerStar Ab.{u + 1} g).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.ι ⋙ (comparisonUpperStar Ab.{u + 1} Y).mapDerivedCategory)
      ((ProEtale.upperStar Ab.{u + 1} j).mapDerivedCategoryHomologyFunctorIso k).symm ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft M (moduleAbelianHomologyComparisonIso Λ g k))
      (ProEtale.upperStar Ab.{u + 1} j) ≪≫
    Functor.isoWhiskerLeft (H ⋙ comparisonUpperStar (ModuleCat.{u + 1} Λ) Y)
      (sheafComposeForget₂CompUpperStarIso Λ j) ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft H
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) j))
      (sheafCompose (ProEt.topology S) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1}))

variable [QuasiCompact g] [QuasiSeparated g]
  {c : Cone ((M ⋙ Etale.moduleAbelianForget Λ T) ⋙ ν^*(T)[Ab.{u + 1}])}

/-- The cone exhibiting `Rg_* (lim_n ν^* Mₙ)` as `R lim_n ν^* Rg_*^{ét} Mₙ`. -/
noncomputable abbrev moduleTowerCone :=
  (Cone.postcompose
    (rightDerivedLowerStarComparisonUpperStarTowerIso
      (M ⋙ Etale.moduleAbelianForget Λ T) g).hom).obj
      ((ProEtale.lowerStar Ab.{u + 1} g).rightDerivedFunctor.mapCone
        ((DerivedCategory.singleFunctor _ 0).mapCone c))

variable (hM : ∀ n : ℕ, Epi ((M ⋙ Etale.moduleAbelianForget Λ T).map (homOfLE n.le_succ).op))
  (hc : IsLimit c)

include hM hc in
/-- **`j^* Rg_* (lim_n ν^* Mₙ) ≅ R lim_n j^* ν^* Rg_*^{ét} Mₙ`** for a locally closed immersion
`j = i ≫ o`, `i : S ⟶ U` a closed immersion with quasi-compact open complement in a
quasi-compact quasi-separated `U` and `o : U ⟶ Y` an open immersion. -/
theorem isHomotopyLimit_upperStar_rightDerivedLowerStar_moduleTowerStratum {U V : Scheme.{u}}
    [CompactSpace U] [QuasiSeparatedSpace U] (i : S ⟶ U) [IsClosedImmersion i] (jc : V ⟶ U)
    [IsOpenImmersion jc] [QuasiCompact jc] (hij : IsCompl (Set.range i.base) (Set.range jc.base))
    (o : U ⟶ Y) [IsOpenImmersion o] :
    IsHomotopyLimit ((ProEtale.upperStar Ab.{u + 1} (i ≫ o)).mapDerivedCategory.mapCone
      (moduleTowerCone g M (c := c))) :=
  isHomotopyLimit_upperStar_mapDerivedCategory_mapCone_comp i jc hij o
    (isHomotopyLimit_rightDerivedLowerStar_comparisonUpperStarTower _ hM hc g)

include hM hc in
/-- **The integral identification on the universal covers of a stratum, for a tower.** Let
`j = i ≫ o` be a locally closed immersion as in
`AlgebraicGeometry.ProEtale.isHomotopyLimit_upperStar_rightDerivedLowerStar_moduleTowerStratum`,
and suppose that the restricted towers `n ↦ j^* Hᵐ(Rg_* Mₙ)` are `IsSetFLC` for `m = k - 1, k`.
Then on the universal cover `Ỹ_y` of `S`, the pullback of `Hᵏ(j^* Rg_* (lim_n ν^* Mₙ))` is
`C(-, lim_n Gₙ)`, `Gₙ` the (finite) stalks of `j^* Hᵏ(Rg_* Mₙ)` at the base point. -/
theorem nonempty_iso_homologyUpperStar_moduleTowerStratum {U V : Scheme.{u}}
    [CompactSpace U] [QuasiSeparatedSpace U] (i : S ⟶ U) [IsClosedImmersion i] (jc : V ⟶ U)
    [IsOpenImmersion jc] [QuasiCompact jc] (hij : IsCompl (Set.range i.base) (Set.range jc.base))
    (o : U ⟶ Y) [IsOpenImmersion o] {Ω : Type u} [Field Ω] (Ũ : Scheme.UniversalCovers S Ω)
    (y : Spec (.of (AlgebraicClosure Ω)) ⟶ S) (k : ℤ)
    (hH : ∀ n : ℕ, IsSetFLC ((Etale.upperStarHomologyRightDerived g (i ≫ o) (k - 1)).obj
      (M.obj (op n))))
    (hH' : ∀ n : ℕ, IsSetFLC ((Etale.upperStarHomologyRightDerived g (i ≫ o) k).obj
      (M.obj (op n)))) :
    let H' := M ⋙ Etale.upperStarHomologyRightDerived g (i ≫ o) k
    let St := (pointSmallEtale (Ũ.pt y ≫ Ũ.proj y)).sheafFiber (A := ModuleCat.{u + 1} Λ)
    have (n : ℕ) : Finite (St.obj (H'.obj (op n))) := (hH' n).finite_sheafFiber _
    Nonempty ((DerivedCategory.homologyFunctor _ k).obj
        ((ProEtale.upperStar Ab.{u + 1} (Ũ.proj y)).mapDerivedCategory.obj
          ((ProEtale.upperStar Ab.{u + 1} (i ≫ o)).mapDerivedCategory.obj
            (moduleTowerCone g M (c := c)).pt)) ≅
      ProEtale.continuousMapAddSheaf (Ũ.cover y)
        (ProEtale.towerLimitAddSubgroup (Qs := fun n ↦ DiscreteShrink (St.obj (H'.obj (op n))))
          (fun n ↦ DiscreteShrink.map
            (St.map (H'.map (homOfLE (n.le_add_right 1)).op)).hom.toAddMonoidHom))) :=
  Ũ.nonempty_iso_homologyUpperStar_continuousMapAddSheaf' y
    (isHomotopyLimit_upperStar_rightDerivedLowerStar_moduleTowerStratum g M hM hc i jc hij o) k
    _ _ hH hH' (homologyModuleTowerStratumIso g M (i ≫ o) (k - 1))
    (homologyModuleTowerStratumIso g M (i ≫ o) k)

end AlgebraicGeometry.ProEtale
