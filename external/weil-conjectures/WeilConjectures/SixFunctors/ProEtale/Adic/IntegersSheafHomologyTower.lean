/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.NumberTheory.Padics.IntegersShrinkModPow
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.AbelianConstant
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.QuotPowHigherDirectImage
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Forget
public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegersSheafLowerStar
public import WeilConjectures.SixFunctors.ProEtale.Comparison.ForgetUpperStar

/-!
# The cohomology towers of `R lim_n ν^* Rg_*^{ét}(𝒪_E ⧸ ℓⁿ)`

The homotopy limit
`isHomotopyLimit_comparisonUpperStar_rightDerivedLowerStar_constantSheafTower` (in the namespace
`AlgebraicGeometry.ProEtale`) writes `Rg_* 𝒪_{E,T}` as the derived limit of the tower
`n ↦ ν^* Rg_*^{ét}(𝒪_E ⧸ ℓⁿ)` of complexes of *abelian* sheaves. This file identifies its
cohomology towers with the abelian sheaves underlying `ν^*` of the tower `n ↦ Hᵏ(Rg_* (Λ ⧸ ℓⁿ))`
of étale sheaves of modules over the single ring `Λ = Shrink 𝒪_E`
(`AlgebraicGeometry.Etale.higherDirectImageQuotPowTower`), naturally in `n`, which is the form of
the hypotheses of
`AlgebraicGeometry.Scheme.UniversalCovers.nonempty_iso_homologyUpperStar_continuousMapAddSheaf'`:

- `AlgebraicGeometry.ProEtale.constantSheafTowerIsoQuotPow`: the tower of constant abelian
  sheaves `𝒪_E ⧸ ℓⁿ` is the abelian tower underlying the constant sheaves of `Λ`-modules
  `Λ ⧸ ℓⁿ` (`PadicAlgCl.integersModPowEquivShrinkQuot`);
- `AlgebraicGeometry.ProEtale.homologyIntegersTowerIso`:
  `Hᵏ(ν^* Rg_*^{ét}(𝒪_E ⧸ ℓⁿ)) ≅ forget₂ (ν^* Hᵏ(Rg_* (Λ ⧸ ℓⁿ)))`, naturally in `n`. It uses
  that taking underlying abelian sheaves commutes with derived direct images
  (`AlgebraicGeometry.Etale.moduleAbelianDerivedLowerStarIso`), with `ν^*`
  (`AlgebraicGeometry.ProEtale.sheafComposeForget₂CompComparisonUpperStarIso`) and with
  cohomology, all functors involved being exact.

The final assembly goes through `AlgebraicGeometry.ProEtale.homologyIntegersTowerIsoAux`, stated
for abstract functors, so that the kernel never reassociates compositions of the concrete derived
functors.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite PadicAlgCl

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl l)]

/-- The coefficient ring `Λ = Shrink 𝒪_E` in the universe of sheaves on `u`-schemes. -/
abbrev integersShrink : Type (u + 1) := Shrink.{u + 1} (integers l E)

/-- The ideal `(ℓ)` of `Λ = Shrink 𝒪_E`. -/
noncomputable abbrev integersShrinkIdeal : Ideal (integersShrink.{u} l E) :=
  Ideal.span {(l : integersShrink.{u} l E)}

/-- `Λ ⧸ ℓⁿ ≃ 𝒪_E ⧸ ℓⁿ`, as abelian groups lifted to the universe `u + 1`. -/
noncomputable def quotPowAddEquivULift (n : ℕ) :
    (Ideal.quotPowFunctor (integersShrinkIdeal.{u} l E)).obj (op n) ≃+
      ULift.{u + 1} (integersModPow l E n) :=
  (integersModPowEquivShrinkQuot.{u} l E n).symm.toAddEquiv.trans AddEquiv.ulift.symm

lemma quotPowAddEquivULift_map (n : ℕ) (x : (Ideal.quotPowFunctor
    (integersShrinkIdeal.{u} l E)).obj (op (n + 1))) :
    quotPowAddEquivULift l E n ((Ideal.quotPowFunctor (integersShrinkIdeal.{u} l E)).map
        (homOfLE (n.le_add_right 1)).op x) =
      ULift.up (integersModPowTransition l E n (quotPowAddEquivULift l E (n + 1) x).down) := by
  obtain ⟨y, rfl⟩ := (integersModPowEquivShrinkQuot.{u} l E (n + 1)).surjective x
  apply ULift.ext
  change (integersModPowEquivShrinkQuot.{u} l E n).symm _ =
    integersModPowTransition l E n ((integersModPowEquivShrinkQuot.{u} l E (n + 1)).symm _)
  rw [RingEquiv.symm_apply_apply, RingEquiv.symm_apply_eq,
    integersModPowEquivShrinkQuot_transition]
  rfl

variable (T : Scheme.{u})

/-- **The constant towers agree**: the tower of constant abelian étale sheaves `𝒪_E ⧸ ℓⁿ` is the
abelian tower underlying the constant sheaves of `Λ`-modules `Λ ⧸ ℓⁿ`. -/
noncomputable def constantSheafTowerIsoQuotPow :
    (Ideal.quotPowFunctor (integersShrinkIdeal.{u} l E) ⋙
        constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} (integersShrink.{u} l E))) ⋙
      Etale.moduleAbelianForget (integersShrink.{u} l E) T ≅
      constantSheafTower T (integersModPowTransition l E) :=
  let ι := Etale.constantSheafSheafComposeForget₂Iso (integersShrink.{u} l E) (Y := T)
  let φ (n : ℕ) := ι.app _ ≪≫ (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso
    (quotPowAddEquivULift l E n).toAddCommGrpIso
  let α : (Ideal.quotPowFunctor (integersShrinkIdeal.{u} l E) ⋙
        constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} (integersShrink.{u} l E))) ⋙
      Etale.moduleAbelianForget (integersShrink.{u} l E) T ⟶
      constantSheafTower T (integersModPowTransition l E) :=
    NatTrans.ofOpSequence (fun n ↦ (φ n).hom) fun n ↦ by
      rw [constantSheafTower_map_succ]
      have h1 := ι.hom.naturality ((Ideal.quotPowFunctor (integersShrinkIdeal.{u} l E)).map
        (homOfLE (n.le_add_right 1)).op)
      have h3 : (forget₂ (ModuleCat.{u + 1} (integersShrink.{u} l E)) AddCommGrpCat.{u + 1}).map
          ((Ideal.quotPowFunctor (integersShrinkIdeal.{u} l E)).map
            (homOfLE (n.le_add_right 1)).op) ≫ (quotPowAddEquivULift l E n).toAddCommGrpIso.hom =
          (quotPowAddEquivULift l E (n + 1)).toAddCommGrpIso.hom ≫
            uliftAddHom.{u} (integersModPowTransition l E n) := by
        ext x
        exact congrArg ULift.down (quotPowAddEquivULift_map l E n x)
      simp only [φ, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Functor.comp_map]
      erw [reassoc_of% h1]
      rw [← Functor.map_comp, h3, Functor.map_comp, Category.assoc]
  have : ∀ n, IsIso (α.app n) := fun n ↦ by
    rw [NatTrans.ofOpSequence_app]
    infer_instance
  have := NatIso.isIso_of_isIso_app α
  asIso α

variable {T} {Y : Scheme.{u}} (g : T ⟶ Y)

section

variable {J M₀ M A DA DM DA' DM' DAY DAP AP DMf DMY MY MP : Type*} [Category J] [Category M₀]
  [Category M] [Category A] [Category DA] [Category DM] [Category DA'] [Category DM']
  [Category DAY] [Category DAP] [Category AP] [Category DMf] [Category DMY] [Category MY]
  [Category MP]

/-- The assembly of `AlgebraicGeometry.ProEtale.homologyIntegersTowerIso` from its three
ingredients, over abstract functors: reassociating compositions of abstract functors is cheap
for the kernel, whereas reassociating the concrete derived functors is not. -/
noncomputable def homologyIntegersTowerIsoAux {Q : J ⥤ M₀} {c : M₀ ⥤ M} {f : M ⥤ A}
    {τ : J ⥤ A} {s : A ⥤ DA} {r : DA ⥤ DA'} {ι : DA' ⥤ DAY} {ν : DAY ⥤ DAP} {H : DAP ⥤ AP}
    {s' : M ⥤ DM} {r' : DM ⥤ DM'} {f' : DM' ⥤ DA'} {S : M ⥤ DMf} {R : DMf ⥤ DMY}
    {H' : DMY ⥤ MY} {ν' : MY ⥤ MP} {f'' : MP ⥤ AP}
    (e₁ : (Q ⋙ c) ⋙ f ≅ τ) (e₂ : f ⋙ s ⋙ r ≅ s' ⋙ r' ⋙ f')
    (e₄ : (s' ⋙ r') ⋙ f' ⋙ ι ⋙ ν ⋙ H ≅ (S ⋙ R) ⋙ H' ⋙ ν' ⋙ f'') :
    (τ ⋙ s ⋙ r ⋙ ι ⋙ ν) ⋙ H ≅ (Q ⋙ c ⋙ S ⋙ R ⋙ H') ⋙ ν' ⋙ f'' :=
  Functor.isoWhiskerRight e₁.symm (s ⋙ r ⋙ ι ⋙ ν ⋙ H) ≪≫
    Functor.isoWhiskerLeft (Q ⋙ c) (Functor.isoWhiskerRight e₂ (ι ⋙ ν ⋙ H) ≪≫ e₄)

end

section

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Taking underlying abelian sheaves commutes with `Rg_*` on the bounded below derived
categories, precomposed with the inclusion of sheaves in degree `0`. -/
noncomputable def forgetSingleRightDerivedLowerStarPlusIso :
    Etale.moduleAbelianForget Λ T ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctorPlus ≅
      DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctorPlus ⋙
          (Etale.moduleAbelianForget Λ Y).mapDerivedCategoryPlus :=
  Functor.isoWhiskerRight
      ((Etale.moduleAbelianForget Λ T).mapDerivedCategoryPlusSingleFunctor 0).symm _ ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
      (Etale.moduleAbelianDerivedLowerStarIso Λ g).symm

/-- The degree `k` cohomology of `ν^*` of the underlying abelian complex of `Rg_* F`, for an
étale sheaf `F` of `Λ`-modules, is the abelian sheaf underlying `ν^* Hᵏ(Rg_* F)`. -/
noncomputable def homologyComparisonUpperStarForgetIso (k : ℤ) :
    (DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctorPlus) ⋙
        (Etale.moduleAbelianForget Λ Y).mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι ⋙
          (comparisonUpperStar AddCommGrpCat.{u + 1} Y).mapDerivedCategory ⋙
          DerivedCategory.homologyFunctor _ k ≅
      (DerivedCategory.singleFunctor _ 0 ⋙
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctor) ⋙
          DerivedCategory.homologyFunctor (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) k ⋙
          comparisonUpperStar _ Y ⋙
          sheafCompose (ProEt.topology Y) (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  let fY := Etale.moduleAbelianForget Λ Y
  let ν := comparisonUpperStar AddCommGrpCat.{u + 1} Y
  let Hk := DerivedCategory.homologyFunctor (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) k
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
  Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0 ⋙
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctorPlus) e₃ ≪≫
    Functor.isoWhiskerRight e₅ (Hk ⋙ fY ⋙ ν) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.singleFunctor _ 0 ⋙
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctor ⋙ Hk)
      (sheafComposeForget₂CompComparisonUpperStarIso Λ Y)

end

/-- **The cohomology towers of `R lim_n ν^* Rg_*^{ét}(𝒪_E ⧸ ℓⁿ)`**: the degree `k` cohomology of
the tower `n ↦ ν^* Rg_*^{ét}(𝒪_E ⧸ ℓⁿ)` of complexes of abelian pro-étale sheaves is, naturally in
`n`, the abelian sheaf underlying `ν^* Hᵏ(Rg_* (Λ ⧸ ℓⁿ))` for the tower of étale sheaves of
`Λ`-modules `AlgebraicGeometry.Etale.higherDirectImageQuotPowTower`, `Λ = Shrink 𝒪_E`. -/
noncomputable def homologyIntegersTowerIso (k : ℤ) :
    (constantSheafTower T (integersModPowTransition l E) ⋙
        DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.ι ⋙ (comparisonUpperStar AddCommGrpCat.{u + 1} Y).mapDerivedCategory) ⋙
        DerivedCategory.homologyFunctor _ k ≅
      Etale.higherDirectImageQuotPowTower (integersShrinkIdeal.{u} l E) g k ⋙
        comparisonUpperStar _ Y ⋙
          sheafCompose (ProEt.topology Y)
            (forget₂ (ModuleCat.{u + 1} (integersShrink.{u} l E)) AddCommGrpCat.{u + 1}) :=
  homologyIntegersTowerIsoAux (constantSheafTowerIsoQuotPow l E T)
    (forgetSingleRightDerivedLowerStarPlusIso g _) (homologyComparisonUpperStarForgetIso g _ k)

end AlgebraicGeometry.ProEtale
