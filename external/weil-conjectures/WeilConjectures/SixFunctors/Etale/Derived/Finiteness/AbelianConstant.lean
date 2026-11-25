/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage
public import WeilConjectures.ConstructibleSheaf.FiniteEtalePushforward
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.SecondStep
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageAmplitude

/-!
# Torsion finiteness for constant abelian étale sheaves

The finiteness theorem for torsion étale coefficients
(`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent`)
is stated for sheaves of `Λ`-modules. This file transports it to the constant *abelian* sheaf
`Λ`, which is what appears in the comparison `Rg_* C(-, 𝒪_E ⧸ ℓⁿ) ≅ ν^* Rg_*^{ét}(𝒪_E ⧸ ℓⁿ)` of
`WeilConjectures.SixFunctors.ProEtale.Adic.IntegersSheafLowerStar`:

- `AlgebraicGeometry.Etale.isConstructibleSheaf_constantSheaf_self`: the constant sheaf `Λ` of
  `Λ`-modules is constructible;
- `AlgebraicGeometry.Etale.exists_boundedConstructible_iso_rightDerivedLowerStar_constantSheaf_ab`:
  `R⁺g_*` of the constant abelian sheaf `Λ` is the underlying complex of abelian sheaves of the
  bounded constructible complex `R⁺g_* Λ` of sheaves of `Λ`-modules, using that taking
  underlying abelian sheaves commutes with derived direct images
  (`AlgebraicGeometry.Etale.moduleAbelianDerivedLowerStarIso`).
- `AlgebraicGeometry.Etale.isGE_and_isLE_rightDerivedLowerStar_constantSheaf_ab`: for a torsion
  ring `Λ`, `R⁺g_*` of the constant abelian sheaf `Λ` lies in degrees `[0, 2d]` when
  `dim T ≤ d`, by `AlgebraicGeometry.Etale.isLE_rightDerivedLowerStar_obj`.

The étale finiteness and amplitude theorems used here rest on sorry leaves of other subsections.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

omit [Finite Λ] in
/-- The constant étale sheaf with value a ring `Λ` is constructible. -/
lemma isConstructibleSheaf_constantSheaf_self (X : Scheme.{u}) :
    IsConstructibleSheaf ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (ModuleCat.of Λ Λ)) := by
  have := isFiniteLocallyConstantSheaf_lowerStar_constantSheaf (𝟙 X) (ModuleCat.of Λ Λ)
  have := Scheme.IsConstructibleSheaf.of_isFiniteLocallyConstantSheaf
    ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (𝟙 X)).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)))
  have : IsConstructibleSheaf ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (𝟙 X)).obj
      ((presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        ((Functor.const _).obj (ModuleCat.of Λ Λ)))) := this
  exact IsConstructibleSheaf.of_iso ((Etale.lowerStarId _ X).app _)

variable {Λ} {k : Type u} [Field k] {T Y : Scheme.{u}}

omit [Finite Λ] in
/-- `R⁺g_*` of the constant abelian étale sheaf `Λ` is the underlying complex of abelian sheaves
of `R⁺g_* Λ` computed with `Λ`-module coefficients. -/
noncomputable def rightDerivedLowerStarConstantSheafAbIso (g : T ⟶ Y) :
    (Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of Λ))) ≅
      (moduleAbelianForget Λ Y).mapDerivedCategoryPlus.obj
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
              (ModuleCat.of Λ Λ)))) :=
  let V := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  have : (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{0, 0, u + 1} (Int.castRingHom Λ)).isLeftAdjoint
  have : V.IsLeftAdjoint := inferInstanceAs (ModuleCat.restrictScalars.{u + 1}
    (Int.castRingHom Λ) ⋙ forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsLeftAdjoint
  have : T.smallEtaleTopology.PreservesSheafification V :=
    Sheaf.preservesSheafification_of_adjunction _ (Adjunction.ofIsLeftAdjoint V)
  (Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctorPlus.mapIso
      ((DerivedCategory.Plus.singleFunctor _ 0).mapIso
          ((constantCommuteCompose T.smallEtaleTopology V).app (ModuleCat.of Λ Λ)).symm ≪≫
        (((moduleAbelianForget Λ T).mapDerivedCategoryPlusSingleFunctor 0).app _).symm) ≪≫
    ((moduleAbelianDerivedLowerStarIso Λ g).app _).symm

/-- **The torsion bridge**: for a finite ring `Λ` whose exponent is invertible on `T`, and
`g : T ⟶ Y` quasi-compact between schemes locally of finite type over a field (`Y`
quasi-compact), the derived direct image of the constant *abelian* étale sheaf `Λ` is the
underlying complex of abelian sheaves of a bounded constructible complex of sheaves of
`Λ`-modules, namely `R⁺g_* Λ` computed with `Λ`-module coefficients
(`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent`
and `AlgebraicGeometry.Etale.moduleAbelianDerivedLowerStarIso`). -/
theorem exists_boundedConstructible_iso_rightDerivedLowerStar_constantSheaf_ab (g : T ⟶ Y)
    [QuasiCompact g] [HasInvertibleExponent Λ T] (aT : T ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aT] [LocallyOfFiniteType aY] [QuasiCompact aY] (hg : g ≫ aY = aT) :
    ∃ K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
        (DerivedCategory.Plus.ι.obj K) ∧
      Nonempty ((Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
              (AddCommGrpCat.of Λ))) ≅
        (moduleAbelianForget Λ Y).mapDerivedCategoryPlus.obj K) := by
  let C := (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)
  have := isConstructibleSheaf_constantSheaf_self Λ T
  refine ⟨(Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctorPlus.obj
    ((DerivedCategory.Plus.singleFunctor _ 0).obj C), ?_, ⟨?_⟩⟩
  · refine (Etale.DerivedCategory.boundedConstructible _ Y).prop_of_iso
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctorPlusCompatibility.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj C)).symm ?_
    exact boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent Λ g aT aY hg _
      (DerivedCategory.boundedConstructible_singleFunctor_obj C 0)
  · exact rightDerivedLowerStarConstantSheafAbIso g

omit [Finite Λ] in
/-- **Amplitude of `Rg_* Λ` for a torsion ring `Λ`**: for `g : T ⟶ Y` between schemes of finite
type over a field with `dim T ≤ d`, the derived direct image of the constant abelian étale sheaf
`Λ` lies in degrees `[0, 2d]`. -/
theorem isGE_and_isLE_rightDerivedLowerStar_constantSheaf_ab (hΛ : IsAddTorsion Λ)
    (aT : T ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aT] [QuasiCompact aT]
    [LocallyOfFiniteType aY] [QuasiCompact aY] (g : T ⟶ Y) (hg : g ≫ aY = aT) (d : ℕ)
    (hd : topologicalKrullDim T ≤ (d : WithBot ℕ∞)) :
    (DerivedCategory.Plus.ι.obj
      ((Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
            (AddCommGrpCat.of Λ))))).IsGE 0 ∧
    (DerivedCategory.Plus.ι.obj
      ((Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
            (AddCommGrpCat.of Λ))))).IsLE (2 * (d : ℤ)) := by
  let C := (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)
  let K := (DerivedCategory.singleFunctor
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj C
  let e : DerivedCategory.Plus.ι.obj
      ((Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of Λ)))) ≅
      (moduleAbelianForget Λ Y).mapDerivedCategory.obj
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctor.obj K) :=
    DerivedCategory.Plus.ι.mapIso (rightDerivedLowerStarConstantSheafAbIso g) ≪≫
      (moduleAbelianForget Λ Y).mapDerivedCategory.mapIso
        (((Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctorPlusCompatibility).app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj C))
  have : K.IsGE 0 := (inferInstance : ((DerivedCategory.singleFunctor _ 0).obj C).IsGE 0)
  have : K.IsLE 0 := (inferInstance : ((DerivedCategory.singleFunctor _ 0).obj C).IsLE 0)
  have h₁ := isGE_rightDerivedLowerStar_obj Λ g K 0
  have h₂ := isLE_rightDerivedLowerStar_obj Λ hΛ aT aY g hg d hd K 0
  rw [zero_add] at h₂
  have := (moduleAbelianForget Λ Y).isGE_mapDerivedCategory_obj
    ((Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctor.obj K) 0
  have := (moduleAbelianForget Λ Y).isLE_mapDerivedCategory_obj
    ((Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctor.obj K) (2 * (d : ℤ))
  exact ⟨DerivedCategory.TStructure.t.isGE_of_iso e.symm 0,
    DerivedCategory.TStructure.t.isLE_of_iso e.symm _⟩

end AlgebraicGeometry.Etale
