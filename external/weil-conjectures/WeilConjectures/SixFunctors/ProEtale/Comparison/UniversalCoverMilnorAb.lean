/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.UniversalCoverMilnor

/-!
# The Milnor sequence on the universal cover, for abelian sheaves

The abelian version of `WeilConjectures.SixFunctors.ProEtale.Comparison.UniversalCoverMilnor`, for
derived limits of towers of complexes of abelian pro-étale sheaves (such as
`Rg_* 𝒪_{E,T} ≅ R lim_n ν^* Rg_*^{ét}(𝒪_E ⧸ ℓⁿ)`,
`isHomotopyLimit_comparisonUpperStar_rightDerivedLowerStar_constantSheafTower`)
whose cohomology towers are, after pullback to the universal cover `p : Ỹ_y ⟶ Y`, the abelian
towers underlying `p^* ν^* Hₙ` for towers `H` of étale sheaves of `Λ`-modules with finite locally
constant underlying sheaves of sets (`AlgebraicGeometry.Scheme.IsSetFLC`):

- `AlgebraicGeometry.Scheme.UniversalCovers.isLimitHomologyUpperStarAbOfIsSetFLC`:
  `Hⁱ(p^* R lim F) = lim_n Hⁱ(p^* Fₙ)`;
- `AlgebraicGeometry.Scheme.UniversalCovers.nonempty_iso_homologyUpperStar_continuousMapAddSheaf`:
  `Hⁱ(p^* R lim F) ≅ C(-, lim_n (Hₙ)_y)`, the integral identification on the universal cover.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

section Forget

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]

/-- Taking underlying abelian sheaves of pro-étale sheaves of `Λ`-modules is left exact. -/
instance ProEt.preservesFiniteLimits_sheafCompose_forget₂ :
    PreservesFiniteLimits (sheafCompose (ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) := by
  have : PreservesFiniteLimits (sheafCompose (ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ⋙ sheafToPresheaf _ _) :=
    inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)

/-- Taking underlying abelian sheaves of pro-étale sheaves of `Λ`-modules preserves
epimorphisms, which are the locally surjective morphisms. -/
instance ProEt.preservesEpimorphisms_sheafCompose_forget₂ :
    (sheafCompose (ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).PreservesEpimorphisms :=
  ⟨fun f _ ↦ by
    have hf : Sheaf.IsLocallySurjective f := (Sheaf.isLocallySurjective_iff_epi' (φ := f)).2
      inferInstance
    have : Sheaf.IsLocallySurjective ((sheafCompose (ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map f) :=
      ⟨fun s ↦ hf.imageSieve_mem s⟩
    exact Sheaf.epi_of_isLocallySurjective _⟩

end Forget

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] (U : Scheme.UniversalCovers Y Ω)
  (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) {Λ : Type (u + 1)} [Ring Λ]

/-- The abelian tower underlying the pullback to the universal cover of a tower of locally
constant sheaves with finite stalks is Mittag-Leffler. -/
theorem UniversalCovers.isMittagLefflerTower_comparisonUpperStar_forget₂
    (H : ℕᵒᵖ ⥤ Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hH : ∀ n : ℕ, IsSetFLC (H.obj (op n))) :
    IsMittagLefflerTower (H ⋙ ProEtale.comparisonUpperStar _ Y ⋙
      ProEtale.upperStar (ModuleCat.{u + 1} Λ) (U.proj y) ⋙
        sheafCompose (ProEt.topology (U.cover y))
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) :=
  (U.isMittagLefflerTower_comparisonUpperStar y H hH).map
    (sheafCompose (ProEt.topology (U.cover y))
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))

open Pretriangulated in
/-- **The Milnor sequence on the universal cover, for abelian sheaves.** Let `c` be a homotopy
limit cone over a tower `F` in the derived category of abelian pro-étale sheaves on `Y` such that,
after pullback to the universal cover `Ỹ_y`, the degree `i - 1` cohomology tower is the abelian
tower underlying `p^* ν^* Hₙ` for a tower `H` of étale sheaves of `Λ`-modules with finite locally
constant underlying sheaves of sets. Then `Hⁱ(p^* R lim F) = lim_n Hⁱ(p^* Fₙ)`. -/
noncomputable def UniversalCovers.isLimitHomologyUpperStarAbOfIsSetFLC
    {F : ℕᵒᵖ ⥤ DerivedCategory (Sheaf (ProEt.topology Y) Ab.{u + 1})}
    {c : Cone F} (hc : IsHomotopyLimit c) (i : ℤ)
    (H : ℕᵒᵖ ⥤ Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hH : ∀ n : ℕ, IsSetFLC (H.obj (op n)))
    (e : (F ⋙ (ProEtale.upperStar Ab.{u + 1} (U.proj y)).mapDerivedCategory) ⋙
        DerivedCategory.homologyFunctor _ (i - 1) ≅
      H ⋙ ProEtale.comparisonUpperStar _ Y ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} Λ) (U.proj y) ⋙
          sheafCompose (ProEt.topology (U.cover y))
            (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) :
    IsLimit ((DerivedCategory.homologyFunctor _ i).mapCone
      ((ProEtale.upperStar Ab.{u + 1} (U.proj y)).mapDerivedCategory.mapCone c)) :=
  have := U.weaklyEtale_proj y
  DerivedCategory.isLimitHomologyFunctorMapConeOfIsHomotopyLimitOfIsMittagLefflerTower
    ProEt.epi_π_app_zero_of_epi_ab
    (ProEtale.isHomotopyLimit_upperStar_mapDerivedCategory_mapCone (U.proj y) hc) i
    ((U.isMittagLefflerTower_comparisonUpperStar_forget₂ y H hH).of_iso e.symm)

open Pretriangulated in
/-- **The integral identification on the universal cover.** In the situation of
`AlgebraicGeometry.Scheme.UniversalCovers.isLimitHomologyUpperStarAbOfIsSetFLC`, if moreover the
degree `i` cohomology tower is, after pullback to `Ỹ_y`, the abelian tower underlying `p^* ν^* H'ₙ`
for a second such tower `H'`, then `Hⁱ(p^* R lim F) ≅ C(-, lim_n (H'ₙ)_y)`, the finite stalks
being made discrete groups. -/
theorem UniversalCovers.nonempty_iso_homologyUpperStar_continuousMapAddSheaf
    {F : ℕᵒᵖ ⥤ DerivedCategory (Sheaf (ProEt.topology Y) Ab.{u + 1})}
    {c : Cone F} (hc : IsHomotopyLimit c) (i : ℤ)
    (H H' : ℕᵒᵖ ⥤ Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hH : ∀ n : ℕ, IsSetFLC (H.obj (op n))) (hH' : ∀ n : ℕ, IsSetFLC (H'.obj (op n)))
    (e : (F ⋙ (ProEtale.upperStar Ab.{u + 1} (U.proj y)).mapDerivedCategory) ⋙
        DerivedCategory.homologyFunctor _ (i - 1) ≅
      H ⋙ ProEtale.comparisonUpperStar _ Y ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} Λ) (U.proj y) ⋙
          sheafCompose (ProEt.topology (U.cover y))
            (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
    (e' : (F ⋙ (ProEtale.upperStar Ab.{u + 1} (U.proj y)).mapDerivedCategory) ⋙
        DerivedCategory.homologyFunctor _ i ≅
      H' ⋙ ProEtale.comparisonUpperStar _ Y ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} Λ) (U.proj y) ⋙
          sheafCompose (ProEt.topology (U.cover y))
            (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) :
    let St := (pointSmallEtale (U.pt y ≫ U.proj y)).sheafFiber (A := ModuleCat.{u + 1} Λ)
    have (n : ℕ) : Finite (St.obj (H'.obj (op n))) := (hH' n).finite_sheafFiber _
    Nonempty ((DerivedCategory.homologyFunctor _ i).obj
        ((ProEtale.upperStar Ab.{u + 1} (U.proj y)).mapDerivedCategory.obj c.pt) ≅
      ProEtale.continuousMapAddSheaf (U.cover y)
        (ProEtale.towerLimitAddSubgroup (Qs := fun n ↦ DiscreteShrink (St.obj (H'.obj (op n))))
          (fun n ↦ DiscreteShrink.map
            (St.map (H'.map (homOfLE (n.le_add_right 1)).op)).hom.toAddMonoidHom))) := by
  intro St hfin
  obtain ⟨c', hpt, ⟨hc'⟩⟩ := U.exists_isLimit_towerComparisonUpperStar' y H' hH'
  exact ⟨IsLimit.conePointsIsoOfNatIso (U.isLimitHomologyUpperStarAbOfIsSetFLC y hc i H hH e)
    hc' e' ≪≫ eqToIso hpt⟩

end AlgebraicGeometry.Scheme
