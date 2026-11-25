/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.UniversalCoverSetFLC
public import WeilConjectures.Algebra.Category.ModuleCat.StableImageTower
public import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStarHomotopyLimit
public import WeilConjectures.Algebra.Homology.DerivedCategory.MittagLefflerTower
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Mittag-Leffler and the Milnor sequence on the universal cover

For a tower `H` of étale sheaves of `Λ`-modules on `Y` with finite locally constant underlying
sheaves of sets (`AlgebraicGeometry.Scheme.IsSetFLC`):

- `AlgebraicGeometry.Scheme.UniversalCovers.isMittagLefflerTower_comparisonUpperStar`: the tower
  `p^* ν^* Hₙ` on the universal cover `Ỹ_y` is Mittag-Leffler, being a tower of constant sheaves
  with finite values;
- `AlgebraicGeometry.Scheme.UniversalCovers.isLimitHomologyUpperStarOfIsSetFLC`: hence, for a
  derived limit `c` of a tower `F` in `D(Y_proét, Λ)` whose degree `i - 1` cohomology tower is
  `ν^* Hₙ`, `Hⁱ(p^* R lim F) = lim Hⁱ(p^* Fₙ)` on `Ỹ_y`.

This avoids proving that images of finite locally constant sheaves are finite locally constant:
Mittag-Leffler is only needed after pulling back to the trivialising cover `Ỹ_y`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] (U : Scheme.UniversalCovers Y Ω)
  (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) {Λ : Type (u + 1)} [Ring Λ]

/-- **Towers of locally constant sheaves with finite stalks are Mittag-Leffler on the universal
cover**: the pullback of the tower `ν^* Hₙ` to the universal cover `Ỹ_y` is the tower of constant
sheaves with the finite stalks `(Hₙ)_y` as values, which is Mittag-Leffler, finite modules being
Artinian. -/
theorem UniversalCovers.isMittagLefflerTower_comparisonUpperStar
    (H : ℕᵒᵖ ⥤ Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hH : ∀ n : ℕ, IsSetFLC (H.obj (op n))) :
    IsMittagLefflerTower
      (H ⋙ ProEtale.comparisonUpperStar _ Y ⋙ ProEtale.upperStar _ (U.proj y)) := by
  have (n : ℕ) : Finite (((H ⋙ (pointSmallEtale (U.pt y ≫ U.proj y)).sheafFiber).obj (op n))) :=
    (hH n).finite_sheafFiber _
  exact (ModuleCat.isMittagLefflerTower_comp_constantSheaf_of_finite
    (H ⋙ (pointSmallEtale (U.pt y ≫ U.proj y)).sheafFiber)
    (ProEt.topology (U.cover y))).of_iso
    (U.towerComparisonUpperStarIsoConstantSheaf' y Λ H hH).symm

open Pretriangulated in
/-- **The Milnor sequence on the universal cover for towers with locally constant cohomology with
finite stalks.** Let `c` be a homotopy limit cone (`R lim`) over a tower `F` in the derived
category of pro-étale sheaves of `Λ`-modules on `Y`, whose degree `i - 1` cohomology tower is
`ν^* Hₙ` for a tower `H` of étale sheaves with finite locally constant underlying sheaves of sets.
Then after pulling back to the universal cover `Ỹ_y`,
`Hⁱ(p^* R lim F) = lim_n Hⁱ(p^* Fₙ)`: pullback preserves the homotopy limit
(`AlgebraicGeometry.ProEtale.isHomotopyLimit_upperStar_mapDerivedCategory_mapCone_moduleCat`), and
the pulled back degree `i - 1` tower is Mittag-Leffler
(`AlgebraicGeometry.Scheme.UniversalCovers.isMittagLefflerTower_comparisonUpperStar`). -/
noncomputable def UniversalCovers.isLimitHomologyUpperStarOfIsSetFLC {Λ : Type (u + 1)}
    [CommRing Λ] {F : ℕᵒᵖ ⥤ DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    {c : Cone F} (hc : IsHomotopyLimit c) (i : ℤ)
    (H : ℕᵒᵖ ⥤ Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hH : ∀ n : ℕ, IsSetFLC (H.obj (op n)))
    (e : F ⋙ DerivedCategory.homologyFunctor _ (i - 1) ≅
      H ⋙ ProEtale.comparisonUpperStar _ Y) :
    IsLimit ((DerivedCategory.homologyFunctor _ i).mapCone
      ((ProEtale.upperStar (ModuleCat.{u + 1} Λ) (U.proj y)).mapDerivedCategory.mapCone c)) :=
  have := U.weaklyEtale_proj y
  have hc' := ProEtale.isHomotopyLimit_upperStar_mapDerivedCategory_mapCone_moduleCat
    (U.proj y) Λ hc
  let Φ := ProEtale.upperStar (ModuleCat.{u + 1} Λ) (U.proj y)
  have hML : IsMittagLefflerTower ((F ⋙ Φ.mapDerivedCategory) ⋙
      DerivedCategory.homologyFunctor _ (i - 1)) :=
    (U.isMittagLefflerTower_comparisonUpperStar y H hH).of_iso
      ((Functor.isoWhiskerRight e Φ).symm ≪≫
        Functor.isoWhiskerLeft F (Φ.mapDerivedCategoryHomologyFunctorIso (i - 1)))
  DerivedCategory.isLimitHomologyFunctorMapConeOfIsHomotopyLimitOfIsMittagLefflerTower
    ProEt.epi_π_app_zero_of_epi hc' i hML

end AlgebraicGeometry.Scheme
