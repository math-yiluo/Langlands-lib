/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResiduePullSquareData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResiduePullOrdinaryUnit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResiduePullFlatModelMateNormalized
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Counit

/-! # Comparison equality for the integral residue pull model

Source: Bhatt--Scholze, Remark 6.8.15.
(blueprint: new-integral-residue-pull-flat-model-comparison)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory
open CategoryTheory.Functor
open scoped CategoryTheory.Obj CategoryTheory.Functor
local instance instEssentiallySmallProfinite_integralResiduePullFlatModelComparison
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- The comparison equality in the flat-model theorem.

Source: Bhatt--Scholze, Remark 6.8.15; the derived mate calculation after
restriction/pullback factorization. This is strictly the second conjunct of
`residueExchangePull_flatModel`; its proof transposes the square under the
extension/restriction adjunction, uses the exact pullback factorization and
`residueExchangePull_ordinary_unit`, and then cancels the invertible localization
factor.
(blueprint: new-integral-residue-pull-flat-model-comparison)
-/
theorem residueExchangePull_flatModel_comparison
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) Y)) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (hcolim : ObjectProperty.flat.cochainComplexMinus.colimitsOfShape ℤ P) :
    let H := (HomotopyCategory.quotient _ (.up ℤ)).obj P
    (residueExchangeReduction ℓ E X).map
        ((residueExchangeUpperStarCounit (integralCoeff ℓ E) f).app H) ≫
      (residueExchangeReductionCounit ℓ E X).app
          ((((f)^*⟦integralCoeff ℓ E⟧).mapHomotopyCategory (.up ℤ)).obj H) ≫
      DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory
          (pullIso (integralReductionMap ℓ E) f).hom (.up ℤ)).app H) =
    (residueExchangePullHom ℓ E f).app (DerivedCategory.Qh.obj H) ≫
      (residueExchangeUpperStar
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).map
          ((residueExchangeReductionCounit ℓ E Y).app H) ≫
      ((residueExchangeUpperStarCounit
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).app
          (((Mod.extendScalars
            (coefficientMap (integralReductionMap ℓ E) Y)).mapHomotopyCategory
              (.up ℤ)).obj H)) := by
  dsimp only
  have _ := hP
  have _ := hcolim
  let H := (HomotopyCategory.quotient _ (.up ℤ)).obj P
  have hC : IsIso ((residueExchangeUpperStarCounit
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).app
      (((Mod.extendScalars
        (coefficientMap (integralReductionMap ℓ E) Y)).mapHomotopyCategory
          (.up ℤ)).obj H)) := by
    unfold residueExchangeUpperStarCounit residueExchangeUpperStar
    dsimp only [id_eq]
    infer_instance
  have hn := residueExchangePull_flatModel_mate_normalized ℓ E f H hC
  have hh := congrArg (fun z => z ≫
      (residueExchangeUpperStarCounit
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).app
        (((Mod.extendScalars
          (coefficientMap (integralReductionMap ℓ E) Y)).mapHomotopyCategory
            (.up ℤ)).obj H)) hn
  simp only [Category.assoc] at hh
  simpa [H] using hh

end AlgebraicGeometry.ProEtale.CondensedRing
