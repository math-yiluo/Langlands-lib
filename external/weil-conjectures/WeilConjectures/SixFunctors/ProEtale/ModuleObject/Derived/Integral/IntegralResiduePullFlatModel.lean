/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResiduePullSquareData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResiduePullbackPreservesFlat
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResiduePullFlatModelComparison

/-! # Computing residue pullback on flat complexes -/

@[expose] public section
set_option autoImplicit false
universe u

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.Functor
open scoped CategoryTheory.Obj CategoryTheory.Functor
local instance instEssentiallySmallProfinite_integralResiduePullFlatModel
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- On a flat-resolution complex the derived pull mate is the ordinary scalar comparison.

Source: Bhatt--Scholze, Remark 6.8.15, derived scalar extension on flat resolutions.
(blueprint: new-integral-residue-pull-flat-model)

Proof. Inverse image of sheaves is exact and preserves colimits. Pullback of the
coefficient ring is identified with the coefficient ring on the source. Thus pullback
preserves flat objects (this can be checked on stalks, where it is scalar extension).
The hypothesis presents P as a colimit of bounded above flat complexes. Pullback
preserves that presentation and its terms are flat; therefore its image is K-flat by
`kFlat_mapHomologicalComplex_obj_of_colimitsOfShape`. Consequently the extension counit
on the pulled complex is invertible. Compare the two maps in the second clause by
transposing under extension/restriction of scalars. The derived adjunction unit and
counit factorization equations and the localization factors for exact pullback reduce
this equality to the ordinary scalar square. The ordinary pull isomorphism is the
conjugate of restriction/pushforward. The ordinary unit identity is isolated in
`residueExchangePull_ordinary_unit`; it is the degreewise geometric/scalar mate
compatibility. Applying this identity gives the homotopy comparison;
localization gives the displayed equation. No residue flatness is used: only the input
resolution and its pullback need compute derived scalar extension. -/
theorem residueExchangePull_flatModel
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) Y)) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (hcolim : ObjectProperty.flat.cochainComplexMinus.colimitsOfShape ℤ P) :
    let H := (HomotopyCategory.quotient _ (.up ℤ)).obj P
    IsIso ((residueExchangeReductionCounit ℓ E X).app
        ((((f)^*⟦integralCoeff ℓ E⟧).mapHomotopyCategory (.up ℤ)).obj H)) ∧
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
              (.up ℤ)).obj H))  := by
  dsimp only
  constructor
  · have : (f)^*⟦integralCoeff ℓ E⟧.PreservesFlat :=
      integralResidue_pullback_preservesFlat ℓ E f
    have hk := Functor.kFlat_mapHomologicalComplex_obj_of_colimitsOfShape
      (f)^*⟦integralCoeff ℓ E⟧ hcolim
    unfold residueExchangeReductionCounit residueExchangeReduction integralReduction
    dsimp only [id_eq]
    exact (Mod.extendScalars (coefficientMap (integralReductionMap ℓ E) X))
      |>.isIso_leftDerivedFunctorCounit_app_of_kFlat _ hk
  · exact residueExchangePull_flatModel_comparison ℓ E f P hP hcolim

end AlgebraicGeometry.ProEtale.CondensedRing
