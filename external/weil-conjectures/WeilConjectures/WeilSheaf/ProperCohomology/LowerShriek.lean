/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.LowerStarComp
public import WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion

/-!
# Compactly supported direct image of a proper scheme

For a proper `k₀`-scheme `a : X ⟶ Spec k₀` the direct image with compact support
`Ra_! = Rg_* ∘ i_!`, for the chosen compactification `X ⟶[i] Z ⟶[g] Spec k₀`, is the derived
direct image `Ra_*`.

## Main statements

- `AlgebraicGeometry.WeilComplex.derivedLowerShriekObjIsoOfIsProper`: `Ra_! K ≅ Ra_* K` for `X`
  proper.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open ProEtale Endofunctor

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
variable {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))]

attribute [local instance] Compactification.over

variable [Fact (ringChar k₀ ≠ l)]

/-- **For a proper `k₀`-scheme, compactly supported direct image is direct image**: for the
chosen compactification `X ⟶[i] Z ⟶[g] Spec k₀` of the proper structure morphism `a`, the open
immersion `i` is universally closed, so that `Ra_! K = Rg_*(i_! K) ≅ Rg_*(i_* K) ≅ Ra_* K`. -/
noncomputable def WeilComplex.derivedLowerShriekObjIsoOfIsProper
    [IsProper (X ↘ Spec (CommRingCat.of k₀))] (K : WeilComplex k₀ l X) :
    (WeilComplex.derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj K ≅
      (WeilComplex.derivedLowerStar (X ↘ Spec (CommRingCat.of k₀))).obj K := by
  let c := HasCompactification.compactification (X ↘ Spec (CommRingCat.of k₀))
    (hf := hasCompactification_of_over (k₀ := k₀) _)
  have : IsProper c.i := c.isProper_openImmersion inferInstance
  have : IsOpenImmersion c.i := c.isOpenImmersion
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  refine ObjectProperty.isoMk _ ?_
  change (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.obj
    ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategory.obj K.obj) ≅ _
  exact (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.mapIso
      ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).rightDerivedFunctorIsoMapDerivedCategory.app
        K.obj).symm ≪≫
    (IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompIso
      (ProEtale.adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso l c.i
        (comp_over c.i _))
      (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l c.g (comp_over c.g _))).symm.app
        K.obj ≪≫
    (Functor.rightDerivedFunctorNatIso (Functor.isoWhiskerRight
      (asIso (ProEtaleWeilSheaf.extensionByZeroToLowerStar k₀ l c.i))
      (ProEtaleWeilSheaf.lowerStar k₀ l c.g))).app K.obj ≪≫
    (Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarCompIso k₀ l c.i c.g)).app
      K.obj ≪≫
    (Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarCongr k₀ l c.comm.symm)).app
      K.obj

end AlgebraicGeometry
