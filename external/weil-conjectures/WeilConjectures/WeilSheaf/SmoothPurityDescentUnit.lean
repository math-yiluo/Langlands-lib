/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityNativeDescent
public import WeilConjectures.WeilSheaf.CondensedModelGeometricFiberPullback
public import WeilConjectures.WeilSheaf.UpperStarConstant
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelUpperStarUnit
public import WeilConjectures.Tactic.ExactModProofs

/-!
# The constant Weil sheaf as finite-base descent

The canonical unit comparison for pullback respects the Frobenius descent datum.
The coefficient equivalence and the degree-zero embedding then identify native
descent of the finite-base unit with the constant Weil complex.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Endofunctor
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- Unit pullback is compatible with the descent isomorphism of an automorphism
over the base. -/
lemma adicUpperStarUnitIso_descent {X Y : Scheme.{u}}
    (p : X ⟶ Y) (a : X ⟶ X) (h : a ≫ p = p) :
    (adicUpperStarComp l a p).inv.app (AdicSheaf.unit l Y) ≫
        (adicUpperStarCongr l h).hom.app (AdicSheaf.unit l Y) ≫
        (adicUpperStarUnitIso l p).hom =
      (a)^*ᵃ[l].map (adicUpperStarUnitIso l p).hom ≫
        (adicUpperStarUnitIso l a).hom := by
  have hs : (upperStarComp (WeilCoefficients.{u} l) a p).inv.app (adicConstantSheaf l Y) ≫
      (upperStarCongr (WeilCoefficients.{u} l) h).hom.app (adicConstantSheaf l Y) ≫
        upperStarAdicConstantSheafHom l p =
      (a)^*[WeilCoefficients.{u} l].map (upperStarAdicConstantSheafHom l p) ≫
        upperStarAdicConstantSheafHom l a := by
    rw [upperStarCongr_hom_app_comp_upperStarAdicConstantSheafHom,
      ← upperStarAdicConstantSheafHom_comp, Iso.inv_hom_id_app_assoc]
  apply Mod.hom_ext
  simp only [Mod.comp_hom', adicUpperStarComp_inv_app_hom,
    adicUpperStarCongr_hom_app_hom, adicUpperStar_map_hom,
    adicUpperStarUnitIso, Mod.regularIsoOfIsIso_hom_hom]
  exact_mod_proofs hs

/-- Switching between pullback and inverse pushforward preserves the unit map. -/
lemma adicUpperStarIsoLowerStarInv_hom_comp_unit {X Y : Scheme.{u}} (e : X ≅ Y) :
    (adicUpperStarIsoLowerStarInv l e).hom.app (AdicSheaf.unit l Y) ≫
        (adicLowerStarUnitIso l e.symm).hom = (adicUpperStarUnitIso l e.hom).hom := by
  apply Mod.hom_ext
  rw [Mod.comp_hom', adicUpperStarIsoLowerStarInv_hom_app_hom,
    adicLowerStarUnitIso_hom_hom]
  exact upperStarIsoLowerStarInv_hom_app_comp_adicConstantSheafLowerStarIso_hom l e

/-- The unit descent equation in inverse-pushforward coordinates. Keeping the
automorphism abstract avoids unfolding the geometric Frobenius while cancelling
the pullback/pushforward comparison. -/
lemma adicUpperStarUnitIso_descent_inv {X Y : Scheme.{u}}
    (p : X ⟶ Y) (e : X ≅ X) (h : e.hom ≫ p = p) :
    (e.inv)_*ᵃ[l].map (adicUpperStarUnitIso l p).hom ≫
        (adicLowerStarUnitIso l e.symm).hom =
      (adicUpperStarIsoLowerStarInv l e).inv.app ((p)^*ᵃ[l].obj (AdicSheaf.unit l Y)) ≫
        (adicUpperStarComp l e.hom p).inv.app (AdicSheaf.unit l Y) ≫
        (adicUpperStarCongr l h).hom.app (AdicSheaf.unit l Y) ≫
        (adicUpperStarUnitIso l p).hom := by
  rw [← cancel_epi ((adicUpperStarIsoLowerStarInv l e).hom.app
    ((p)^*ᵃ[l].obj (AdicSheaf.unit l Y)))]
  rw [← NatTrans.naturality_assoc]
  simp only [Iso.hom_inv_id_app_assoc, adicUpperStarIsoLowerStarInv_hom_comp_unit]
  exact (adicUpperStarUnitIso_descent p e.hom h).symm

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- Descent of the native finite-base unit is the constant native Weil sheaf. -/
noncomputable def geometricFiberPullbackUnitIso :
    (geometricFiberPullback k₀ l X).obj (AdicSheaf.unit l X) ≅ adicConstant k₀ l X :=
  IsoAlgebra.isoMk (adicUpperStarUnitIso l
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj) (by
      change ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*ᵃ[l].map
        (adicUpperStarUnitIso l (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).hom ≫
          (adicLowerStarUnitIso l
            (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.symm).hom =
        (geometricFiberPullbackFrobeniusIso k₀ l X).hom.app (AdicSheaf.unit l X) ≫
          (adicUpperStarUnitIso l (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).hom
      dsimp only [geometricFiberPullbackFrobeniusIso, Iso.trans_hom, NatTrans.comp_app,
        Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom]
      simp only [Category.assoc]
      exact adicUpperStarUnitIso_descent_inv
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso
        (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj _))

/-- The native constant sheaf, in condensed coordinates, is descent of the unit. -/
noncomputable def toCondensedAdicConstantDescentIso :
    (toCondensed k₀ l X).obj (adicConstant k₀ l X) ≅
      (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀))).obj (𝟙_ _) :=
  (toCondensed k₀ l X).mapIso (geometricFiberPullbackUnitIso k₀ l X).symm ≪≫
    (geometricFiberPullbackCompToCondensedIso k₀ l X).app (AdicSheaf.unit l X) ≪≫
    (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
      (X ↘ Spec (CommRingCat.of k₀))).mapIso (adicSheafEquivCondensedModTensorUnitIso l X)

end AlgebraicGeometry.ProEtaleWeilSheaf

namespace AlgebraicGeometry.WeilComplex

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

local instance instLocallyOfFiniteType_smoothPurityDescentUnit
    : LocallyOfFiniteType (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)))
local instance instQuasiCompactHomScheme_smoothPurityDescentUnit
    : QuasiCompact (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (QuasiCompact (X ↘ Spec (CommRingCat.of k₀)))
/-- Native descent of the finite-base tensor unit is the constant Weil complex. -/
noncomputable def finiteBaseNativeDescentUnitIso :
    letI : (boundedConstructible
        (condensedRingObj (Profinite.padicAlgClRingObj l) X)).IsMonoidal :=
      CondensedRing.isMonoidal_boundedConstructible l (Over.mk (X ↘ Spec (CommRingCat.of k₀)))
    letI := ObjectProperty.fullMonoidalSubcategory
      (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l) X))
    (finiteBaseNativeDescent (k₀ := k₀) (l := l) (X := X)).obj (𝟙_ _) ≅
      WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X) :=
  letI : (boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj l) X)).IsMonoidal :=
    CondensedRing.isMonoidal_boundedConstructible l (Over.mk (X ↘ Spec (CommRingCat.of k₀)))
  letI := ObjectProperty.fullMonoidalSubcategory
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l) X))
  ObjectProperty.isoMk _
    ((ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.preimageIso
      ((finiteBaseNativeDescentComparison (k₀ := k₀) (l := l) (X := X)).app (𝟙_ _) ≪≫
        (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
          (X ↘ Spec (CommRingCat.of k₀))).mapDerivedCategory.mapIso
            ((Functor.Monoidal.εIso (boundedConstructible
              (condensedRingObj (Profinite.padicAlgClRingObj l) X)).ι).symm ≪≫
              (DerivedCategory.singleFunctorObjUnitIso _).symm) ≪≫
        (derivedEquivCondensedSingleIso (WeilSheaf.adicConstant k₀ l X) (𝟙_ _)
          (ProEtaleWeilSheaf.toCondensedAdicConstantDescentIso k₀ l X)).symm))

end AlgebraicGeometry.WeilComplex
