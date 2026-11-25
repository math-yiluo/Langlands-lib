/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafOperations
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Shift
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange

set_option linter.privateModule false

/-! # Scalar-compatible open base change for condensed coefficients

Source: blueprint main-20261015, proposition-extension-zero-restriction-closed-subscheme, proof (4),
and sk-prop-sfb-cartesian-coefficients/lem-sfb-eta-comp; exact localization uses
Stacks Project, Tag 04VG, lemma-properties-left-localization.
(blueprint: lem-sfb-condensed-open-square-scalar-comparison)

The pullback square comparison and its complex-level map are real constructions from
existing module pullbacks, their specified compositors, and termwise application.
The theorem retains the specified open adjunctions and ordinary unbounded derived categories.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] ProEtale.upperStarCompIso ProEtale.upperStarCongr
attribute [local irreducible] ProEtale.upperStarFromPointComp

private theorem upperStarCongr_hom_app {S T : Scheme.{u}} {f g : S ⟶ T}
    (h : f = g) (M : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) :
    (ProEtale.upperStarCongr Ab.{u + 1} h).hom.app M =
      (eqToHom (congrArg (ProEtale.upperStar Ab.{u + 1}) h)).app M := by
  subst h
  unfold ProEtale.upperStarCongr
  rfl

private theorem upperStarCongr_symm {S T : Scheme.{u}} {f g : S ⟶ T}
    (h : f = g) : (ProEtale.upperStarCongr Ab.{u + 1} h).symm =
      ProEtale.upperStarCongr Ab.{u + 1} h.symm := by
  subst h
  unfold ProEtale.upperStarCongr
  rfl

private theorem upperStarCompIso_symm {S X Y Z : Scheme.{u}}
    (a : S ⟶ X) (b : X ⟶ Z) (c : S ⟶ Y) (d : Y ⟶ Z) (h : a ≫ b = c ≫ d) :
    (ProEtale.upperStarCompIso Ab.{u + 1} h).symm =
      ProEtale.upperStarCompIso Ab.{u + 1} h.symm := by
  simp only [upperStarCompIso, Iso.trans_symm, Iso.symm_symm_eq, upperStarCongr_symm,
    Iso.trans_assoc]

private theorem upperStarCompIso_inv_app {S X Y Z : Scheme.{u}}
    (a : S ⟶ X) (b : X ⟶ Z) (c : S ⟶ Y) (d : Y ⟶ Z) (h : a ≫ b = c ≫ d)
    (M : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :
    (ProEtale.upperStarCompIso Ab.{u + 1} h).inv.app M =
      (ProEtale.upperStarComp Ab.{u + 1} c d).inv.app M ≫
        (eqToHom (congrArg (ProEtale.upperStar Ab.{u + 1}) h.symm)).app M ≫
        (ProEtale.upperStarComp Ab.{u + 1} a b).hom.app M := by
  change (ProEtale.upperStarCompIso Ab.{u + 1} h).symm.hom.app M = _
  rw [upperStarCompIso_symm]
  unfold ProEtale.upperStarCompIso
  dsimp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [upperStarCongr_hom_app]

private theorem compFromFive {C : Type*} [Category C]
    {A B C₁ D E F : C} {s : A ⟶ D} {a : A ⟶ B} {b : B ⟶ C₁}
    {c : C₁ ⟶ D} {d : D ⟶ E} {e : E ⟶ F} {f : A ⟶ F}
    (h : s = a ≫ b ≫ c) (hh : a ≫ b ≫ c ≫ d ≫ e = f) : s ≫ d ≫ e = f := by
  rw [h, Category.assoc, Category.assoc]
  exact hh

private theorem coefficientMap_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    {S T : Scheme.{u}} (f : S ⟶ T) :
    condensedPullbackHom Λ f = (upperStarFromPointComp f).hom.app Λ := rfl

private theorem coefficientSquare
    {S X Y Z : Scheme.{u}} (a : S ⟶ X) (b : X ⟶ Z)
    (c : S ⟶ Y) (d : Y ⟶ Z) (h : a ≫ b = c ≫ d)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :
    (ProEtale.upperStarCompIso Ab.{u + 1} h).inv.app ((upperStarFromPoint Z).obj Λ) ≫
        (ProEtale.upperStar Ab.{u + 1} a).map ((upperStarFromPointComp b).hom.app Λ) ≫
        (upperStarFromPointComp a).hom.app Λ =
      (ProEtale.upperStar Ab.{u + 1} c).map ((upperStarFromPointComp d).hom.app Λ) ≫
        (upperStarFromPointComp c).hom.app Λ := by
  exact compFromFive (C := Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
    (upperStarCompIso_inv_app a b c d h ((upperStarFromPoint Z).obj Λ))
    (profinite_point_pullback_abelian_coherence.2.2.2 _ _ _ _ c d a b h.symm Λ)

attribute [local irreducible] ProEtale.upperStar ProEtale.upperStarFromPoint
attribute [local irreducible] upperStar openImmersionLowerShriek
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors

end AlgebraicGeometry.ProEtale.CondensedRing
