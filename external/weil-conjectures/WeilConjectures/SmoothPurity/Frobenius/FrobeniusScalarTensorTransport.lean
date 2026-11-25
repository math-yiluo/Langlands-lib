/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SmoothPurity.InvertibleTensorScalarExtensionDefinitionsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.SmoothPurity.Frobenius.FrobeniusIntegralDiscreteTransportInvertible
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleIsomorphismInverseImage
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-! # Invertibility of semilinear scalar tensor transport

Source: Stacks Project, Modules on Sites, Tags 03EK and 03EL.
(blueprint: new-weil-frobenius-scalar-tensor-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped ChangeOfRings TensorProduct
namespace WeilConjectures

attribute [local implicit_reducible] sheafCompose Functor.sheafPushforwardContinuous
  MorphismProperty.Over.pullback Scheme.instCategoryProEt
  ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'
  SheafOfModules.changeOfRingsOfUniverses ModuleCat.extendScalars ModuleCat.ExtendScalars.obj'
  SheafOfModules.toSheaf PresheafOfModules.sheafification PresheafOfModules.sheafify
  SheafOfModules.changeOfRingsPresheafOfUniverses PresheafOfModules.presheaf

section TensorTransport

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  {R S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
  {R' S' : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
  (α : R ⟶ S) (α' : R' ⟶ S')
  (ρ : R ⟶ (proEtaleSheafDirectImage g CommRingCat.{u + 1}).obj R')
  (σ : S ⟶ (proEtaleSheafDirectImage g CommRingCat.{u + 1}).obj S')
  (h : α ≫ σ = ρ ≫ (proEtaleSheafDirectImage g CommRingCat.{u + 1}).map α')
  (M : SheafOfModules.{u + 1}
    ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
  (N : SheafOfModules.{u + 1}
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R'))
  (β : (SheafOfModules.toSheaf _).obj M ⟶
    (proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).obj
      ((SheafOfModules.toSheaf _).obj N))
  (hb : ∀ (U : Y.ProEtᵒᵖ) (a : R.obj.obj U) (x : M.val.obj U),
    β.hom.app U (a • x) =
      (show R'.obj.obj ((proEtaleBaseChange g).op.obj U) from ρ.hom.app U a) •
        (show N.val.obj ((proEtaleBaseChange g).op.obj U) from β.hom.app U x))

end TensorTransport

end WeilConjectures
