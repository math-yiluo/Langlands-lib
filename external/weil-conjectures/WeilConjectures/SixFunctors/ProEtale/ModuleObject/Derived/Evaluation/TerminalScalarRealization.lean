/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
public import WeilConjectures.Algebra.Homology.FlatScalarRealization
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Adjunction.Additive

/-! The concrete ordinary functor underlying terminal scalar realization.

Source: Hemo--Richarz--Scholbach, Section 3, equations (3.1)--(3.2).
(blueprint: def-zl-terminal-scalar-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.CondensedRing.Evaluation

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) [(J.W (A := Ab.{u + 1})).IsMonoidal]
  (O : Sheaf J Ab.{u + 1}) [MonObj O] [IsCommMonObj O]
  (U : C) (hU : IsTerminal U)

/-- Constant realization, sheafified scalar extension, and internal reconstruction.
Source: HRS equations (3.1)--(3.2) (blueprint: def-zl-terminal-scalar-realization). -/
def terminalScalarRealization :
    ModuleCat.{u + 1} (A J O U) ⥤ Mod (Sheaf J Ab.{u + 1}) O :=
  SheafOfModules.flatScalarRealization J (scalarMap J O U hU) ⋙
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J O).inverse

/-- Both scalar realization and the inverse section equivalence preserve addition.
Source: HRS Section 3 (blueprint: def-zl-terminal-scalar-realization). -/
instance terminalScalarRealization_additive : (terminalScalarRealization J O U hU).Additive := by
  let e := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J O
  let : e.inverse.Additive := Functor.additive_of_preserves_binary_products e.inverse
  change (SheafOfModules.flatScalarRealization J (scalarMap J O U hU) ⋙ e.inverse).Additive
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing.Evaluation
