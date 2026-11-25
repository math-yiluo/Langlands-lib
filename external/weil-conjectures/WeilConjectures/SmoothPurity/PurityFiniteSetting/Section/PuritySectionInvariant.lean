/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteTypeExceptionalInverseImage
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.Comparison

public import WeilConjectures.Algebra.Homology.HomotopyCategory.DerivabilityStructure
public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
public import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesTwo
public import WeilConjectures.Mathlib.CategoryTheory.EssentialImage
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.Derived
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.KFlat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.Vanishing
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.KFlat
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import WeilConjectures.SmoothPurity.Section.ProEtaleSectionInvariant
import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison

/-! # The pro-etale section invariant

Source: blueprint sec-smooth-purity/sk-def-purity-conv/def-pur-section-invariant.md
(blueprint: lemma-section-normal-bundle--1).

Its data are the actual derived inverse image of the relative dualizing object.
No orientation or Tate identification is chosen. The finite coefficient stage is
used here, as stipulated by the purity conventions. It is the general pro-étale section
invariant `AlgebraicGeometry.ProEtale.sectionInvariant` at the coefficient ring `O_E/ϖ^n`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

/-- The section invariant C(g,s) = Ls* Rg! A_B on the small pro-etale site.
The definition makes sense for any map s; its geometric and invertibility
properties below apply to closed sections of smooth separated finite-type maps.
It is the general pro-étale section invariant at the coefficient ring `O_E/ϖ^n`; the structure
morphism `aB` is kept for the finite-type interface of `P.dualizing`.
Source: blueprint lemma-section-normal-bundle--1, displayed definition
(blueprint: lemma-section-normal-bundle--1). -/
noncomputable def sectionInvariant (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) [HasCompactification g] (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] (s : B ⟶ V) :=
  ProEtale.sectionInvariant P.Coefficient g s

/-- The section invariant is `Ls^*` of the relative dualizing object `P.dualizing g aB`. -/
theorem sectionInvariant_eq_dualizing (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) [HasCompactification g] (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] (s : B ⟶ V) :
    P.sectionInvariant g aB s =
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) s).leftDerivedFunctor.obj
        (P.dualizing g aB) :=
  rfl

end WeilConjectures.PurityFiniteSetting
