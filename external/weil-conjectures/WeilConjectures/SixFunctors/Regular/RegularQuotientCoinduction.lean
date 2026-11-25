/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
import WeilConjectures.SixFunctors.ProEtale.IntegralNormalizedRestrictionSquaresSupplement
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement

/-! # Derived coinduction for the actual completed coefficient projection

Source: Stacks Tags 03D7, 079P and 06YY; the internal module-object equalizer adjunction,
transported by the normalized coefficient encoding.
(blueprint: lem-sf-regular-quotient-coinduction). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
open SheafOfModules
namespace WeilConjectures

attribute [-instance] integralCoefficientAbSheafify integralCoefficientAbLocallyBijective
  scalarReductionSourceDerived scalarReductionTargetDerived

local instance instHasSheafifyProEt_regularQuotientCoinduction (T : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, 0} T

local instance instWEqualsLocallyBijective_regularQuotientCoinduction (T : Scheme.{u}) :
    (Scheme.ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, 0} T

attribute [local instance] HasDerivedCategory.standard

/-- Exact scalar restriction along a positive completed-coefficient quotient has a right adjoint.
The ordinary internal-module adjunction is transported through the normalized section-action
equivalences. Source: Stacks Tags 03D7, 079P and 06YY; the internal module-object equalizer
adjunction, transported by the normalized coefficient encoding.
(blueprint: lem-sf-regular-quotient-coinduction). -/
theorem scalarReductionRestriction_isLeftAdjoint
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ) :
    (scalarReductionRestriction.{u, u} l E T n).IsLeftAdjoint := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  obtain ⟨A, e, a, _⟩ := IntegralPresentation.integral_completion_normalized_squares l E T
  let : MonoidalClosed (Sheaf (Scheme.ProEt.topology T) Ab.{u+1}) := inferInstance
  have h : (Mod.comap (AdicCompletion.quotient l E T n)).IsLeftAdjoint :=
    (Mod.restrictCoextendAdjunction (AdicCompletion.quotient l E T n)).isLeftAdjoint
  have h' : (Mod.comap (AdicCompletion.quotient l E T n) ⋙
      A.modules.functor).IsLeftAdjoint := inferInstance
  have h'' : ((e n).ordinary.functor ⋙
      scalarReductionRestriction.{u, u} l E T n).IsLeftAdjoint :=
    Functor.isLeftAdjoint_of_iso (a n)
  exact (Functor.isLeftAdjoint_comp_iff_right (e n).ordinary.functor _).mp h''

/-- The right adjoint to ordinary quotient restriction, uniquely characterized by its adjunction. It
is transported internal coextension, not an arbitrary module. Source: Stacks Tags 03D7, 079P and
06YY; the internal module-object equalizer adjunction, transported by the normalized coefficient
encoding.
(blueprint: lem-sf-regular-quotient-coinduction). -/
def scalarReductionCoinduction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ) :
    scalarReductionSource.{u, u} l E T ⥤ scalarReductionTarget.{u, u} l E T n :=
  letI := scalarReductionRestriction_isLeftAdjoint l E T n
  (scalarReductionRestriction.{u, u} l E T n).rightAdjoint

/-- Evaluation adjunction for the actual completed coefficient projection. Source: Stacks Tags 03D7,
079P and 06YY; the internal module-object equalizer adjunction, transported by the normalized
coefficient encoding.
(blueprint: lem-sf-regular-quotient-coinduction). -/
def scalarReductionCoinductionAdjunction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ) :
    scalarReductionRestriction.{u, u} l E T n ⊣ scalarReductionCoinduction l E T n :=
  letI := scalarReductionRestriction_isLeftAdjoint l E T n
  Adjunction.ofIsLeftAdjoint _

/-- Coinduction is additive, as the right adjoint of additive exact restriction.
Source: Stacks Tags 03D7 and 079P.
(blueprint: lem-sf-regular-quotient-coinduction). -/
instance scalarReductionCoinduction_additive
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ) :
    (scalarReductionCoinduction.{u} l E T n).Additive :=
  (scalarReductionCoinductionAdjunction.{u} l E T n).right_adjoint_additive

/-- Derive ordinary coinduction on K-injective completed-coefficient complexes. Source: Stacks Tags
03D7, 079P and 06YY; the internal module-object equalizer adjunction, transported by the
normalized coefficient encoding.
(blueprint: lem-sf-regular-quotient-coinduction). -/
def scalarReductionDerivedCoinduction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ) :
    DerivedCategory.{u + 2} (scalarReductionSource.{u, u} l E T) ⥤
      DerivedCategory.{u + 2} (scalarReductionTarget.{u, u} l E T n) :=
  letI : HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, u} T
  letI : (Scheme.ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, u} T
  letI : Abelian.HasKInjectiveResolutions (scalarReductionSource.{u, u} l E T) :=
    Scheme.proEtaleRingModules_hasKInjectiveResolutions T
      (completedIntegralCommRingSheafUnrestricted l E T)
  (scalarReductionCoinduction.{u} l E T n).rightDerivedFunctor.{u+2, u+2, u+1, u+1, u+2, u+2}

/-- Exact quotient restriction is left adjoint to its derived coinduction. Source: Stacks Tags 03D7,
079P and 06YY; the internal module-object equalizer adjunction, transported by the normalized
coefficient encoding.
(blueprint: lem-sf-regular-quotient-coinduction). -/
def scalarReductionDerivedCoinductionAdjunction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ) :
    scalarReductionDerivedRestriction.{u, u} l E T n ⊣
      scalarReductionDerivedCoinduction.{u} l E T n :=
  letI : HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, u} T
  letI : (Scheme.ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, u} T
  letI : Abelian.HasKInjectiveResolutions (scalarReductionSource.{u, u} l E T) :=
    Scheme.proEtaleRingModules_hasKInjectiveResolutions T
      (completedIntegralCommRingSheafUnrestricted l E T)
  letI := (scalarReductionRestriction_exact.{u, u} l E T n).1
  letI := (scalarReductionRestriction_exact.{u, u} l E T n).2
  show (scalarReductionRestriction.{u, u} l E T n).mapDerivedCategory ⊣
    (scalarReductionCoinduction.{u} l E T n).rightDerivedFunctor.{u+2, u+2, u+1, u+1, u+2, u+2} from
      (scalarReductionCoinductionAdjunction.{u} l E T n).mapDerivedCategoryRightDerivedAdjunction

end WeilConjectures
