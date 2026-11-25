/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.AlgebraicGeometry.ContinuousRingUniverseRealization
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.Topology.NoetherianSpace
public import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Topology.Category.Profinite.AsLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import Mathlib.Topology.Connected.TotallyDisconnected
public import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
public import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
public import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Category.Ring.Basic
public import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.LatticeSheafBasicSupplement

/-! # Section-action module encodings in the scheme universe

Source: Stacks Project, Tag 00YV; Bhatt--Scholze, Section 6.8.
(blueprint: def-sfb-continuous-coefficient-module-equivalence-universe)

These are the specified encodings formerly defined in IntegralScalarConstructibleImage.
They are separated here so ordinary module and scalar comparison lemmas can use them.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The section-action encoding, using the canonical continuous chart in arbitrary universe.
Source: Stacks Project, Tag 00YV; Bhatt--Scholze, Section 6.8.
(blueprint: def-sfb-continuous-coefficient-module-equivalence-universe). -/
def continuousRingModuleEquivalenceUniverse (X : Scheme.{u}) (T : Type u)
    [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] [TotallyDisconnectedSpace T] :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousCoefficientRingObj T) X) ≌
      SheafOfModules.{u + 1, u, u + 1, u + 1} (continuousCoefficientRingSheaf X T) := by
  letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} X.ProEt
  let J := Scheme.ProEt.topology X
  let R := continuousCoefficientRingSheaf X T
  let A := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  letI : IsCommMonObj A := Sheaf.isCommMonObj_sheafCompose_obj J R
    (fun V a b ↦ by
      exact @mul_comm (ULift.{u + 1} C(V.unop.left, T)) inferInstance a b)
  letI := Profinite.continuousMapRingObjOfUniverseMonObj.{u, u} T
  let φ := ContinuousRingUniverse.comparison X T
  letI := ContinuousRingUniverse.comparison_isIso X T
  exact (Mod.comapEquivalenceOfIsIso (inv φ)).trans
    ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J A).trans
      (ringModuleEquivalenceOfIso X (reconstructedRingIso X R).symm))

/-- The two section-ring presentations agree by the identity on continuous functions.
Source: Stacks Project, Tag 00YV; Bhatt--Scholze, Section 6.8.
(blueprint: def-sfb-continuous-coefficient-module-equivalence-universe). -/
def continuousSectionRingIso (X : Scheme.{u}) (T : Type u)
    [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] :
    latticeModuleRing X T ≅ continuousCoefficientRingSheaf X T :=
  ObjectProperty.isoMk _
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl))

/-- The same encoding in the existing commutative coefficient-sheaf coordinates.
Source: Stacks Project, Tag 00YV; Bhatt--Scholze, Section 6.8.
(blueprint: def-sfb-continuous-coefficient-module-equivalence-universe). -/
def continuousLatticeModuleEquivalenceUniverse (X : Scheme.{u}) (T : Type u)
    [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] [TotallyDisconnectedSpace T] :=
  (continuousRingModuleEquivalenceUniverse X T).trans
    (ringModuleEquivalenceOfIso X (continuousSectionRingIso X T))

/-- The field encoding has the specified continuous section action.
Source: Bhatt--Scholze, Section 6.8; Stacks Project, Tag 00YV.
(blueprint: def-sfb-continuous-coefficient-module-equivalence-universe). -/
def continuousFieldModuleEquivalenceUniverse (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    (X : Scheme.{u}) :=
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[l]
  continuousLatticeModuleEquivalenceUniverse X E

end AlgebraicGeometry.ProEtale.CondensedRing
