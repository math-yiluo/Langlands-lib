/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Integral.IntegralExceptionalInverseImage
public import WeilConjectures.CategoryTheory.ConstantRingModuleSheaves
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
public import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import WeilConjectures.CategoryTheory.IntTensorFamilyIso
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Sites.CartesianMonoidal

/-! # Finite realization of the strict exceptional adjunction
Source: blueprint theorem-f-shriek-finite-coefficients. All changes of quotient-ring
presentation act identically on sections. Derived comparisons retain the universal
right-derived unit, and exceptional comparisons are adjunction mates.
(blueprint: def-pur-adic-etale-realization).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry SheafOfModules
namespace WeilConjectures

-- Since build 2026-10-28 `Scheme.ProjectionRestriction.derived`
-- (with `SemilinearSections.moduleAbelian`) is also in scope for the strict levels; keep the
-- instances these statements were written against
-- (those of StrictEtaleSystemInterfaces, which the strict-system fields carry).
attribute [local instance 5000] AlgebraicGeometry.strictEtaleSystemDerived
  AlgebraicGeometry.strictEtaleLevelDerived
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The actual quotient ring in the lifted integer presentation.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-etale-realization). -/
abbrev integralExceptionalQuotientRing (n : ℕ) :=
  integralExceptionalIntegers l E ⧸
    (Ideal.span ({integralExceptionalUniformizer l E} :
      Set (integralExceptionalIntegers l E))) ^ (n + 1)

/-- Forgetting commutativity commutes with etale sheafification.
Source: Stacks 00W1 (blueprint: def-pur-adic-etale-realization).
Proof: the forgetful functor preserves the finite limits and filtered colimits used
by the covering-compatible-family construction of sheafification. Local equality
is unchanged, giving the same associated ring sheaf in both constructions. -/
theorem integralExceptionalEtaleForget (W : Scheme.{u}) :
    W.smallEtaleTopology.PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := by
  have : EssentiallySmall.{u + 1} W.Etale := essentiallySmallSelf.{0} _
  constructor
  intro P Q f hf
  change W.smallEtaleTopology.W
    (Functor.whiskerRight f (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
  have hi : Presheaf.IsLocallyInjective W.smallEtaleTopology f := hf.isLocallyInjective
  have hs : Presheaf.IsLocallySurjective W.smallEtaleTopology f := hf.isLocallySurjective
  apply (W.smallEtaleTopology.W_iff_isLocallyBijective _).mpr
  constructor
  · exact ⟨fun x y h ↦ Presheaf.equalizerSieve_mem W.smallEtaleTopology f x y h⟩
  · exact ⟨fun x ↦ Presheaf.imageSieve_mem W.smallEtaleTopology f x⟩

/-- Ordinary finite realization on the etale site: forget the locally constant scalar
sections to constant scalars and restrict along the explicit quotient-ring equivalence.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-etale-realization). -/
def integralExceptionalEtaleRealization (W : Scheme.{u}) (n : ℕ) :
    strictEtaleLevel W (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E) n ⥤
    Sheaf W.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) :=
  letI := integralExceptionalEtaleForget W
  SheafOfModules.restrictScalars
      ((constantCommuteCompose W.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
          (CommRingCat.of (integralExceptionalQuotientRing l E n))).inv ⋙
    constantRingModuleRestriction W.smallEtaleTopology (integralExceptionalQuotientRing l E n) ⋙
      sheafCompose W.smallEtaleTopology
        (ModuleCat.restrictScalars (integralExceptionalQuotient l E n).symm.toRingHom)

private def finiteRestrictionCancel {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{u + 1}}
    (α : R ⟶ S) (β : S ⟶ R) (h : α ≫ β = 𝟙 R) :
    SheafOfModules.restrictScalars.{u + 1} β ⋙ SheafOfModules.restrictScalars α ≅
      𝟭 (SheafOfModules.{u + 1} R) := by
  have hU (U : Cᵒᵖ) : (β.hom.app U).hom.comp (α.hom.app U).hom =
      RingHom.id (R.obj.obj U) :=
    congrArg RingCat.Hom.hom (congr_app (congrArg (fun k : R ⟶ R ↦ k.hom) h) U)
  refine NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (α.hom.app U).hom (β.hom.app U).hom
        (RingHom.id (R.obj.obj U)) (hU U).symm (M.val.obj U)).symm ≪≫
      (ModuleCat.restrictScalarsId (R.obj.obj U)).app (M.val.obj U)) ?_)) ?_
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

private theorem finiteRestrictionEquivalence {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{u + 1}} (e : R ≅ S) :
    (SheafOfModules.restrictScalars.{u + 1} e.hom).IsEquivalence :=
  (CategoryTheory.Equivalence.mk (SheafOfModules.restrictScalars e.hom)
    (SheafOfModules.restrictScalars e.inv)
    (finiteRestrictionCancel e.inv e.hom e.inv_hom_id).symm
    (finiteRestrictionCancel e.hom e.inv e.hom_inv_id)).isEquivalence_functor

/-- The finite realization is an exact additive equivalence.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-etale-realization).
Proof: constant-ring restriction is the equivalence of locally constant scalar actions.Restriction
 along a ring equivalence is an equivalence with inverse the opposite scalar
restriction. All maps leave the underlying abelian sheaves unchanged, hence preserve
addition, kernels and cokernels. -/
theorem integralExceptionalEtaleRealization_properties (W : Scheme.{u}) (n : ℕ) :
    (integralExceptionalEtaleRealization l E W n).IsEquivalence ∧
      (integralExceptionalEtaleRealization l E W n).Additive ∧
      PreservesFiniteLimits (integralExceptionalEtaleRealization l E W n) ∧
      PreservesFiniteColimits (integralExceptionalEtaleRealization l E W n) := by
  let := integralExceptionalEtaleForget W
  obtain ⟨e, he, ha, _, _⟩ :=
    (constant_ring_module_sheaves W.smallEtaleTopology
      (integralExceptionalQuotientRing l E n)).1
  have h₁ : (SheafOfModules.restrictScalars.{u + 1}
      ((constantCommuteCompose W.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
          (CommRingCat.of (integralExceptionalQuotientRing l E n))).inv).IsEquivalence :=
    finiteRestrictionEquivalence
      ((constantCommuteCompose W.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
          (CommRingCat.of (integralExceptionalQuotientRing l E n))).symm
  have h₂ : (constantRingModuleRestriction W.smallEtaleTopology
      (integralExceptionalQuotientRing l E n)).IsEquivalence := by
    rw [← he]
    exact e.isEquivalence_functor
  have ha₂ : (constantRingModuleRestriction W.smallEtaleTopology
      (integralExceptionalQuotientRing l E n)).Additive := by
    rw [← he]
    exact ha
  have h₃ : (sheafCompose W.smallEtaleTopology
      (ModuleCat.restrictScalars.{u + 1} (integralExceptionalQuotient l E n).symm.toRingHom)
      ).IsEquivalence := isEquivalence_sheafCompose_of_isEquivalence W.smallEtaleTopology _
  have h : (integralExceptionalEtaleRealization l E W n).IsEquivalence := by
    dsimp only [integralExceptionalEtaleRealization]
    exact Functor.isEquivalence_trans _ _
  exact ⟨h, by dsimp only [integralExceptionalEtaleRealization]; infer_instance,
    inferInstance, inferInstance⟩

/-- Instance induced by the preceding named construction or property.
Source: blueprint adic reconstruction, canonical coefficient comparisons
(blueprint: def-pur-adic-etale-realization). -/
instance integralExceptionalEtaleRealization_equivalence (W : Scheme.{u}) (n : ℕ) :
    (integralExceptionalEtaleRealization l E W n).IsEquivalence :=
  (integralExceptionalEtaleRealization_properties l E W n).1
/-- Instance induced by the preceding named construction or property.
Source: blueprint adic reconstruction, canonical coefficient comparisons
(blueprint: def-pur-adic-etale-realization). -/
instance integralExceptionalEtaleRealization_additive (W : Scheme.{u}) (n : ℕ) :
    (integralExceptionalEtaleRealization l E W n).Additive :=
  (integralExceptionalEtaleRealization_properties l E W n).2.1
/-- Instance induced by the preceding named construction or property.
Source: blueprint adic reconstruction, canonical coefficient comparisons
(blueprint: def-pur-adic-etale-realization). -/
instance integralExceptionalEtaleRealization_limits (W : Scheme.{u}) (n : ℕ) :
    PreservesFiniteLimits (integralExceptionalEtaleRealization l E W n) :=
  (integralExceptionalEtaleRealization_properties l E W n).2.2.1
/-- Instance induced by the preceding named construction or property.
Source: blueprint adic reconstruction, canonical coefficient comparisons
(blueprint: def-pur-adic-etale-realization). -/
instance integralExceptionalEtaleRealization_colimits (W : Scheme.{u}) (n : ℕ) :
    PreservesFiniteColimits (integralExceptionalEtaleRealization l E W n) :=
  (integralExceptionalEtaleRealization_properties l E W n).2.2.2

private theorem constantSection_apply
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type (u + 1))] [HasWeakSheafify J CommRingCat.{u + 1}]
    [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u + 1})]
    (A : Type (u + 1)) [CommRing A] (a : A) (U : Cᵒᵖ)
    (z : ((constantSheaf J (Type (u + 1))).obj PUnit).obj.obj U) :
    ((((sheafificationAdjunction J (Type (u + 1))).homEquiv _
      ((sheafCompose J (CategoryTheory.forget CommRingCat.{u + 1})).obj
        ((constantSheaf J CommRingCat.{u + 1}).obj (CommRingCat.of A)))).symm
      ((Functor.const Cᵒᵖ).map (TypeCat.ofHom (fun (_ : PUnit.{u + 2}) ↦ a)) ≫
        Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A)))
          (CategoryTheory.forget CommRingCat.{u + 1}))).hom.app U z) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U a := by
  let T := (Functor.const Cᵒᵖ).obj (PUnit.{u + 2} : Type (u + 1))
  have hT : Presheaf.IsSheaf J T := Sheaf.tensorUnit_isSheaf J
  have : IsIso (toSheafify J T) := isIso_toSheafify J hT
  obtain ⟨t, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    ((toSheafify J T).app U)).surjective z
  have h := ((sheafificationAdjunction J (Type (u + 1))).homEquiv _
      ((sheafCompose J (CategoryTheory.forget CommRingCat.{u + 1})).obj
        ((constantSheaf J CommRingCat.{u + 1}).obj (CommRingCat.of A)))).apply_symm_apply
    ((Functor.const Cᵒᵖ).map (TypeCat.ofHom (fun (_ : PUnit.{u + 2}) ↦ a)) ≫
      Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A)))
        (CategoryTheory.forget CommRingCat.{u + 1}))
  exact congrArg (fun f ↦ f.app U t) h

private theorem constantRingScalar
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    [HasWeakSheafify J RingCat.{u + 1}] [HasWeakSheafify J CommRingCat.{u + 1}]
    [J.PreservesSheafification (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    (A : Type (u + 1)) [CommRing A] (U : Cᵒᵖ) (a : A) :
    (((constantCommuteCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app
      (CommRingCat.of A)).hom.app U)
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of A))).app U a) =
    (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U a := by
  have h := sheafComposeIso_hom_fac J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))
  change ((sheafifyComposeIso J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).hom.app U)
      (((presheafToSheaf J RingCat.{u + 1}).map
        ((Functor.compConstIso Cᵒᵖ
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom.app
            (CommRingCat.of A))).hom.app U
              ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of A))).app U a)) = _
  have hi : ((Functor.compConstIso Cᵒᵖ
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom.app
        (CommRingCat.of A)) = 𝟙 _ := rfl
  rw [hi, CategoryTheory.Functor.map_id]
  exact congrArg (fun f ↦ f.app U a) h

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (A : StrictEtaleOrdinaryImage (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E) g)

attribute [local irreducible] integralExceptionalQuotient

/-- Direct-image realization, uniquely determined by the given set-sheaf comparison
on every section. This fixes its scalar normalization, not just its isomorphism class.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-etale-realization).
Proof: both direct images evaluate on the same base-change etale object. The specified
rightUnderlying map identifies their sections and commutes with restriction. Constants
have the same image under the explicit quotient equivalence, so the map is linear. Its
underlying bijection gives an inverse; faithful forgetting proves uniqueness. -/
theorem integralExceptionalEtaleRight_existsUnique (n : ℕ) :
    ∃! e : A.right n ⋙ integralExceptionalEtaleRealization l E Y n ≅
      integralExceptionalEtaleRealization l E X n ⋙
        Etale.lowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1}
            (Padic.coefficientExtensionRing l E (n + 1)))) g,
      ∀ (M : strictEtaleLevel X (integralExceptionalIntegers l E)
        (integralExceptionalUniformizer l E) n) (W : Y.Etaleᵒᵖ)
        (x : ((A.right n).obj M).val.obj W),
        (e.hom.app M).hom.app W x =
          ((A.rightUnderlying n).hom.app M).hom.app W x := by
  let := integralExceptionalEtaleForget Y
  let := integralExceptionalEtaleForget X
  let p := MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ g
  let L := Scheme.etaleSetPullback g
  let adj := strictEtaleSetAdjunction g
  let Q := coefficientUnderlying (J := Y.smallEtaleTopology)
    (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n
  let V := coefficientUnderlying (J := X.smallEtaleTopology)
    (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n
  let I := A.lift n
  let R := A.right n
  let β := A.rightUnderlying n
  have hβ (M) : β.hom.app M = adj.homEquiv _ _
      (I.moduleUnderlying.inv.app (R.obj M) ≫
        V.map ((A.levelAdj n).counit.app M)) := by
    have hc : (A.levelAdj n).homEquiv (R.obj M) M
        ((A.levelAdj n).counit.app M) = 𝟙 _ := by
      rw [← Adjunction.homEquiv_symm_id]
      exact ((A.levelAdj n).homEquiv (R.obj M) M).apply_symm_apply _
    have h := A.levelTranspose n (R.obj M) M
      ((A.levelAdj n).counit.app M)
    change (A.levelAdj n).homEquiv (R.obj M) M
      ((A.levelAdj n).counit.app M) = 𝟙 _ at hc
    change Q.map ((A.levelAdj n).homEquiv (R.obj M) M
      ((A.levelAdj n).counit.app M)) ≫ β.hom.app M = _ at h
    rw [hc, Q.map_id, Category.id_comp] at h
    exact h
  have hunit (M) (T : Sheaf Y.smallEtaleTopology (Type (u + 1)))
      (a : T ⟶ Q.obj (R.obj M)) (U : Y.Etaleᵒᵖ) (z : T.obj.obj U) :
      (β.hom.app M).hom.app U (a.hom.app U z) =
      ((A.levelAdj n).counit.app M).val.app (p.op.obj U)
        ((I.moduleUnderlying.inv.app (R.obj M)).hom.app (p.op.obj U)
          ((L.map a).hom.app (p.op.obj U)
            ((adj.unit.app T).hom.app U z))) := by
    rw [hβ, Adjunction.homEquiv_unit]
    have h := congrArg (fun f ↦ f.hom.app U z) (adj.unit.naturality a)
    change (adj.unit.app (Q.obj (R.obj M))).hom.app U (a.hom.app U z) =
      (L.map a).hom.app (p.op.obj U)
        ((adj.unit.app T).hom.app U z) at h
    exact congrArg (fun x ↦
      ((A.levelAdj n).counit.app M).val.app (p.op.obj U)
        ((I.moduleUnderlying.inv.app (R.obj M)).hom.app
          (p.op.obj U) x)) h
  have hadd (M) (U : Y.Etaleᵒᵖ) (x y : (R.obj M).val.obj U) :
      (β.hom.app M).hom.app U (x + y) =
        (show M.val.obj (p.op.obj U) from
          (β.hom.app M).hom.app U x) +
        (show M.val.obj (p.op.obj U) from
          (β.hom.app M).hom.app U y) := by
    let Tmod := Q.obj (R.obj M)
    let T := (CategoryTheory.MonoidalCategory.tensorObj Tmod Tmod)
    let a : T ⟶ Tmod := CartesianMonoidalCategory.fst Tmod Tmod
    let b : T ⟶ Tmod := CartesianMonoidalCategory.snd Tmod Tmod
    let t : T ⟶ Tmod := ⟨{
      app := fun Y ↦ ↾fun z ↦
        (show (R.obj M).val.obj Y from z.1) +
          (show (R.obj M).val.obj Y from z.2)
      naturality := by
        intro Y Z f
        ext z
        exact ((R.obj M).val.map f).hom.map_add z.1 z.2 |>.symm }⟩
    have h := I.moduleAdd (R.obj M) T a b t (fun _ _ ↦ rfl)
      (p.op.obj U) ((adj.unit.app T).hom.app U (x, y))
    have ha := hunit M T a U (x, y)
    have hb := hunit M T b U (x, y)
    have ht := hunit M T t U (x, y)
    change (β.hom.app M).hom.app U (x + y) = _ at ht
    change (β.hom.app M).hom.app U x = _ at ha
    change (β.hom.app M).hom.app U y = _ at hb
    dsimp only [id] at h
    -- Compose section equations directly to avoid rewriting through the sheaf constructions.
    let ε := (((A.levelAdj n).counit.app M).val.app (p.op.obj U)).hom
    exact ht.trans ((congrArg ε h).trans
      ((ε.map_add _ _).trans (congrArg₂ (· + ·) ha.symm hb.symm)))
  have hsmul (M) (U : Y.Etaleᵒᵖ) (q : integralExceptionalQuotientRing l E n)
      (x : (R.obj M).val.obj U) :
      (β.hom.app M).hom.app U
        ((toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj
          (CommRingCat.of (integralExceptionalQuotientRing l E n)))).app U q • x) =
      (toSheafify (X.smallEtaleTopology) ((Functor.const X.Etaleᵒᵖ).obj
        (CommRingCat.of (integralExceptionalQuotientRing l E n)))).app
          (p.op.obj U) q •
        (show M.val.obj (p.op.obj U) from
          (β.hom.app M).hom.app U x) := by
    let Tmod := Q.obj (R.obj M)
    let S := (constantSheaf Y.smallEtaleTopology (Type (u + 1))).obj PUnit
    let T := CategoryTheory.MonoidalCategory.tensorObj S Tmod
    let a : T ⟶ _ := CartesianMonoidalCategory.fst S Tmod ≫
      coefficientConstantSection (J := Y.smallEtaleTopology)
        (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n q
    let b : T ⟶ Tmod := CartesianMonoidalCategory.snd S Tmod
    let t : T ⟶ Tmod := ⟨{
      app := fun U₀ ↦ ↾fun z ↦
        (show (coefficientQuotientSheaf (J := Y.smallEtaleTopology)
          (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n).obj.obj U₀
            from a.hom.app U₀ z) • (show (R.obj M).val.obj U₀ from z.2)
      naturality := by
        intro U₀ Z f
        ext z
        have hn := congrArg (fun k ↦ k z) (a.hom.naturality f).symm
        change (coefficientQuotientSheaf (J := Y.smallEtaleTopology)
          (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n).obj.map f
            (a.hom.app U₀ z) = a.hom.app Z (T.obj.map f z) at hn
        symm
        change (R.obj M).val.map f
          ((show (coefficientQuotientSheaf (J := Y.smallEtaleTopology)
            (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n).obj.obj U₀
              from a.hom.app U₀ z) • (show (R.obj M).val.obj U₀ from z.2)) =
          (show (coefficientQuotientSheaf (J := Y.smallEtaleTopology)
            (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n).obj.obj Z
              from a.hom.app Z (T.obj.map f z)) •
                (show (R.obj M).val.obj Z from (R.obj M).val.map f z.2)
        rw [(R.obj M).val.map_smul]
        exact congrArg (fun c : (coefficientQuotientSheaf
          (J := Y.smallEtaleTopology) (integralExceptionalIntegers l E)
          (integralExceptionalUniformizer l E) n).obj.obj Z ↦
            c • (show (R.obj M).val.obj Z from (R.obj M).val.map f z.2)) hn }⟩
    let z : T.obj.obj U :=
      ((toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj
        (PUnit.{u + 2} : Type (u + 1)))).app U PUnit.unit, x)
    have ha : a.hom.app U z =
        (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj
          (CommRingCat.of (integralExceptionalQuotientRing l E n)))).app U q :=
      constantSection_apply Y.smallEtaleTopology _ q U z.1
    have h := I.moduleSMul (R.obj M) T a b t (fun _ _ ↦ rfl)
      (p.op.obj U) ((adj.unit.app T).hom.app U z)
    have hc : L.map a ≫ I.ringUnderlying.hom =
        L.map (CartesianMonoidalCategory.fst S Tmod) ≫ A.singleton.hom ≫
          coefficientConstantSection (J := X.smallEtaleTopology)
            (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n q := by
      dsimp only [a]
      rw [L.map_comp, Category.assoc, A.constants]
    have hc' := congrArg (fun f ↦ f.hom.app (p.op.obj U)
      ((adj.unit.app T).hom.app U z)) hc
    have ht := hunit M T t U z
    have hb := hunit M T b U z
    change (β.hom.app M).hom.app U
      ((show (coefficientQuotientSheaf (J := Y.smallEtaleTopology)
        (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n).obj.obj U
          from a.hom.app U z) • x) = _ at ht
    change (β.hom.app M).hom.app U x = _ at hb
    rw [ha] at ht
    dsimp only [id] at h
    have hconst := constantSection_apply (X.smallEtaleTopology)
      (integralExceptionalQuotientRing l E n) q (p.op.obj U)
      ((A.singleton.hom).hom.app (p.op.obj U)
        ((L.map (CartesianMonoidalCategory.fst S Tmod)).hom.app
          (p.op.obj U) ((adj.unit.app T).hom.app U z)))
    change (I.ringUnderlying.hom).hom.app (p.op.obj U)
      ((L.map a).hom.app (p.op.obj U)
        ((adj.unit.app T).hom.app U z)) = _ at hc'
    have hs := hc'.trans hconst
    let ε := (((A.levelAdj n).counit.app M).val.app (p.op.obj U)).hom
    exact ht.trans ((congrArg ε h).trans
      ((ε.map_smul _ _).trans (congrArg₂ (· • ·) hs hb.symm)))
  let F := R ⋙ integralExceptionalEtaleRealization l E Y n
  let G := integralExceptionalEtaleRealization l E X n ⋙
    Etale.lowerStar (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) g
  let γ : F ⟶ G := {
    app := fun M ↦ { hom := {
      app := fun U ↦ ModuleCat.ofHom
        (X := (F.obj M).obj.obj U) (Y := (G.obj M).obj.obj U) {
        toFun := fun x ↦ (β.hom.app M).hom.app U x
        map_add' := fun x y ↦ hadd M U x y
        map_smul' := by
          intro c x
          change (β.hom.app M).hom.app U
            (((constantCommuteCompose Y.smallEtaleTopology
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app
                (CommRingCat.of (integralExceptionalQuotientRing l E n))).hom.app U
                  ((toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj
                    (RingCat.of (integralExceptionalQuotientRing l E n)))).app U
                      ((integralExceptionalQuotient l E n).symm c)) •
                (show (R.obj M).val.obj U from x)) =
            (((constantCommuteCompose (X.smallEtaleTopology)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app
                (CommRingCat.of (integralExceptionalQuotientRing l E n))).hom.app
                  (p.op.obj U)
                    ((toSheafify (X.smallEtaleTopology) ((Functor.const X.Etaleᵒᵖ).obj
                      (RingCat.of (integralExceptionalQuotientRing l E n)))).app
                        (p.op.obj U)
                          ((integralExceptionalQuotient l E n).symm c))) •
              (show M.val.obj (p.op.obj U) from
                (β.hom.app M).hom.app U x)
          rw [constantRingScalar, constantRingScalar]
          exact hsmul M U ((integralExceptionalQuotient l E n).symm c) x }
      naturality := by
        intro U V f
        ext x
        exact congrArg (fun k ↦ k x) ((β.hom.app M).hom.naturality f) } }
    naturality := by
      intro M N f
      ext U x
      exact congrArg (fun k ↦ k.hom.app U x) (β.hom.naturality f) }
  have hγ (M) : IsIso (γ.app M) := by
    have hpoint (U) : IsIso ((γ.app M).hom.app U) := by
      rw [ConcreteCategory.isIso_iff_bijective]
      exact ConcreteCategory.bijective_of_isIso ((β.hom.app M).hom.app U)
    have : IsIso ((sheafToPresheaf Y.smallEtaleTopology _).map (γ.app M)) :=
      NatIso.isIso_of_isIso_app (γ.app M).hom
    exact isIso_of_reflects_iso (γ.app M) (sheafToPresheaf Y.smallEtaleTopology _)
  have : IsIso γ := NatIso.isIso_of_isIso_app γ
  refine ⟨asIso γ, ?_, ?_⟩
  · intro M U x
    rfl
  · intro e he
    apply Iso.ext
    apply NatTrans.ext
    apply funext
    intro M
    ext U x
    exact he M U x

/-- The actual ordinary direct-image realization, fixed on all underlying sections.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-etale-realization). -/
def integralExceptionalEtaleRight (n : ℕ) :
    A.right n ⋙ integralExceptionalEtaleRealization l E Y n ≅
      integralExceptionalEtaleRealization l E X n ⋙
        Etale.lowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1}
            (Padic.coefficientExtensionRing l E (n + 1)))) g :=
  (integralExceptionalEtaleRight_existsUnique l E g A n).choose

/-- Inverse-image realization, fixed by the actual Hom transposes and the normalized
ordinary right-image comparison.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-etale-realization).
Proof: transport both adjunctions along the finite realization equivalences. The
normalized right comparison induces the comparison of their left adjoints. The
adjunction bijections force precisely the displayed equation and make it unique. -/
theorem integralExceptionalEtaleInverse_existsUnique (n : ℕ) :
    ∃! e : (A.lift n).modules ⋙ integralExceptionalEtaleRealization l E X n ≅
      integralExceptionalEtaleRealization l E Y n ⋙
        Etale.upperStar
          (ModuleCat.{u + 1} (ULift.{u + 1}
            (Padic.coefficientExtensionRing l E (n + 1)))) g,
      ∀ (M : strictEtaleLevel Y (integralExceptionalIntegers l E)
          (integralExceptionalUniformizer l E) n)
        (N : strictEtaleLevel X (integralExceptionalIntegers l E)
          (integralExceptionalUniformizer l E) n)
        (h : (A.lift n).modules.obj M ⟶ N),
        (Etale.upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1}
            (Padic.coefficientExtensionRing l E (n + 1)))) g).homEquiv _ _
          (e.inv.app M ≫ (integralExceptionalEtaleRealization l E X n).map h) =
        (integralExceptionalEtaleRealization l E Y n).map
          ((A.levelAdj n).homEquiv _ _ h) ≫
            (integralExceptionalEtaleRight l E g A n).hom.app N := by
  let a := A.levelAdj n
  let b := Etale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1}
      (Padic.coefficientExtensionRing l E (n + 1)))) g
  let β := integralExceptionalEtaleRight l E g A n
  let α := ((mateEquiv a b).symm β.hom)
  have : IsIso α := isIso_inverseMate_of_equivalences a b β
  let e := (asIso α).symm
  have he M N (h : (A.lift n).modules.obj M ⟶ N) :
      b.homEquiv _ _ (e.inv.app M ≫
        (integralExceptionalEtaleRealization l E X n).map h) =
      (integralExceptionalEtaleRealization l E Y n).map (a.homEquiv _ _ h) ≫
        β.hom.app N :=
    adjunctionMate_transpose a b β.hom M N h
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext_inv
  apply NatTrans.ext
  funext M
  apply (b.homEquiv _ _).injective
  have h := (he' M _ (𝟙 _)).trans (he M _ (𝟙 _)).symm
  change b.homEquiv _ _ (e'.inv.app M ≫
      (integralExceptionalEtaleRealization l E X n).map (𝟙 _)) =
    b.homEquiv _ _ (e.inv.app M ≫
      (integralExceptionalEtaleRealization l E X n).map (𝟙 _)) at h
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Category.comp_id,
    CategoryTheory.Category.comp_id] at h
  exact h

/-- The ordinary inverse comparison specified by the full adjunction equation.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-etale-realization). -/
def integralExceptionalEtaleInverse (n : ℕ) :
    (A.lift n).modules ⋙ integralExceptionalEtaleRealization l E X n ≅
      integralExceptionalEtaleRealization l E Y n ⋙
        Etale.upperStar
          (ModuleCat.{u + 1} (ULift.{u + 1}
            (Padic.coefficientExtensionRing l E (n + 1)))) g :=
  (integralExceptionalEtaleInverse_existsUnique l E g A n).choose
/-- The universal right-derived unit on cochain complexes, retaining its actual map.
Source: blueprint derived exceptional construction
(blueprint: def-pur-adic-etale-realization). -/
def integralExceptionalFixedRightUnit (n : ℕ)
    (J : CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) ℤ) :
    DerivedCategory.Q.obj
      (((Etale.lowerStar (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) g).mapHomologicalComplex
           (.up ℤ)).obj J) ⟶
    (Etale.lowerStar (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) g).rightDerivedFunctor.obj
         (DerivedCategory.Q.obj J) :=
  (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
    (Etale.lowerStar (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) g).rightDerivedFunctorUnit.app
         ((HomotopyCategory.quotient _ _).obj J) ≫
    (Etale.lowerStar (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) g).rightDerivedFunctor.map
         ((DerivedCategory.quotientCompQhIso _).hom.app J)

/-- The full right-derived-unit square on every cochain representative.
Source: blueprint integral exceptional realization
(blueprint: def-pur-adic-etale-realization). -/
def IsIntegralExceptionalEtaleDerivedRight (n : ℕ)
    (B : CoefficientDerivedImage (A.lift n).modules (A.right n) (A.levelAdj n))
    (e : B.direct ⋙ (integralExceptionalEtaleRealization l E Y n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E X n).mapDerivedCategory ⋙
        (Etale.lowerStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) g).rightDerivedFunctor) :
      Prop :=
  ∀ J : CochainComplex (strictEtaleLevel X (integralExceptionalIntegers l E)
        (integralExceptionalUniformizer l E) n) ℤ,
        (integralExceptionalEtaleRealization l E Y n).mapDerivedCategory.map
            (B.directUnit.app J) ≫ e.hom.app (DerivedCategory.Q.obj J) ≫
          (Etale.lowerStar (ModuleCat.{u + 1}
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) g).rightDerivedFunctor.map
                ((integralExceptionalEtaleRealization l E X n).mapDerivedCategoryFactors.hom.app
                   J) =
        (integralExceptionalEtaleRealization l E Y n).mapDerivedCategoryFactors.hom.app
          (((A.right n).mapHomologicalComplex (.up ℤ)).obj J) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (integralExceptionalEtaleRight l E g A n).hom (.up ℤ)).app J) ≫
        integralExceptionalFixedRightUnit l E g n
          (((integralExceptionalEtaleRealization l E X n).mapHomologicalComplex
             (.up ℤ)).obj J)

/-- Natural transformations out of a right derived functor followed by an equivalence are
determined by their restriction along the derived unit. -/
theorem rightDerived_comp_equivalence_ext {C D H K : Type*} [Category C] [Category D]
    [Category H] [Category K] {F : C ⥤ H} {L : C ⥤ D} {RF : D ⥤ H} (α : F ⟶ L ⋙ RF)
    (W : MorphismProperty C) [L.IsLocalization W] [RF.IsRightDerivedFunctor α W]
    (e : H ≌ K) {G : D ⥤ K} (γ₁ γ₂ : RF ⋙ e.functor ⟶ G)
    (h : ∀ x, e.functor.map (α.app x) ≫ γ₁.app (L.obj x) =
      e.functor.map (α.app x) ≫ γ₂.app (L.obj x)) :
    γ₁ = γ₂ := by
  let δ (γ : RF ⋙ e.functor ⟶ G) : RF ⟶ G ⋙ e.inverse :=
    RF.rightUnitor.inv ≫ Functor.whiskerLeft RF e.unit ≫ (RF.associator _ _).inv ≫
      Functor.whiskerRight γ e.inverse
  have hδ (γ : RF ⋙ e.functor ⟶ G) (y : D) :
      (δ γ).app y = e.unit.app (RF.obj y) ≫ e.inverse.map (γ.app y) := by
    simp [δ]
  have hδ' : δ γ₁ = δ γ₂ := by
    apply RF.rightDerived_ext α W
    ext x
    have h₁ : α.app x ≫ e.unit.app (RF.obj (L.obj x)) =
        e.unit.app (F.obj x) ≫ e.inverse.map (e.functor.map (α.app x)) :=
      e.unit.naturality (α.app x)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, hδ]
    rw [reassoc_of% h₁, reassoc_of% h₁, ← e.inverse.map_comp, ← e.inverse.map_comp, h x]
  ext y
  apply e.inverse.map_injective
  have h₂ := congr_app hδ' y
  rw [hδ, hδ] at h₂
  exact (cancel_epi _).1 h₂

set_option hygiene false in
local notation "ΦYc" => integralExceptionalEtaleRealization l E Y n
set_option hygiene false in
local notation "ΦXc" => integralExceptionalEtaleRealization l E X n
set_option hygiene false in
local notation "gs" => Etale.lowerStar (ModuleCat.{u + 1}
  (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) g

private lemma quotientCompQhIso_inv_app_eq_id {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (K : CochainComplex C ℤ) :
    (DerivedCategory.quotientCompQhIso C).inv.app K ≫
      (DerivedCategory.quotientCompQhIso C).hom.app K = 𝟙 _ :=
  Iso.inv_hom_id_app _ _

private lemma integralExceptionalFixedRightUnit_eq (n : ℕ)
    (J : CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) ℤ) :
    integralExceptionalFixedRightUnit l E g n J =
      (DerivedCategory.quotientCompQhIso _).inv.app (((gs).mapHomologicalComplex (.up ℤ)).obj J) ≫
        (gs).rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj J) ≫
          (gs).rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app J) :=
  rfl

private lemma integralExceptionalFixedRightUnit_naturality (n : ℕ)
    {J J' : CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) ℤ} (f : J ⟶ J') :
    DerivedCategory.Q.map (((gs).mapHomologicalComplex (.up ℤ)).map f) ≫
        integralExceptionalFixedRightUnit l E g n J' =
      integralExceptionalFixedRightUnit l E g n J ≫ (gs).rightDerivedFunctor.map
        (DerivedCategory.Q.map f) := by
  have hu := (gs).rightDerivedFunctorUnit.naturality ((HomotopyCategory.quotient _ _).map f)
  have hh := congrArg (gs).rightDerivedFunctor.map
    (DerivedCategory.quotientCompQhIso_hom_naturality f)
  simp only [Functor.map_comp] at hh
  rw [integralExceptionalFixedRightUnit_eq, integralExceptionalFixedRightUnit_eq,
    DerivedCategory.quotientCompQhIso_inv_naturality_assoc, Category.assoc, Category.assoc,
    ← hh]
  congr 1
  rw [← Category.assoc, ← Category.assoc]
  congr 1

/-- The representative comparison on cochain complexes underlying the derived right
comparison. -/
private noncomputable def derivedRightRep (n : ℕ)
    (J : CochainComplex (strictEtaleLevel X (integralExceptionalIntegers l E)
        (integralExceptionalUniformizer l E) n) ℤ) :
    (ΦYc).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (((A.right n).mapHomologicalComplex (.up ℤ)).obj J)) ⟶
      (gs).rightDerivedFunctor.obj ((ΦXc).mapDerivedCategory.obj (DerivedCategory.Q.obj J)) :=
  (ΦYc).mapDerivedCategoryFactors.hom.app
      (((A.right n).mapHomologicalComplex (.up ℤ)).obj J) ≫
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
      (integralExceptionalEtaleRight l E g A n).hom (.up ℤ)).app J) ≫
    integralExceptionalFixedRightUnit l E g n (((ΦXc).mapHomologicalComplex (.up ℤ)).obj J) ≫
    (gs).rightDerivedFunctor.map ((ΦXc).mapDerivedCategoryFactors.inv.app J)

private lemma derivedRightRep_naturality (n : ℕ)
    {J J' : CochainComplex (strictEtaleLevel X (integralExceptionalIntegers l E)
        (integralExceptionalUniformizer l E) n) ℤ} (f : J ⟶ J') :
    (ΦYc).mapDerivedCategory.map
        (DerivedCategory.Q.map (((A.right n).mapHomologicalComplex (.up ℤ)).map f)) ≫
        derivedRightRep l E g A n J' =
      derivedRightRep l E g A n J ≫ (gs).rightDerivedFunctor.map
        ((ΦXc).mapDerivedCategory.map (DerivedCategory.Q.map f)) := by
  have h₁ : (ΦYc).mapDerivedCategory.map
      (DerivedCategory.Q.map (((A.right n).mapHomologicalComplex (.up ℤ)).map f)) ≫
        (ΦYc).mapDerivedCategoryFactors.hom.app
          (((A.right n).mapHomologicalComplex (.up ℤ)).obj J') =
      (ΦYc).mapDerivedCategoryFactors.hom.app
          (((A.right n).mapHomologicalComplex (.up ℤ)).obj J) ≫
        DerivedCategory.Q.map (((ΦYc).mapHomologicalComplex (.up ℤ)).map
          (((A.right n).mapHomologicalComplex (.up ℤ)).map f)) :=
    (ΦYc).mapDerivedCategoryFactors.hom.naturality _
  have h₂ : DerivedCategory.Q.map (((ΦYc).mapHomologicalComplex (.up ℤ)).map
        (((A.right n).mapHomologicalComplex (.up ℤ)).map f)) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (integralExceptionalEtaleRight l E g A n).hom (.up ℤ)).app J') =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (integralExceptionalEtaleRight l E g A n).hom (.up ℤ)).app J) ≫
      DerivedCategory.Q.map (((gs).mapHomologicalComplex (.up ℤ)).map
        (((ΦXc).mapHomologicalComplex (.up ℤ)).map f)) := by
    rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
    exact congrArg DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
      (integralExceptionalEtaleRight l E g A n).hom (.up ℤ)).naturality f)
  have h₃ := integralExceptionalFixedRightUnit_naturality l E g n
    (((ΦXc).mapHomologicalComplex (.up ℤ)).map f)
  have h₄ : (gs).rightDerivedFunctor.map
        (DerivedCategory.Q.map (((ΦXc).mapHomologicalComplex (.up ℤ)).map f)) ≫
      (gs).rightDerivedFunctor.map ((ΦXc).mapDerivedCategoryFactors.inv.app J') =
      (gs).rightDerivedFunctor.map ((ΦXc).mapDerivedCategoryFactors.inv.app J) ≫
      (gs).rightDerivedFunctor.map
        ((ΦXc).mapDerivedCategory.map (DerivedCategory.Q.map f)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (gs).rightDerivedFunctor.map
      ((ΦXc).mapDerivedCategoryFactors.inv.naturality f)
  simp only [derivedRightRep, Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, h₄]

private lemma derivedRightRep_isIso (n : ℕ)
    (I : CochainComplex (strictEtaleLevel X (integralExceptionalIntegers l E)
        (integralExceptionalUniformizer l E) n) ℤ) (hI : I.IsKInjective) :
    IsIso (derivedRightRep l E g A n I) := by
  have : IsIso (integralExceptionalFixedRightUnit l E g n
      (((ΦXc).mapHomologicalComplex (.up ℤ)).obj I)) := by
    rw [integralExceptionalFixedRightUnit_eq]
    infer_instance
  have : IsIso ((NatTrans.mapHomologicalComplex
      (integralExceptionalEtaleRight l E g A n).hom (.up ℤ)).app I) :=
    inferInstanceAs (IsIso ((NatIso.mapHomologicalComplex
      (integralExceptionalEtaleRight l E g A n) (.up ℤ)).hom.app I))
  unfold derivedRightRep
  infer_instance

/-- The existence component of the normalized derived direct-image comparison.
Source: blueprint integral exceptional construction
(blueprint: lem-pur-adic-etale-derived-right-existence).
Proof: transport the universal right-derived pair through the exact realization
 equivalences and retain its representative unit square on every cochain complex. -/
theorem integralExceptionalEtaleDerivedRight_exists (n : ℕ)
    (B : CoefficientDerivedImage (A.lift n).modules (A.right n) (A.levelAdj n)) :
    ∃ e : B.direct ⋙ (integralExceptionalEtaleRealization l E Y n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E X n).mapDerivedCategory ⋙
        (Etale.lowerStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) g).rightDerivedFunctor,
      IsIntegralExceptionalEtaleDerivedRight l E g A n B e := by
  have := B.isRightDerived
  have : IsGrothendieckAbelian.{u + 1} (strictEtaleLevel X (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E) n) := isGrothendieckAbelian_coefficientUniverse _
  let eqY := (ΦYc).mapDerivedCategory.asEquivalence
  let ρ : (((A.right n).mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q) ⋙
      (ΦYc).mapDerivedCategory ⟶
      DerivedCategory.Q ⋙ (ΦXc).mapDerivedCategory ⋙ (gs).rightDerivedFunctor :=
    { app := fun J ↦ derivedRightRep l E g A n J
      naturality := fun _ _ f ↦ derivedRightRep_naturality l E g A n f }
  let β' : ((A.right n).mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (((ΦXc).mapDerivedCategory ⋙ (gs).rightDerivedFunctor) ⋙
        eqY.inverse) :=
    (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft _ eqY.unit ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight ρ eqY.inverse ≫
      (Functor.associator _ _ _).hom
  have hβ' (J) : β'.app J = eqY.unit.app _ ≫ eqY.inverse.map (derivedRightRep l E g A n J) := by
    simp [β', ρ]
  let δ := B.direct.rightDerivedDesc B.directUnit
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _ β'
  let τ : B.direct ⋙ (ΦYc).mapDerivedCategory ⟶
      (ΦXc).mapDerivedCategory ⋙ (gs).rightDerivedFunctor :=
    Functor.whiskerRight δ eqY.functor ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _ eqY.counit ≫ (Functor.rightUnitor _).hom
  have hτ (K) : τ.app K = eqY.functor.map (δ.app K) ≫ eqY.counit.app _ := by
    simp [τ]
  have hfac (J) : (ΦYc).mapDerivedCategory.map (B.directUnit.app J) ≫
      τ.app (DerivedCategory.Q.obj J) = derivedRightRep l E g A n J := by
    rw [hτ, ← Category.assoc]
    erw [← Functor.map_comp, B.direct.rightDerived_fac_app]
    rw [hβ', Functor.map_comp, Category.assoc]
    erw [eqY.counit.naturality (derivedRightRep l E g A n J)]
    rw [← Category.assoc]
    erw [eqY.functor_unit_comp]
    exact Category.id_comp _
  have : IsIso τ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    obtain ⟨I, hI, ⟨i⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective K
    rw [NatTrans.isIso_app_iff_of_iso τ i]
    have := B.computes I hI
    have := derivedRightRep_isIso l E g A n I hI
    rw [← hfac] at this
    exact IsIso.of_isIso_comp_left ((ΦYc).mapDerivedCategory.map (B.directUnit.app I)) _
  refine ⟨asIso τ, fun J ↦ ?_⟩
  rw [asIso_hom, reassoc_of% (hfac J)]
  simp [derivedRightRep]

/-- The uniqueness component of the normalized derived direct-image comparison.
Source: blueprint integral exceptional construction
(blueprint: lem-pur-adic-etale-derived-right-uniqueness).
Proof: cancel the exact realization factors and the universal right-derived unit;
right-derived uniqueness then identifies any two comparisons satisfying the square. -/
theorem integralExceptionalEtaleDerivedRight_unique (n : ℕ)
    (B : CoefficientDerivedImage (A.lift n).modules (A.right n) (A.levelAdj n))
    {e e' : B.direct ⋙ (integralExceptionalEtaleRealization l E Y n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E X n).mapDerivedCategory ⋙
        (Etale.lowerStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) g).rightDerivedFunctor}
    (he : IsIntegralExceptionalEtaleDerivedRight l E g A n B e)
    (he' : IsIntegralExceptionalEtaleDerivedRight l E g A n B e') : e = e' := by
  have := B.isRightDerived
  apply Iso.ext
  refine rightDerived_comp_equivalence_ext B.directUnit
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (integralExceptionalEtaleRealization l E Y n).mapDerivedCategory.asEquivalence
    _ _ fun J ↦ ?_
  have h := (he J).trans (he' J).symm
  simp only [← Category.assoc] at h
  exact (cancel_mono _).1 h

/-- Proper derived realization is uniquely fixed by the full universal-unit square on
all cochain complexes. It agrees with the underlying section map before derivation.
Source: blueprint integral exceptional construction
(blueprint: def-pur-adic-etale-realization).
Proof: exact realization is an equivalence and thus preserves K-injective complexes.
On such complexes the two right-derived units are isomorphisms; the square defines
 the comparison from the ordinary section-normalized comparison. Resolve any complex
by a K-injective one. Universal right derivation extends the comparison uniquely and
proves the square for all complexes. Its inverse is obtained from the opposite ring
coordinate equivalence, and the two composites equal the identity by the unit square. -/
theorem integralExceptionalEtaleDerivedRight_existsUnique (n : ℕ)
    (B : CoefficientDerivedImage (A.lift n).modules (A.right n) (A.levelAdj n)) :
    ∃! e : B.direct ⋙ (integralExceptionalEtaleRealization l E Y n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E X n).mapDerivedCategory ⋙
        (Etale.lowerStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) g).rightDerivedFunctor,
      IsIntegralExceptionalEtaleDerivedRight l E g A n B e := by
  obtain ⟨e, he⟩ := integralExceptionalEtaleDerivedRight_exists l E g A n B
  refine ⟨e, he, ?_⟩
  intro e' he'
  exact (integralExceptionalEtaleDerivedRight_unique l E g A n B (e := e) (e' := e') he he').symm

/-- The uniquely normalized derived right comparison, not an arbitrary natural iso.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-etale-realization). -/
@[no_expose] def integralExceptionalEtaleDerivedRight (n : ℕ)
    (B : CoefficientDerivedImage (A.lift n).modules (A.right n) (A.levelAdj n)) :
    B.direct ⋙ (integralExceptionalEtaleRealization l E Y n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E X n).mapDerivedCategory ⋙
        (Etale.lowerStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) g).rightDerivedFunctor :=
  (integralExceptionalEtaleDerivedRight_existsUnique l E g A n B).choose

end WeilConjectures
