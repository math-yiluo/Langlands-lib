/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Ordinary.OrdinaryCompletedIntegralPullback
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
public import WeilConjectures.Algebra.Homology.Ringed.RingedTopoiDerivedPullbackIndependentSupplement
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
import WeilConjectures.CategoryTheory.ContinuousRingedToposModuleDirectImage
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.LeftDerivedEquivalence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Canonical completion units and finite open--closed locality on qcqs schemes

Source: Stacks Project, Tags 099M, 09BL and 09BM; Bhatt--Scholze, Lemma 6.5.8
and Remark 6.5.10 (blueprint: def-fix-qcqs-completion-ordinary-models).

Completion and its unit are the recorded functorial strict quotient-tower product
mapping fiber. The unit has zero shifted-product coordinate. The finite tree is
presented by numbered vertices, with parents preceding their children. No chart
condition is imposed on an empty leaf. Site and coefficient universes are independent.
The ordinary ringed-pullback helpers below extend the recorded construction to those
independent universes; the existing ordinaryIntegral declarations remain imported.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOnSlice
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (f : X ⟶ Y)

/-- The actual ring direct image, with coefficient size max u (t+1).
Source: Stacks 03D2 (blueprint: def-fix-qcqs-completion-ordinary-models). -/
abbrev ordinaryRingPush := (proEtaleBaseChange f).sheafPushforwardContinuous
  RingCat.{max u (t + 1)} (ProEt.topology Y) (ProEt.topology X)

/-- Ring inverse image exists in the chosen coefficient universe.
Source: Stacks 00VC (blueprint: def-fix-qcqs-completion-ordinary-models).
Proof: transport the actual pro-etale sites to coefficientProEtaleSiteModel, which
changes only presentation sizes. Left Kan extension and sheafification give a left
adjoint there. Transport its adjunction back to the displayed ring direct image. -/
@[instance] theorem ordinaryRingPush_isRightAdjoint :
    (ordinaryRingPush.{t, u} f).IsRightAdjoint := by
  let : EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf _
  let : HasSheafify (ProEt.topology X) RingCat.{max u (t + 1)} :=
    hasSheafifyEssentiallySmallSite _ _
  have : HasColimitsOfSize.{t + 1, t + 1} RingCat.{max u (t + 1)} :=
    hasColimitsOfSizeShrink _
  let : EssentiallySmall.{t + 1} Y.ProEt := essentiallySmallSelf.{0} _
  let : LocallySmall.{t + 1} X.ProEt := ⟨fun _ _ ↦ inferInstance⟩
  have : ∀ V : X.ProEtᵒᵖ,
      HasColimitsOfShape (CostructuredArrow (proEtaleBaseChange f).op V)
        RingCat.{max u (t + 1)} := fun _ ↦
    hasColimitsOfShape_of_essentiallySmall.{t + 1} _ _
  have : ∀ F : Y.ProEtᵒᵖ ⥤ RingCat.{max u (t + 1)},
      (proEtaleBaseChange f).op.HasLeftKanExtension F := fun _ ↦ inferInstance
  exact (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (proEtaleBaseChange f) RingCat.{max u (t + 1)}
      (ProEt.topology Y) (ProEt.topology X)).isRightAdjoint

/-- The sheaf inverse image, fixed by its adjunction with actual ring direct image.
Source: Stacks 00VC (blueprint: def-fix-qcqs-completion-ordinary-models). -/
abbrev ordinaryRingInverse := (ordinaryRingPush.{t, u} f).leftAdjoint

/-- The constant-section map for the finite quotient at exponent n+1.
Source: Stacks 0H7J (blueprint: def-fix-qcqs-completion-ordinary-models). -/
def ordinaryFiniteRingMap (n : ℕ) : integralCoefficientSheaf l E Y n ⟶
    (ordinaryRingPush.{t, u} f).obj (integralCoefficientSheaf l E X n) :=
  (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
    (coefficientProEtaleDirectRingMap.{t, u} f
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))

/-- The completed ring map is determined, including every finite projection.
Source: Stacks 03CO and 0H7J (blueprint: def-fix-qcqs-completion-ordinary-models).
Proof: finite constant-section maps commute with the quotient homomorphisms by
sheafification. They form a cone. Direct image is a right adjoint and preserves
limits, so the limit universal property gives this map and its uniqueness. -/
theorem ordinaryCompletedRingMap_existsUnique :
    ∃! c : completedIntegralCoefficientSheafUnrestricted l E Y ⟶
        (ordinaryRingPush.{t, u} f).obj (completedIntegralCoefficientSheafUnrestricted l E X),
      ∀ n : ℕ, c ≫ (ordinaryRingPush.{t, u} f).map
          (limit.π (integralCoefficientSheafSystem l E X) (op n)) =
        limit.π (integralCoefficientSheafSystem l E Y) (op n) ≫
          ordinaryFiniteRingMap l E f n := by
  let G := ordinaryRingPush.{t, u} f
  let F := sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  let ρ := F.map (IntegralAmbient.coefficientMap l E f)
  have hρ (n : ℕ) : ρ ≫ G.map
      (limit.π (integralCoefficientSheafSystem l E X) (op n)) =
        limit.π (integralCoefficientSheafSystem l E Y) (op n) ≫
          ordinaryFiniteRingMap l E f n :=
    congrArg F.map ((IntegralAmbient.coefficientMap_existsUnique l E f).exists.choose_spec n)
  refine ⟨ρ, hρ, ?_⟩
  intro c hc
  apply (isLimitOfPreserves G
    (limit.isLimit (integralCoefficientSheafSystem l E X))).hom_ext
  intro n
  exact (hc n.unop).trans (hρ n.unop).symm

/-- The unique completed direct ring map with the specified finite projections.
Source: Stacks 03CO (blueprint: def-fix-qcqs-completion-ordinary-models). -/
def ordinaryCompletedRingMap := (ordinaryCompletedRingMap_existsUnique l E f).exists.choose

/-- The canonical inverse-image coefficient map, the adjoint of the limit map.
Source: Stacks 03D2 (blueprint: def-fix-qcqs-completion-ordinary-models). -/
def ordinaryCoefficientMap :
    (ordinaryRingInverse.{t, u} f).obj (completedIntegralCoefficientSheafUnrestricted l E Y) ⟶
      completedIntegralCoefficientSheafUnrestricted l E X :=
  ((Adjunction.ofIsRightAdjoint (ordinaryRingPush.{t, u} f)).homEquiv _ _).symm
        (ordinaryCompletedRingMap l E f)

/-- Module direct image with the canonical completed coefficient action.
Source: Stacks 03D1 (blueprint: def-fix-qcqs-completion-ordinary-models). -/
def ordinaryPush : Mod l E X none ⥤ Mod l E Y none :=
  SheafOfModules.pushforward.{max u (t + 1)} (F := proEtaleBaseChange f)
    (J := ProEt.topology Y) (K := ProEt.topology X) (ordinaryCompletedRingMap l E f)

/-- The canonical module direct image admits its sheafified Kan-extension left adjoint.
Source: Stacks 03D7 (blueprint: def-fix-qcqs-completion-ordinary-models).
Proof: apply module_pushforward_isRightAdjoint_of_universes with site object size t+1,
morphism size t and module size max u (t+1). No site universe is identified with u. -/
@[instance] theorem ordinaryPush_isRightAdjoint : (ordinaryPush l E f).IsRightAdjoint := by
  exact SheafOfModules.module_pushforward_isRightAdjoint_of_universes.{t + 1, t, u}
    (U := proEtaleBaseChange f) (ordinaryCompletedRingMap l E f)

/-- Ordinary pullback, before any completion, along the fixed coefficient morphism.
Source: Stacks 03D2 (blueprint: def-fix-qcqs-completion-ordinary-models). -/
def ordinaryPull : Mod l E Y none ⥤ Mod l E X none := (ordinaryPush l E f).leftAdjoint

/-- The specified sheafified Kan-extension module adjunction.
Source: Stacks 03D2 (blueprint: def-fix-qcqs-completion-ordinary-models). -/
def ordinaryAdjunction : ordinaryPull l E f ⊣ ordinaryPush l E f :=
  Adjunction.ofIsRightAdjoint (ordinaryPush l E f)

/-- Additivity of this ordinary pullback.
Source: Stacks 03D2 (blueprint: def-fix-qcqs-completion-ordinary-models).
Proof: sectionwise module direct image is additive, and its left adjoint is additive
by the preadditive adjunction criterion. -/
@[instance] theorem ordinaryPull_additive : (ordinaryPull l E f).Additive := by
  have : (ordinaryPush l E f).Additive := by
    constructor
    intro M N a b
    rfl
  exact (ordinaryAdjunction l E f).left_adjoint_additive

private theorem ordinaryAmbientRingMap :
    (⟨Functor.whiskerRight (IntegralAmbient.coefficientMap l E f).hom
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})⟩ :
      completedIntegralCoefficientSheafUnrestricted l E Y ⟶
        (ordinaryRingPush.{t, u} f).obj
          (completedIntegralCoefficientSheafUnrestricted l E X)) =
      ordinaryCompletedRingMap l E f := by
  apply (ordinaryCompletedRingMap_existsUnique l E f).unique
  · intro n
    exact congrArg
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map)
      ((IntegralAmbient.coefficientMap_existsUnique l E f).exists.choose_spec n)
  · exact (ordinaryCompletedRingMap_existsUnique l E f).exists.choose_spec

namespace OrdinaryModelProof
universe a b c d r v

private abbrev homotopyEquivalence
    {A : Type a} {B : Type b} [Category A] [Category B] [Preadditive A] [Preadditive B]
    (e : A ≌ B) [e.functor.Additive] [e.inverse.Additive] :
    HomotopyCategory A (.up ℤ) ≌ HomotopyCategory B (.up ℤ) :=
  CategoryTheory.Equivalence.mk (e.functor.mapHomotopyCategory (.up ℤ))
    (e.inverse.mapHomotopyCategory (.up ℤ))
    ((Functor.mapHomotopyCategoryIdIso A (.up ℤ)).symm ≪≫
      (Functor.mapHomotopyCategoryCompIso e.unitIso.symm (.up ℤ)).symm)
    (Functor.mapHomotopyCategoryCompIso e.counitIso (.up ℤ) ≪≫
      Functor.mapHomotopyCategoryIdIso B (.up ℤ))

private theorem kan_equivalence
    {A : Type a} {B : Type b} {D : Type c} {H : Type d}
    [Category A] [Category B] [Category D] [Category H]
    (e : A ≌ B) (L : B ⥤ D) (F : B ⥤ H) [Functor.HasRightKanExtension L F] :
    Functor.HasRightKanExtension (e.functor ⋙ L) (e.functor ⋙ F) :=
  (Functor.RightExtension.precomp L F e.functor).asEquivalence.hasTerminal_iff.mp
    inferInstance

private theorem derived_equivalence
    {A : Type a} {B : Type b} {A' : Type c} {B' : Type d}
    [Category A] [Category B] [Category A'] [Category B']
    [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
    [HasDerivedCategory.{v} A] [HasDerivedCategory.{v} B]
    [HasDerivedCategory.{v} A'] [HasDerivedCategory.{v} B']
    (e : A ≌ A') (e' : B ≌ B')
    [e.functor.Additive] [e.inverse.Additive] [e'.functor.Additive] [e'.inverse.Additive]
    (F : A ⥤ B) (G : A' ⥤ B') [F.Additive] [G.Additive]
    (i : e.functor ⋙ G ≅ F ⋙ e'.functor)
    [(G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso A' (.up ℤ))] :
    (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso A (.up ℤ)) := by
  let eh := homotopyEquivalence e
  let q := DerivedCategory.Qh (C := A)
  let q' := DerivedCategory.Qh (C := A')
  let g := G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let f := F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  have : Functor.HasRightKanExtension q' g :=
    (Functor.hasLeftDerivedFunctor_iff g q'
      (HomotopyCategory.quasiIso A' (.up ℤ))).mp inferInstance
  have := kan_equivalence eh q' g
  let il : q ⋙ e.functor.mapDerivedCategory ≅ eh.functor ⋙ q' :=
    by exact e.functor.mapDerivedCategoryFactorsh
  have h : Functor.HasRightKanExtension q (eh.functor ⋙ g) :=
    (Functor.hasRightExtension_iff_postcomp₁ il _).mp inferInstance
  let j : eh.functor ⋙ g ≅ f ⋙ e'.functor.mapDerivedCategory :=
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso i (.up ℤ) ≪≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).symm)
        DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (F.mapHomotopyCategory (.up ℤ))
      e'.functor.mapDerivedCategoryFactorsh.symm ≪≫ (Functor.associator _ _ _).symm
  have : Functor.HasRightKanExtension q (f ⋙ e'.functor.mapDerivedCategory) :=
    (Functor.hasRightExtension_iff_of_iso₂ q j).mp h
  let hF := q.rightKanExtension (f ⋙ e'.functor.mapDerivedCategory)
  let hα := q.rightKanExtensionCounit (f ⋙ e'.functor.mapDerivedCategory)
  have := Functor.isRightKanExtension_comp_of_isEquivalence hF hα
    e'.inverse.mapDerivedCategory
  let k : (f ⋙ e'.functor.mapDerivedCategory) ⋙ e'.inverse.mapDerivedCategory ≅ f :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft f
      (Functor.mapDerivedCategoryCompIso e'.functor e'.inverse ≪≫
        Functor.mapDerivedCategoryNatIso e'.unitIso.symm ≪≫ Functor.mapDerivedCategoryIdIso B)
      ≪≫ f.rightUnitor
  have : Functor.HasRightKanExtension q
      ((f ⋙ e'.functor.mapDerivedCategory) ⋙ e'.inverse.mapDerivedCategory) :=
    Functor.HasRightKanExtension.mk (hF ⋙ e'.inverse.mapDerivedCategory)
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight hα e'.inverse.mapDerivedCategory)
  exact (Functor.hasLeftDerivedFunctor_iff f q
    (HomotopyCategory.quasiIso A (.up ℤ))).mpr
      ((Functor.hasRightExtension_iff_of_iso₂ q k).mp inferInstance)

private theorem small_pull_derived
    {C D : Type r} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : D ⥤ C) [F.IsContinuous K J] [RepresentablyFlat F]
    (R : Sheaf J CommRingCat.{r}) (S : Sheaf K CommRingCat.{r})
    (φ : S ⟶ (F.sheafPushforwardContinuous CommRingCat.{r} K J).obj R)
    [HasDerivedCategory.{v} (SheafOfModules.{r}
      ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj S))]
    [HasDerivedCategory.{v} (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))] :
    ∃ (G : SheafOfModules.{r}
        ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj S) ⥤
      SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
      (_hG : G.Additive) (_adj : G ⊣ SheafOfModules.pushforward
        ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).map φ)),
      (G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  classical
  let : HasSheafify J (Type r) := hasSheafifyEssentiallySmallSite _ _
  let : HasSheafify K (Type r) := hasSheafifyEssentiallySmallSite _ _
  let L := F.sheafPullback (Type r) K J
  let adj := F.sheafAdjunctionContinuous (Type r) K J
  let : ReflectsLimits (forget (Type r)) := reflectsLimits_of_reflectsIsomorphisms
  let : PreservesFiniteLimits (F.op.lan : (Dᵒᵖ ⥤ Type r) ⥤ Cᵒᵖ ⥤ Type r) :=
    lan_preservesFiniteLimits_of_flat (Type r) F
  have : PreservesFiniteLimits L :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits F (Type r) K J
  obtain ⟨f, hf⟩ := continuousRingedToposModuleDirectImage_exists F L adj R S φ
  obtain ⟨G, hG, am, _, hpres⟩ := f.exists_kFlatPullback J K R S
  let := hG
  let A := SheafOfModules.{r} ((sheafCompose K
    (forget₂ CommRingCat.{r} RingCat.{r})).obj S)
  let B := SheafOfModules.{r} ((sheafCompose J
    (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
  let π := HomotopyCategory.quotient A (.up ℤ)
  let GF := G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let P : Set (HomotopyCategory A (.up ℤ)) :=
    {X | ∃ M : CochainComplex A ℤ, π.obj M = X ∧
      M.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (M.X n).IsFlat}
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (X' : HomotopyCategory A (.up ℤ)) (s : X' ⟶ X),
        X' ∈ P ∧ HomotopyCategory.quasiIso A (.up ℤ) s := by
    intro X
    obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨M, s, hM, hf, hs, _⟩ := CochainComplex.exists_isKFlatResolution X
    exact ⟨π.obj M, π.map s, ⟨M, rfl, hM, hf⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have hinv : ∀ (X Y : HomotopyCategory A (.up ℤ)) (s : X ⟶ Y),
      X ∈ P → Y ∈ P → HomotopyCategory.quasiIso A (.up ℤ) s → IsIso (GF.map s) := by
    intro X Y s hX hY hs
    obtain ⟨X, rfl, hX, hfX⟩ := hX
    obtain ⟨Y, rfl, hY, hfY⟩ := hY
    obtain ⟨s, rfl⟩ := π.map_surjective s
    have hq := (HomotopyCategory.quotient_map_mem_quasiIso_iff s).1 hs
    have ht := hpres X Y s hX hfX hY hfY hq
    change IsIso (DerivedCategory.Qh.map
      ((G.mapHomotopyCategory (.up ℤ)).map (π.map s)))
    rw [Functor.mapHomotopyCategory_map]
    exact Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso B (.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 ht)
  obtain ⟨_, LF, ε, hLF, _, _⟩ :=
    Functor.leftDerived_from_resolvingClass A (DerivedCategory.{v} B) GF P hres hinv
  let := hLF
  refine ⟨G, hG, am.ofNatIsoRight (eqToIso hf), ?_⟩
  exact Functor.HasLeftDerivedFunctor.mk' LF ε

private abbrev model (X : Scheme.{t}) := coefficientProEtaleSiteModel.{t, u} X
private abbrev top (X : Scheme.{t}) := coefficientProEtaleModelTopology.{t, u} X

private def modelRing (X : Scheme.{t}) :=
  ((AsSmall.down : model.{t, u} X ⥤ X.ProEt).sheafPushforwardContinuous
    CommRingCat.{max u (t + 1)} (top X) (ProEt.topology X)).obj
      (completedIntegralCommRingSheafUnrestricted l E X)

private def modelBackMap (X : Scheme.{t}) :
    completedIntegralCoefficientSheafUnrestricted l E X ⟶
      ((AsSmall.up : X.ProEt ⥤ model.{t, u} X).sheafPushforwardContinuous
        RingCat.{max u (t + 1)} (ProEt.topology X) (top X)).obj
          ((sheafCompose (top X) (forget₂ CommRingCat RingCat)).obj (modelRing l E X)) :=
  ⟨{ app := fun _ ↦ 𝟙 _
     naturality := by intros; simp only [Category.id_comp, Category.comp_id]; rfl }⟩

private def moduleEquivalence (X : Scheme.{t}) :
    Mod l E X none ≌ SheafOfModules.{max u (t + 1)}
      ((sheafCompose (top.{t, u} X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
          (modelRing l E X)) := by
  let e := (AsSmall.equiv.{t, t + 1, max u (t + 1)} (C := X.ProEt)).symm
  let R := completedIntegralCoefficientSheafUnrestricted l E X
  let S := ((AsSmall.down : model.{t, u} X ⥤ X.ProEt).sheafPushforwardContinuous
    RingCat.{max u (t + 1)} (top X) (ProEt.topology X)).obj R
  let : e.functor.IsContinuous (top X) (ProEt.topology X) :=
    inferInstanceAs ((AsSmall.down : model.{t, u} X ⥤ X.ProEt).IsContinuous
      ((AsSmall.down : model.{t, u} X ⥤ X.ProEt).inducedTopology (ProEt.topology X))
      (ProEt.topology X))
  let : e.inverse.IsContinuous (ProEt.topology X) (top X) :=
    coefficientProEtaleModelUp_isContinuous X
  let φ : S ⟶ (e.functor.sheafPushforwardContinuous RingCat (top X)
      (ProEt.topology X)).obj R := 𝟙 _
  let ψ : R ⟶ (e.inverse.sheafPushforwardContinuous RingCat (ProEt.topology X)
      (top X)).obj S := modelBackMap l E X
  change SheafOfModules R ≌ SheafOfModules S
  exact SheafOfModules.pushforwardPushforwardEquivalence
    (J := top X) (K := ProEt.topology X) e φ ψ
    (by
      ext U : 2
      change R.obj.map (𝟙 _) = 𝟙 _ ≫ 𝟙 _
      simp)
    (by
      ext U : 2
      change 𝟙 _ ≫ 𝟙 _ ≫ R.obj.map (𝟙 _) = 𝟙 _
      simp)

private theorem moduleEquivalence_inverse (X : Scheme.{t}) :
    (moduleEquivalence l E X).inverse = SheafOfModules.pushforward (modelBackMap l E X) := rfl

private def modelMap : modelRing l E Y ⟶
    ((coefficientProEtaleModelBaseChange.{t, u} f).sheafPushforwardContinuous
      CommRingCat.{max u (t + 1)} (top Y) (top X)).obj (modelRing l E X) :=
  ⟨{ app := fun U ↦
       letI := completedIntegralCoefficientCommRingUnrestricted l E Y (AsSmall.down.op.obj U)
       letI := completedIntegralCoefficientCommRingUnrestricted l E X
         (AsSmall.down.op.obj ((coefficientProEtaleModelBaseChange.{t, u} f).op.obj U))
       CommRingCat.ofHom
         ((ordinaryCompletedRingMap l E f).hom.app (AsSmall.down.op.obj U)).hom
     naturality := by
       intro U V h
       ext x
       exact congrArg (fun g ↦ g.hom x)
         ((ordinaryCompletedRingMap l E f).hom.naturality (AsSmall.down.op.map h)) }⟩

end OrdinaryModelProof

private def ordinaryModelPushIso :
    (OrdinaryModelProof.moduleEquivalence l E X).inverse ⋙ ordinaryPush l E f ≅
      SheafOfModules.pushforward
        ((sheafCompose (OrdinaryModelProof.top Y)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
            (OrdinaryModelProof.modelMap l E f)) ⋙
              (OrdinaryModelProof.moduleEquivalence l E Y).inverse := by
  rw [OrdinaryModelProof.moduleEquivalence_inverse,
    OrdinaryModelProof.moduleEquivalence_inverse]
  refine NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦ ?_) ?_)) ?_
  · refine ModuleCat.isoMk (Iso.refl _) ?_
    intro a
    ext x
    rfl
  · intros
    ext x
    rfl
  · intros
    ext U x
    rfl

/-- Existence of ordinary total derived pullback, with its universal comparison.
Source: Stacks 06YY (blueprint: def-fix-qcqs-completion-ordinary-models).
Proof: apply lem-weil-pbc-ringed-topoi-derived-pullback to the specified ringed
inverse image and its module adjunction. Flat-term K-flat resolutions exist in the
independent coefficient universe.
Ringed inverse image preserves quasi-isomorphisms between these resolutions.
The resolving-class localization therefore gives the total left derived functor. -/
@[instance] theorem ordinaryPull_hasLeftDerived :
    ((ordinaryPull l E f).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Mod l E Y none) (.up ℤ)) := by
  classical
  let R := OrdinaryModelProof.modelRing l E X
  let S := OrdinaryModelProof.modelRing l E Y
  let eX := OrdinaryModelProof.moduleEquivalence l E X
  let eY := OrdinaryModelProof.moduleEquivalence l E Y
  have : eX.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : eX.inverse.Additive := Functor.additive_of_preserves_binary_products _
  have : eY.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : eY.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let : HasDerivedCategory.{max u (t + 1) + 1} (SheafOfModules.{max u (t + 1)}
      ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory.{max u (t + 1) + 1} (SheafOfModules.{max u (t + 1)}
      ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj S)) :=
    HasDerivedCategory.standard _
  let : (AsSmall.down : OrdinaryModelProof.model.{t, u} Y ⥤ Y.ProEt).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{t, t + 1, max u (t + 1)}
      (C := Y.ProEt)).inverse.IsEquivalence
  let : (AsSmall.up : X.ProEt ⥤ OrdinaryModelProof.model.{t, u} X).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{t, t + 1, max u (t + 1)}
      (C := X.ProEt)).functor.IsEquivalence
  let F := coefficientProEtaleModelBaseChange.{t, u} f
  have : PreservesFiniteLimits F := by
    dsimp [F, coefficientProEtaleModelBaseChange]
    infer_instance
  have : RepresentablyFlat F := flat_of_preservesFiniteLimits F
  obtain ⟨G, hG, am, hder⟩ := OrdinaryModelProof.small_pull_derived
    (OrdinaryModelProof.top X) (OrdinaryModelProof.top Y) F R S
      (OrdinaryModelProof.modelMap l E f)
  let := hG
  let := hder
  let am' := eY.toAdjunction.comp am
  let bm' := (ordinaryAdjunction l E f).comp eX.toAdjunction
  let k := ordinaryModelPushIso l E f
  let i : eY.functor ⋙ G ≅ ordinaryPull l E f ⋙ eX.functor :=
    am'.leftAdjointUniq (bm'.ofNatIsoRight k)
  exact OrdinaryModelProof.derived_equivalence eY eX (ordinaryPull l E f) G i

/-- The ordinary unbounded derived pullback of completed-coefficient modules.
Source: Stacks 06YY (blueprint: def-fix-qcqs-completion-ordinary-models). -/
def ordinaryDerivedPull : D l E Y none ⥤ D l E X none :=
  ((ordinaryPull l E f).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).totalLeftDerived
    DerivedCategory.Qh (HomotopyCategory.quasiIso (Mod l E Y none) (.up ℤ))

/-- Termwise ordinary pullback, retaining the strict differentials and quotient maps.
Source: Stacks 06YY (blueprint: def-fix-qcqs-completion-ordinary-models). -/
def ordinaryComplexPull : Cx l E Y none ⥤ Cx l E X none :=
  (ordinaryPull l E f).mapHomologicalComplex (.up ℤ)

end WeilConjectures.IntegralOnSlice

namespace WeilConjectures.IntegralOnSlice
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (f : X ⟶ Y)

/-- The ordinary derived counit on an arbitrary cochain representative.
Source: Stacks 06YY (blueprint: def-fix-qcqs-completion-ordinary-models). -/
def ordinaryComplexCounit (P : Cx l E Y none) :
    (ordinaryDerivedPull l E f).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((ordinaryComplexPull l E f).obj P) :=
  (ordinaryDerivedPull l E f).map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
    (((ordinaryPull l E f).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh).totalLeftDerivedCounit DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Mod l E Y none) (.up ℤ))).app
          ((HomotopyCategory.quotient _ _).obj P) ≫
    DerivedCategory.Qh.map
      (((ordinaryPull l E f).mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app ((ordinaryComplexPull l E f).obj P)

/-- The product endomorphism 1-s of the already recorded strict quotient tower.
Source: Stacks 0941 (blueprint: def-fix-qcqs-completion-ordinary-models). -/
def ordinaryRoosEndomorphism (P : Cx l E Y none) :=
  towerTransitionEndomorphism
    (K := fun n : ℕ ↦ ((tower l E Y none).obj P).obj (op n))
    (integralOperationsTowerStep ((tower l E Y none).obj P))

end WeilConjectures.IntegralOnSlice

namespace WeilConjectures.IntegralOnSlice
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (f : X ⟶ Y)

private def ordinaryAmbientPushIso : IntegralAmbient.push l E f ≅ ordinaryPush l E f :=
  SheafOfModules.pushforwardCongr (ordinaryAmbientRingMap l E f)

private def ordinaryAmbientPullIso : ordinaryPull l E f ≅ IntegralAmbient.pull l E f :=
  Adjunction.leftAdjointUniq (ordinaryAdjunction l E f)
    ((IntegralAmbient.adjunction l E f).ofNatIsoRight (ordinaryAmbientPushIso l E f))

private theorem ordinaryAmbientPullIso_unit
    (M : integralTowerModules l E Y) (V : Y.ProEt) (x : M.val.obj (op V)) :
    ((ordinaryAmbientPullIso l E f).hom.app M).val.app
        (op ((proEtaleBaseChange f).obj V))
      (((ordinaryAdjunction l E f).unit.app M).val.app (op V) x) =
      IntegralAmbient.pullSection l E f M V x := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (ordinaryAdjunction l E f)
    ((IntegralAmbient.adjunction l E f).ofNatIsoRight (ordinaryAmbientPushIso l E f)) M
  exact congrArg (fun a ↦ a.val.app (op V) x) h

private def ordinaryAmbientComplexIso :
    ordinaryComplexPull l E f ≅ IntegralAmbient.pullComplex l E f := by
  let := IntegralAmbient.pull_additive l E f
  exact NatIso.mapHomologicalComplex (ordinaryAmbientPullIso l E f) (.up ℤ)

private def ordinaryAugmentation :
    ordinaryComplexPull l E f ⋙
        (Functor.const ℕᵒᵖ : CochainComplex (integralTowerModules l E X) ℤ ⥤ _) ⟶
      integralOperationsPullbackTowerFunctor l E f :=
  Functor.whiskerRight (ordinaryAmbientComplexIso l E f).hom (Functor.const ℕᵒᵖ) ≫
    Functor.whiskerLeft (IntegralAmbient.pullComplex l E f)
      (augmentation l E X none) ≫
    (IntegralAmbient.pullTowerIso l E f).hom

private theorem ordinaryAugmentation_formula
    (P : Cx l E Y none) (n : ℕ) (i : ℤ)
    (V : Y.ProEt) (x : (P.X i).val.obj (op V)) :
    ((((ordinaryAugmentation l E f).app P).app (op n)).f i).val.app
        (op ((proEtaleBaseChange f).obj V))
      (((ordinaryAdjunction l E f).unit.app (P.X i)).val.app (op V) x) =
      integralOperationsPullbackGenerator l E f n
        (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V
        (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) 1 x) := by
  have ha := (augmentation_existsUnique l E X none).exists.choose_spec
    ((IntegralAmbient.pullComplex l E f).obj P) n i
    (op ((proEtaleBaseChange f).obj V))
    (IntegralAmbient.pullSection l E f (P.X i) V x)
  have hb := (IntegralAmbient.pullTowerModel l E f).exists.choose_spec P n i V 1 x
  change (((((IntegralAmbient.pullTowerIso l E f).hom.app P).app (op n)).f i).val.app
    (op ((proEtaleBaseChange f).obj V))
      (((((augmentation l E X none).app
        ((IntegralAmbient.pullComplex l E f).obj P)).app (op n)).f i).val.app
        (op ((proEtaleBaseChange f).obj V))
          (((ordinaryAmbientPullIso l E f).hom.app (P.X i)).val.app
            (op ((proEtaleBaseChange f).obj V))
            (((ordinaryAdjunction l E f).unit.app (P.X i)).val.app (op V) x)))) = _
  rw [ordinaryAmbientPullIso_unit]
  exact (congrArg (((((IntegralAmbient.pullTowerIso l E f).hom.app P).app
    (op n)).f i).val.app (op ((proEtaleBaseChange f).obj V))) ha).trans
    (by
      change _ = IntegralAmbient.finitePullSection l E f n P i V 1 x at hb
      have hc : IntegralAmbient.finitePullSection l E f n P i V 1 x =
          integralOperationsPullbackGenerator l E f n
            (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V
            (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) 1 x) := by
        dsimp only [IntegralAmbient.finitePullSection]
        exact one_smul _ _
      exact hb.trans hc)

/-- The quotient maps, as one natural map of strict towers, are uniquely fixed on generators.
The formula is 1 tensor q ↦ 1 tensor (q tensor 1); completed linearity gives
b tensor q ↦ 1 tensor (q tensor pi_n(b)) on every inverse-image generator.
Source: Bhatt--Scholze, Lemma 6.5.9; Stacks 06YY, 08TC
(blueprint: def-fix-qcqs-completion-ordinary-models).
Proof: the completed coefficient map commutes with each quotient by its defining
projection equation. Thus the displayed map is balanced, linear and restriction
compatible. Sheafification gives the module maps; applying them degreewise gives
chain maps. Coefficient reduction preserves one, so consecutive transition squares
commute. The same generator equality proves naturality. Locally the scalar multiples
of restrictions of adjunction-unit generators generate pullback, giving uniqueness. -/
theorem ordinaryQuotientAugmentation_existsUnique :
    ∃! a : ordinaryComplexPull l E f ⋙
        (Functor.const ℕᵒᵖ : CochainComplex (integralTowerModules l E X) ℤ ⥤ _) ⟶
      integralOperationsPullbackTowerFunctor l E f,
      ∀ (P : Cx l E Y none) (n : ℕ) (i : ℤ)
        (V : Y.ProEt) (x : (P.X i).val.obj (op V)),
        (((a.app P).app (op n)).f i).val.app (op ((proEtaleBaseChange f).obj V))
          (((ordinaryAdjunction l E f).unit.app (P.X i)).val.app (op V) x) =
        integralOperationsPullbackGenerator l E f n
          (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V
          (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) 1 x) := by
  refine ⟨ordinaryAugmentation l E f, ordinaryAugmentation_formula l E f, ?_⟩
  intro a ha
  apply NatTrans.ext
  funext P
  apply NatTrans.ext
  funext n
  apply HomologicalComplex.hom_ext
  intro i
  apply ((ordinaryAdjunction l E f).homEquiv _ _).injective
  ext V x
  change (((a.app P).app n).f i).val.app
      (op ((proEtaleBaseChange f).obj V.unop))
      (((ordinaryAdjunction l E f).unit.app (P.X i)).val.app V x) = _
  exact (ha P n.unop i V.unop x).trans
    (ordinaryAugmentation_formula l E f P n.unop i V.unop x).symm

/-- The actual quotient augmentation, with all quotient transitions retained.
Source: Bhatt--Scholze, Lemma 6.5.9; Stacks 08TC
(blueprint: def-fix-qcqs-completion-ordinary-models). -/
def ordinaryQuotientAugmentation :=
  (ordinaryQuotientAugmentation_existsUnique l E f).exists.choose

/-- The product of the specified quotient maps.
Source: Stacks 08TC (blueprint: def-fix-qcqs-completion-ordinary-models). -/
def ordinaryProductAugmentation
    (P : Cx l E Y none) :
    (ordinaryComplexPull l E f).obj P ⟶
      ∏ᶜ (fun n : ℕ ↦ ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n)) :=
  Pi.lift (fun n ↦ ((ordinaryQuotientAugmentation l E f).app P).app (op n))

/-- The strict quotient augmentation is killed by 1-s, with zero second cone cochain.
Source: Stacks 08TC (blueprint: def-fix-qcqs-completion-ordinary-models).
Proof: after every product projection, the composite with 1-s is the difference
between consecutive quotient maps and is zero by the strict tower's naturality.
The differential of the zero cochain is zero. Product projections are jointly monic. -/
theorem ordinaryCompletionChain_condition
    (P : Cx l E Y none) :
    CochainComplex.HomComplex.δ (-1) 0
      (0 : CochainComplex.HomComplex.Cochain ((ordinaryComplexPull l E f).obj P)
        (∏ᶜ fun n : ℕ ↦
          ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (ordinaryProductAugmentation l E f P ≫
          towerTransitionEndomorphism
            (K := fun n : ℕ ↦
              ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n))
            (integralOperationsTowerStep
              ((integralOperationsPullbackTowerFunctor l E f).obj P))) = 0 := by
  have h : ordinaryProductAugmentation l E f P ≫
      towerTransitionEndomorphism
        (K := fun n : ℕ ↦
          ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n))
        (integralOperationsTowerStep
          ((integralOperationsPullbackTowerFunctor l E f).obj P)) = 0 := by
    apply Pi.hom_ext
    intro n
    have hn := ((ordinaryQuotientAugmentation l E f).app P).naturality
      (homOfLE (Nat.le_succ n)).op
    simpa [ordinaryProductAugmentation, towerTransitionEndomorphism, towerProductShift,
      integralOperationsTowerStep, Category.assoc] using sub_eq_zero.mpr hn
  rw [h]
  simp

/-- The prescribed chain map into Cone(1-s)[-1]: quotient maps and zero, respectively.
Source: Stacks 08TC (blueprint: def-fix-qcqs-completion-ordinary-models). -/
def ordinaryCompletionChain
    (P : Cx l E Y none) :
    (ordinaryComplexPull l E f).obj P ⟶
      (integralOperationsPullbackComplexFunctor l E f).obj P :=
  CochainComplex.mappingCocone.lift
    (towerTransitionEndomorphism
      (K := fun n : ℕ ↦ ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n))
      (integralOperationsTowerStep ((integralOperationsPullbackTowerFunctor l E f).obj P)))
    (ordinaryProductAugmentation l E f P) 0
    (ordinaryCompletionChain_condition l E f P)

end WeilConjectures.IntegralOnSlice
