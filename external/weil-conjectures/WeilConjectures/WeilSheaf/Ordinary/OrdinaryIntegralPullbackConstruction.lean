/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
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
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
import all WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
import WeilConjectures.Algebra.Homology.Ringed.RingedTopoiDerivedPullbackIndependentSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
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
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.Algebra.Category.Grp.Colimits
import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
import all WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import all WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import all WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import all WeilConjectures.CategoryTheory.ModuleInverseImageAction
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import all WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-!
# Ordinary integral pullback and its normalized completion comparison

Source: Bhatt--Scholze, Lemma 6.5.9, Proposition 6.6.11 and Remark 6.8.15;
Stacks Project, Tags 06YY and 08TC
(blueprint: lem-tw-ordinary-completed-integral-pullback).

The ordinary pullback uses the adjoint of the completed coefficient map fixed by
all finite projections. The comparison is fixed on flat-term K-flat representatives
by the quotient augmentation and the zero second coordinate of the strict Roos cone.

## Main definitions

* `ordinaryIntegralDerivedPull`: ordinary unbounded ringed pullback before completion.
* `ordinaryIntegralCompletionChain`: the prescribed (quotients, zero) cone map.
* `ordinaryIntegralCompletionComparison`: its uniquely normalized derived descent.

The constructibility and invertibility theorem remains in
`WeilConjectures.WeilSheaf.Ordinary.OrdinaryCompletedIntegralPullback`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.scalarReductionSourceDerived
attribute [-instance] WeilConjectures.scalarReductionTargetDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local instance 3000] WeilConjectures.integralTowerHasDerivedCategory

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

private instance ordinarySiteSmall (W : Scheme.{u}) :
    EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0} _

/-- The finite constant coefficient map adjoint to the constant-section inverse-image map.
Source: Stacks 0H7J (blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralFiniteDirectRingMap (n : ℕ) :
    integralCoefficientSheaf l E Y n ⟶
      (proEtaleSheafDirectImage f RingCat.{u + 1}).obj (integralCoefficientSheaf l E X n) :=
  (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (coefficientProEtaleDirectRingMap.{u, u} f
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))

private theorem ordinaryConstantUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : CommRingCat.{u + 1}) (U : Y.ProEtᵒᵖ) :
    (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app U ≫
      (coefficientProEtaleDirectRingMap.{u, u} f A).hom.app U =
    (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
      ((proEtaleBaseChange f).op.obj U) := by
  have h := (sheafificationAdjunction (ProEt.topology Y)
      CommRingCat.{u + 1}).homEquiv ((Functor.const Y.ProEtᵒᵖ).obj A)
        (((proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{u + 1}
          (ProEt.topology Y) (ProEt.topology X)).obj
            ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj A))
      |>.apply_symm_apply (Functor.whiskerLeft (proEtaleBaseChange f).op
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)))
  exact congrArg (fun α ↦ α.app U) h

private theorem ordinaryConstantMap_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : CommRingCat.{u + 1}} (a : A ⟶ B) :
    (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map a ≫
      coefficientProEtaleDirectRingMap.{u, u} f B =
    coefficientProEtaleDirectRingMap.{u, u} f A ≫
      ((proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{u + 1}
        (ProEt.topology Y) (ProEt.topology X)).map
          ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map a) := by
  apply (sheafificationAdjunction (ProEt.topology Y)
      CommRingCat.{u + 1}).homEquiv ((Functor.const Y.ProEtᵒᵖ).obj A)
        (((proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{u + 1}
          (ProEt.topology Y) (ProEt.topology X)).obj
            ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj B)) |>.injective
  apply NatTrans.ext
  funext U
  change _ ≫ (_ ≫ _) = _ ≫ (_ ≫ _)
  have hY := congrArg (fun α ↦ α.app U)
    (toSheafify_naturality (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).map a))
  change a ≫ _ = _ ≫ _ at hY
  erw [← Category.assoc, ← hY, Category.assoc, ordinaryConstantUnit,
    ← Category.assoc, ordinaryConstantUnit]
  exact congrArg (fun α ↦ α.app ((proEtaleBaseChange f).op.obj U))
    (toSheafify_naturality (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).map a))

attribute [local irreducible] constantSheaf HasDerivedCategory.standard

/-- The adjoint completed ring map is uniquely determined by all its quotient projections.
Its inverse-image adjoint is exactly c_f of the statement.
Source: Bhatt--Scholze, Lemma 6.5.9; Stacks 06YY
(blueprint: lem-tw-ordinary-completed-integral-pullback).
Proof: the constant-section maps commute with quotient transitions, by their
sheafification universal property. Right adjoint direct image preserves limits.
The limit universal property supplies the displayed map and proves uniqueness. -/
theorem ordinaryIntegralDirectRingMap_existsUnique :
    ∃! ρ : completedIntegralCoefficientSheafUnrestricted l E Y ⟶
        (proEtaleSheafDirectImage f RingCat.{u + 1}).obj
          (completedIntegralCoefficientSheafUnrestricted l E X),
      ∀ n : ℕ, ρ ≫ (proEtaleSheafDirectImage f RingCat.{u + 1}).map
          (limit.π (integralCoefficientSheafSystem l E X) (op n)) =
        limit.π (integralCoefficientSheafSystem l E Y) (op n) ≫
          ordinaryIntegralFiniteDirectRingMap l E f n := by
  let G := proEtaleSheafDirectImage f RingCat.{u + 1}
  let τ : integralCoefficientSheafSystem l E Y ⟶
      integralCoefficientSheafSystem l E X ⋙ G :=
    NatTrans.ofOpSequence (ordinaryIntegralFiniteDirectRingMap l E f) (fun n ↦ by
      simp only [integralCoefficientSheafSystem, Functor.comp_map,
        Functor.ofOpSequence_map_homOfLE_succ]
      exact congrArg
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map)
        (ordinaryConstantMap_naturality f
          (CommRingCat.ofHom (Padic.coefficientExtensionTransition l E (n + 1)).ulift)))
  let c : Cone (integralCoefficientSheafSystem l E X ⋙ G) :=
    { pt := completedIntegralCoefficientSheafUnrestricted l E Y
      π := (limit.cone (integralCoefficientSheafSystem l E Y)).π ≫ τ }
  let hc := isLimitOfPreserves G (limit.isLimit (integralCoefficientSheafSystem l E X))
  refine ⟨hc.lift c, ?_, ?_⟩
  · intro n
    exact hc.fac c (op n)
  · intro ρ hρ
    apply hc.hom_ext
    intro n
    exact (hρ n.unop).trans (hc.fac c n).symm

attribute [local irreducible] limit

/-- The canonical completed coefficient map, in its direct-image adjoint form.
Source: Bhatt--Scholze, Lemma 6.5.9
(blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralDirectRingMap :=
  (ordinaryIntegralDirectRingMap_existsUnique l E f).exists.choose

attribute [local irreducible] ordinaryIntegralDirectRingMap

/-- The actual sectionwise module direct image with this completed coefficient action.
Source: Stacks 03D1 (blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralModulePush : integralTowerModules l E X ⥤ integralTowerModules l E Y :=
  SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
    (J := ProEt.topology Y) (K := ProEt.topology X) (ordinaryIntegralDirectRingMap l E f)

/-- The specified pushforward has the sheafified module Kan-extension left adjoint.
Source: Stacks 03D2 (blueprint: lem-tw-ordinary-completed-integral-pullback).
Proof: transport to the already recorded small site models, form the presheaf
module Kan extension along the displayed ring map and sheafify. Transport its
adjunction back. Its right adjoint is the specified sectionwise module pushforward.
The left adjoint is B_X tensor over f-inverse B_Y with f-inverse of the module. -/
@[instance] theorem ordinaryIntegralModulePush_isRightAdjoint :
    (ordinaryIntegralModulePush l E f).IsRightAdjoint := by
  exact SheafOfModules.module_pushforward_isRightAdjoint_of_universes.{u + 1, u, u}
    (U := proEtaleBaseChange f) (ordinaryIntegralDirectRingMap l E f)

/-- Ordinary ringed module pullback, fixed by its sheafified Kan-extension adjunction.
Source: Stacks 03D2 (blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralModulePull :
    integralTowerModules l E Y ⥤ integralTowerModules l E X :=
  letI : (SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
      (J := ProEt.topology Y) (K := ProEt.topology X)
      (ordinaryIntegralDirectRingMap l E f)).IsRightAdjoint :=
    ordinaryIntegralModulePush_isRightAdjoint l E f
  SheafOfModules.pullback.{u + 1} (F := proEtaleBaseChange f)
    (J := ProEt.topology Y) (K := ProEt.topology X) (ordinaryIntegralDirectRingMap l E f)

/-- The adjunction supplying the canonical tensor generators of ordinary pullback.
Source: Stacks 03D2 (blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralModuleAdjunction :
    ordinaryIntegralModulePull l E f ⊣ ordinaryIntegralModulePush l E f :=
  letI : (SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
      (J := ProEt.topology Y) (K := ProEt.topology X)
      (ordinaryIntegralDirectRingMap l E f)).IsRightAdjoint :=
    ordinaryIntegralModulePush_isRightAdjoint l E f
  SheafOfModules.pullbackPushforwardAdjunction (F := proEtaleBaseChange f)
    (J := ProEt.topology Y) (K := ProEt.topology X) (ordinaryIntegralDirectRingMap l E f)

/-- Additivity of ordinary module pullback.
Source: Stacks 03D2 (blueprint: lem-tw-ordinary-completed-integral-pullback).
Proof: sectionwise pushforward is additive. Its adjunction makes its left adjoint
additive by the preadditive adjunction criterion. -/
@[instance] theorem ordinaryIntegralModulePull_additive :
    (ordinaryIntegralModulePull l E f).Additive := by
  have : (ordinaryIntegralModulePush l E f).Additive := by
    refine ⟨?_⟩
    intro M N a b
    rfl
  exact (ordinaryIntegralModuleAdjunction l E f).left_adjoint_additive

attribute [local irreducible] ordinaryIntegralModulePull

private theorem ordinaryAmbientRingMap :
    (⟨Functor.whiskerRight (IntegralAmbient.coefficientMap l E f).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩ :
      completedIntegralCoefficientSheafUnrestricted l E Y ⟶
        (proEtaleSheafDirectImage f RingCat.{u + 1}).obj
          (completedIntegralCoefficientSheafUnrestricted l E X)) =
      ordinaryIntegralDirectRingMap l E f := by
  apply (ordinaryIntegralDirectRingMap_existsUnique l E f).unique
  · intro n
    exact congrArg
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map)
      ((IntegralAmbient.coefficientMap_existsUnique l E f).exists.choose_spec n)
  · simpa only [ordinaryIntegralDirectRingMap] using
      (ordinaryIntegralDirectRingMap_existsUnique l E f).exists.choose_spec

private def ordinaryAmbientPushIso :
    IntegralAmbient.push l E f ≅ ordinaryIntegralModulePush l E f :=
  SheafOfModules.pushforwardCongr (ordinaryAmbientRingMap l E f)

private def ordinaryTensorRingMap :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (completedIntegralCommRingSheafUnrestricted l E Y) ⟶
      completedIntegralCommRingSheafUnrestricted l E X :=
  ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).symm
    (IntegralAmbient.coefficientMap l E f)

private def ordinaryTensorPull : integralTowerModules l E Y ⥤ integralTowerModules l E X :=
  proEtaleModuleInverseImage f (completedIntegralCommRingSheafUnrestricted l E Y) ⋙
    SheafOfModules.ScalarReductionProof.tensorFunctor.{u + 1, u, u + 1}
      (ordinaryTensorRingMap l E f)

@[irreducible] private def ordinaryTensorAdjunction :
    ordinaryTensorPull l E f ⊣
      SheafOfModules.ScalarReductionProof.restriction.{u + 1, u, u + 1}
        (ordinaryTensorRingMap l E f) ⋙
        AlgebraicGeometry.Scheme.T f (completedIntegralCommRingSheafUnrestricted l E Y) :=
  (AlgebraicGeometry.Scheme.canonicalAdjunction f
    (completedIntegralCommRingSheafUnrestricted l E Y)).comp
      (SheafOfModules.ScalarReductionProof.tensorAdjunction.{u + 1, u, u + 1}
        (ordinaryTensorRingMap l E f))

@[irreducible] private def ordinaryTensorPushIso :
    SheafOfModules.ScalarReductionProof.restriction.{u + 1, u, u + 1}
        (ordinaryTensorRingMap l E f) ⋙
        AlgebraicGeometry.Scheme.T f (completedIntegralCommRingSheafUnrestricted l E Y) ≅
      IntegralAmbient.push l E f := by
  let R := completedIntegralCommRingSheafUnrestricted l E Y
  let S := completedIntegralCommRingSheafUnrestricted l E X
  let η := (proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R
  let c := ordinaryTensorRingMap l E f
  let F := sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let G := sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let η' := F.map η
  let c' := G.map c
  have h : η' ≫ (proEtaleSheafDirectImage f RingCat.{u + 1}).map c' =
      F.map (IntegralAmbient.coefficientMap l E f) := by
    have ht := (proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _ |>.apply_symm_apply
      (IntegralAmbient.coefficientMap l E f)
    exact congrArg F.map ht
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
    apply PresheafOfModules.isoMk
      (fun V ↦ (ModuleCat.restrictScalarsCongr
        (congrArg (fun q ↦ (q.hom.app V).hom) h)).app (M.val.obj
          (op ((proEtaleBaseChange f).obj V.unop))))
      (by
        intro V W i
        ext x
        rfl)
  · intro M N a
    ext V x
    rfl

private instance ordinaryTensorPull_additive : (ordinaryTensorPull l E f).Additive := by
  have : (SheafOfModules.ScalarReductionProof.restriction.{u + 1, u, u + 1}
        (ordinaryTensorRingMap l E f) ⋙
      AlgebraicGeometry.Scheme.T f
        (completedIntegralCommRingSheafUnrestricted l E Y)).Additive := by
    constructor
    intro M N a b
    rfl
  exact (ordinaryTensorAdjunction l E f).left_adjoint_additive

@[irreducible] private def ordinaryTensorPullIso :
    ordinaryTensorPull l E f ≅ ordinaryIntegralModulePull l E f :=
  Adjunction.leftAdjointUniq
    ((ordinaryTensorAdjunction l E f).ofNatIsoRight
      (ordinaryTensorPushIso l E f ≪≫ ordinaryAmbientPushIso l E f))
    (ordinaryIntegralModuleAdjunction l E f)

@[irreducible] private def ordinaryTensorHomotopyIso :
    (ordinaryTensorPull l E f).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ≅
      (ordinaryIntegralModulePull l E f).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh := by
  let e := ordinaryTensorPullIso l E f
  have : IsIso (e.hom.mapHomotopyCategory (.up ℤ)) :=
    ⟨e.inv.mapHomotopyCategory (.up ℤ),
      by rw [← NatTrans.mapHomotopyCategory_comp, e.hom_inv_id,
        NatTrans.mapHomotopyCategory_id],
      by rw [← NatTrans.mapHomotopyCategory_comp, e.inv_hom_id,
        NatTrans.mapHomotopyCategory_id]⟩
  exact Functor.isoWhiskerRight (asIso (e.hom.mapHomotopyCategory (.up ℤ))) DerivedCategory.Qh

private theorem ordinaryFunctorMap
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    (F G : A ⥤ B) (T : B ⥤ C) (h : F = G) {M N : A} (a : M ⟶ N) :
    (F ⋙ T).map a =
      eqToHom (congrArg T.obj (congrArg (fun H ↦ H.obj M) h)) ≫
        T.map (G.map a) ≫
        eqToHom (congrArg T.obj (congrArg (fun H ↦ H.obj N) h)).symm := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, Functor.comp_map]

private theorem ordinaryTensorDerivedData :
    ∃ (LF : DerivedCategory (integralTowerModules l E Y) ⥤
        DerivedCategory (integralTowerModules l E X))
      (ε : DerivedCategory.Qh ⋙ LF ⟶
        (ordinaryTensorPull l E f).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
      LF.IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso (integralTowerModules l E Y) (.up ℤ)) ∧
      ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
        IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P.obj)) := by
  let : EssentiallySmall.{u + 1} X.ProEt := integralOperationsSiteSmall.{u, u} X
  let : EssentiallySmall.{u + 1} Y.ProEt := integralOperationsSiteSmall.{u, u} Y
  have : PreservesFiniteLimits (proEtaleSheafInverseImage f (Type (u + 1))) :=
    (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage f (𝟙 Y)).2.2.2.1
  obtain ⟨I, hI⟩ := proEtaleAlgebraicInverseImage_exists f
    (completedIntegralCommRingSheafUnrestricted l E Y)
  obtain ⟨LF, ε, hLF, _, _, hε, _⟩ :=
    SheafOfModules.ringedTopoiDerivedPullbackIndependent
      (proEtaleSheafInverseImage f (Type (u + 1)))
      (proEtaleSheafDirectImage f (Type (u + 1)))
      (proEtaleSheafAdjunction f (Type (u + 1))) I (ordinaryTensorRingMap l E f)
      (ordinaryTensorPull l E f)
      (fun M ↦ congrArg
        (SheafOfModules.ScalarReductionProof.tensorFunctor.{u + 1, u, u + 1}
          (ordinaryTensorRingMap l E f)).obj
        (congrArg (fun T ↦ T.obj M) hI.symm))
      (fun {M N} a ↦ ordinaryFunctorMap _ _
        (SheafOfModules.ScalarReductionProof.tensorFunctor.{u + 1, u, u + 1}
          (ordinaryTensorRingMap l E f)) hI.symm a)
  exact ⟨LF, ε, hLF, fun P ↦ hε P.obj P.property.1 P.property.2⟩

/-- The canonical total left derived functor exists on the unbounded category.
Source: Stacks 06YY (blueprint: lem-tw-ordinary-completed-integral-pullback).
Proof: use lem-pc-kflat-resolution with independent site and coefficient sizes.
Exact inverse image followed by extension of scalars preserves quasi-isomorphisms
between flat-term K-flat complexes, by ringed-topoi-derived-pullback. Localization
of this resolving class gives the total left derived functor and its counit. -/
@[instance] theorem ordinaryIntegralPull_hasLeftDerived :
    ((ordinaryIntegralModulePull l E f).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (integralTowerModules l E Y) (.up ℤ)) := by
  obtain ⟨LF, ε, hLF, _⟩ := ordinaryTensorDerivedData l E f
  let := hLF
  have := @Functor.HasLeftDerivedFunctor.mk' _ _ _ _ _ _ _ _ _ _ _ _ hLF
  exact (Functor.hasLeftDerivedFunctor_iff_of_iso
    (ordinaryTensorHomotopyIso l E f)
    (HomotopyCategory.quasiIso (integralTowerModules l E Y) (.up ℤ))).mp inferInstance

/-- Ordinary unbounded derived ringed pullback, before completion.
Source: Stacks 06YY (blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralDerivedPull :=
  ((ordinaryIntegralModulePull l E f).mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh).totalLeftDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (integralTowerModules l E Y) (.up ℤ))

/-- The counit of the specified ordinary total derived pullback.
Source: Stacks 06YY (blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralPullCounit :
    DerivedCategory.Qh ⋙ ordinaryIntegralDerivedPull l E f ⟶
      (ordinaryIntegralModulePull l E f).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh :=
  ((ordinaryIntegralModulePull l E f).mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh).totalLeftDerivedCounit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (integralTowerModules l E Y) (.up ℤ))

/-- Termwise ordinary pullback on cochain representatives.
Source: Stacks 06YY (blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralPullComplex :=
  (ordinaryIntegralModulePull l E f).mapHomologicalComplex (.up ℤ)

/-- The ordinary computation map on a cochain representative, retaining its universal counit.
Source: Stacks 06YY (blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralPullComplexCounit (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    (ordinaryIntegralDerivedPull l E f).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((ordinaryIntegralPullComplex l E f).obj P) :=
  (ordinaryIntegralDerivedPull l E f).map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
    (ordinaryIntegralPullCounit l E f).app ((HomotopyCategory.quotient _ _).obj P) ≫
    DerivedCategory.Qh.map
      (((ordinaryIntegralModulePull l E f).mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app ((ordinaryIntegralPullComplex l E f).obj P)

/-- The ordinary computation map is invertible on every flat-term K-flat representative.
Source: Stacks 06YY (blueprint: lem-tw-ordinary-completed-integral-pullback).
Proof: the resolving-class derived-pullback theorem computes the total left derived
functor on precisely these complexes. Its counit is invertible there. The remaining
factors are the canonical cochain-to-homotopy localization isomorphisms. -/
theorem ordinaryIntegralPullComplexCounit_isIso
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    IsIso (ordinaryIntegralPullComplexCounit l E f P.obj) := by
  obtain ⟨LF, ε, hLF, hε⟩ := ordinaryTensorDerivedData l E f
  let := hLF
  let W := HomotopyCategory.quasiIso (integralTowerModules l E Y) (.up ℤ)
  have : (ordinaryIntegralDerivedPull l E f).IsLeftDerivedFunctor
      (ordinaryIntegralPullCounit l E f) W := by
    dsimp only [ordinaryIntegralDerivedPull, ordinaryIntegralPullCounit, W]
    infer_instance
  let τ := ordinaryTensorHomotopyIso l E f
  let e : LF ≅ ordinaryIntegralDerivedPull l E f :=
    Functor.leftDerivedNatIso LF (ordinaryIntegralDerivedPull l E f)
      ε (ordinaryIntegralPullCounit l E f) W τ
  let H := (HomotopyCategory.quotient _ (.up ℤ)).obj P.obj
  have : IsIso (ε.app H) := hε P
  have he : e.hom.app (DerivedCategory.Qh.obj H) ≫
      (ordinaryIntegralPullCounit l E f).app H = ε.app H ≫ τ.hom.app H :=
    Functor.leftDerivedNatTrans_app LF (ordinaryIntegralDerivedPull l E f)
      ε (ordinaryIntegralPullCounit l E f) W τ.hom H
  have : IsIso (e.hom.app (DerivedCategory.Qh.obj H) ≫
      (ordinaryIntegralPullCounit l E f).app H) := by
    rw [he]
    infer_instance
  have : IsIso ((ordinaryIntegralPullCounit l E f).app H) :=
    IsIso.of_isIso_comp_left (e.hom.app (DerivedCategory.Qh.obj H)) _
  dsimp only [ordinaryIntegralPullComplexCounit]
  infer_instance

attribute [local irreducible] ordinaryIntegralDerivedPull ordinaryIntegralPullCounit
  ordinaryTensorPull ordinaryTensorRingMap ordinaryIntegralPullComplexCounit

private def ordinaryAmbientPullIso :
    ordinaryIntegralModulePull l E f ≅ IntegralAmbient.pull l E f :=
  Adjunction.leftAdjointUniq (ordinaryIntegralModuleAdjunction l E f)
    ((IntegralAmbient.adjunction l E f).ofNatIsoRight (ordinaryAmbientPushIso l E f))

private theorem ordinaryAmbientPullIso_unit
    (M : integralTowerModules l E Y) (V : Y.ProEt) (x : M.val.obj (op V)) :
    ((ordinaryAmbientPullIso l E f).hom.app M).val.app
        (op ((proEtaleBaseChange f).obj V))
      (((ordinaryIntegralModuleAdjunction l E f).unit.app M).val.app (op V) x) =
      IntegralAmbient.pullSection l E f M V x := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (ordinaryIntegralModuleAdjunction l E f)
    ((IntegralAmbient.adjunction l E f).ofNatIsoRight (ordinaryAmbientPushIso l E f)) M
  have hh := congrArg (fun a ↦ a.val.app (op V) x) h
  exact hh

private def ordinaryAmbientComplexIso :
    ordinaryIntegralPullComplex l E f ≅ IntegralAmbient.pullComplex l E f := by
  let := IntegralAmbient.pull_additive l E f
  exact NatIso.mapHomologicalComplex (ordinaryAmbientPullIso l E f) (.up ℤ)

private def ordinaryAugmentation :
    ordinaryIntegralPullComplex l E f ⋙
        (Functor.const ℕᵒᵖ : CochainComplex (integralTowerModules l E X) ℤ ⥤ _) ⟶
      integralOperationsPullbackTowerFunctor l E f :=
  Functor.whiskerRight (ordinaryAmbientComplexIso l E f).hom (Functor.const ℕᵒᵖ) ≫
    Functor.whiskerLeft (IntegralAmbient.pullComplex l E f)
      (IntegralOnSlice.augmentation l E X none) ≫
    (IntegralAmbient.pullTowerIso l E f).hom

private theorem ordinaryAugmentation_formula
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) (i : ℤ)
    (V : Y.ProEt) (x : (P.X i).val.obj (op V)) :
    ((((ordinaryAugmentation l E f).app P).app (op n)).f i).val.app
        (op ((proEtaleBaseChange f).obj V))
      (((ordinaryIntegralModuleAdjunction l E f).unit.app (P.X i)).val.app (op V) x) =
      integralOperationsPullbackGenerator l E f n
        (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V
        (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) 1 x) := by
  have ha := (IntegralOnSlice.augmentation_existsUnique l E X none).exists.choose_spec
    ((IntegralAmbient.pullComplex l E f).obj P) n i
    (op ((proEtaleBaseChange f).obj V))
    (IntegralAmbient.pullSection l E f (P.X i) V x)
  have hb := (IntegralAmbient.pullTowerModel l E f).exists.choose_spec P n i V 1 x
  change (((((IntegralAmbient.pullTowerIso l E f).hom.app P).app (op n)).f i).val.app
    (op ((proEtaleBaseChange f).obj V))
      (((((IntegralOnSlice.augmentation l E X none).app
        ((IntegralAmbient.pullComplex l E f).obj P)).app (op n)).f i).val.app
        (op ((proEtaleBaseChange f).obj V))
          (((ordinaryAmbientPullIso l E f).hom.app (P.X i)).val.app
            (op ((proEtaleBaseChange f).obj V))
            (((ordinaryIntegralModuleAdjunction l E f).unit.app (P.X i)).val.app
              (op V) x)))) = _
  rw [ordinaryAmbientPullIso_unit]
  have ha' :
      (((((IntegralOnSlice.augmentation l E X none).app
        ((IntegralAmbient.pullComplex l E f).obj P)).app (op n)).f i).val.app
          (op ((proEtaleBaseChange f).obj V)))
        (IntegralAmbient.pullSection l E f (P.X i) V x) =
      IntegralOnSlice.generator l E X none n ((IntegralAmbient.pull l E f).obj (P.X i))
        (op ((proEtaleBaseChange f).obj V)) 1
        (IntegralAmbient.pullSection l E f (P.X i) V x) := ha
  exact (congrArg (((((IntegralAmbient.pullTowerIso l E f).hom.app P).app
    (op n)).f i).val.app (op ((proEtaleBaseChange f).obj V))) ha').trans
    (by
      change _ = IntegralAmbient.finitePullSection l E f n P i V 1 x
        at hb
      have hc : IntegralAmbient.finitePullSection l E f n P i V 1 x =
          integralOperationsPullbackGenerator l E f n
            (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V
            (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) 1 x) := by
        dsimp only [IntegralAmbient.finitePullSection]
        exact one_smul _ _
      exact hb.trans hc)

attribute [local irreducible] ordinaryAmbientComplexIso ordinaryAmbientPullIso
  ordinaryAugmentation

/-- The quotient maps, as one natural map of strict towers, are uniquely fixed on generators.
The formula is 1 tensor q ↦ 1 tensor (q tensor 1); completed linearity gives
b tensor q ↦ 1 tensor (q tensor pi_n(b)) on every inverse-image generator.
Source: Bhatt--Scholze, Lemma 6.5.9; Stacks 06YY, 08TC
(blueprint: lem-tw-ordinary-completed-integral-pullback).
Proof: the completed coefficient map commutes with each quotient by its defining
projection equation. Thus the displayed map is balanced, linear and restriction
compatible. Sheafification gives the module maps; applying them degreewise gives
chain maps. Coefficient reduction preserves one, so consecutive transition squares
commute. The same generator equality proves naturality. Locally the scalar multiples
of restrictions of adjunction-unit generators generate pullback, giving uniqueness. -/
theorem ordinaryIntegralQuotientAugmentation_existsUnique :
    ∃! a : ordinaryIntegralPullComplex l E f ⋙
        (Functor.const ℕᵒᵖ : CochainComplex (integralTowerModules l E X) ℤ ⥤ _) ⟶
      integralOperationsPullbackTowerFunctor l E f,
      ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) (i : ℤ)
        (V : Y.ProEt) (x : (P.X i).val.obj (op V)),
        (((a.app P).app (op n)).f i).val.app (op ((proEtaleBaseChange f).obj V))
          (((ordinaryIntegralModuleAdjunction l E f).unit.app (P.X i)).val.app (op V) x) =
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
  apply ((ordinaryIntegralModuleAdjunction l E f).homEquiv _ _).injective
  ext V x
  change (((a.app P).app n).f i).val.app
      (op ((proEtaleBaseChange f).obj V.unop))
      (((ordinaryIntegralModuleAdjunction l E f).unit.app (P.X i)).val.app V x) = _
  exact (ha P n.unop i V.unop x).trans
    (ordinaryAugmentation_formula l E f P n.unop i V.unop x).symm

/-- The actual quotient augmentation, with all quotient transitions retained.
Source: Bhatt--Scholze, Lemma 6.5.9; Stacks 08TC
(blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralQuotientAugmentation :=
  (ordinaryIntegralQuotientAugmentation_existsUnique l E f).exists.choose

attribute [local irreducible] ordinaryIntegralQuotientAugmentation

/-- The product of the specified quotient maps.
Source: Stacks 08TC (blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralProductAugmentation
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    (ordinaryIntegralPullComplex l E f).obj P ⟶
      ∏ᶜ (fun n : ℕ ↦ ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n)) :=
  Pi.lift (fun n ↦ ((ordinaryIntegralQuotientAugmentation l E f).app P).app (op n))

private theorem ordinaryTowerAugmentation_zero
    (M : Type*) [Category* M] [Abelian M] [HasCountableProducts M]
    (S : ℕᵒᵖ ⥤ CochainComplex M ℤ) (C : CochainComplex M ℤ)
    (a : (Functor.const ℕᵒᵖ).obj C ⟶ S) :
    Pi.lift (fun n : ℕ ↦ a.app (op n)) ≫
      towerTransitionEndomorphism (K := fun n : ℕ ↦ S.obj (op n))
        (integralOperationsTowerStep S) = 0 := by
  apply Pi.hom_ext
  intro n
  have h := a.naturality (homOfLE (Nat.le_succ n)).op
  simpa [towerTransitionEndomorphism, towerProductShift,
    integralOperationsTowerStep, Category.assoc] using sub_eq_zero.mpr h

/-- The strict quotient augmentation is killed by 1-s, with zero second cone cochain.
Source: Stacks 08TC (blueprint: lem-tw-ordinary-completed-integral-pullback).
Proof: after every product projection, the composite with 1-s is the difference
between consecutive quotient maps and is zero by the strict tower's naturality.
The differential of the zero cochain is zero. Product projections are jointly monic. -/
theorem ordinaryIntegralCompletionChain_condition
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    CochainComplex.HomComplex.δ (-1) 0
      (0 : CochainComplex.HomComplex.Cochain ((ordinaryIntegralPullComplex l E f).obj P)
        (∏ᶜ fun n : ℕ ↦
          ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (ordinaryIntegralProductAugmentation l E f P ≫
          towerTransitionEndomorphism
            (K := fun n : ℕ ↦
              ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n))
            (integralOperationsTowerStep
              ((integralOperationsPullbackTowerFunctor l E f).obj P))) = 0 := by
  have hzero : ordinaryIntegralProductAugmentation l E f P ≫
      towerTransitionEndomorphism
        (K := fun n : ℕ ↦
          ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n))
        (integralOperationsTowerStep
          ((integralOperationsPullbackTowerFunctor l E f).obj P)) = 0 := by
    exact ordinaryTowerAugmentation_zero (integralTowerModules l E X)
      ((integralOperationsPullbackTowerFunctor l E f).obj P)
      ((ordinaryIntegralPullComplex l E f).obj P)
      ((ordinaryIntegralQuotientAugmentation l E f).app P)
  simp only [CochainComplex.HomComplex.δ_zero, zero_add, hzero,
    CochainComplex.HomComplex.Cochain.ofHom_zero]

/-- The prescribed chain map into Cone(1-s)[-1]: quotient maps and zero, respectively.
Source: Stacks 08TC (blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralCompletionChain
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    (ordinaryIntegralPullComplex l E f).obj P ⟶
      (integralOperationsPullbackComplexFunctor l E f).obj P :=
  CochainComplex.mappingCocone.lift
    (towerTransitionEndomorphism
      (K := fun n : ℕ ↦ ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n))
      (integralOperationsTowerStep ((integralOperationsPullbackTowerFunctor l E f).obj P)))
    (ordinaryIntegralProductAugmentation l E f P) 0
    (ordinaryIntegralCompletionChain_condition l E f P)

attribute [local irreducible] towerTransitionEndomorphism

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem ordinaryRoosLift_natural (M : Type*) [Category* M] [Abelian M]
    [HasCountableProducts M] {C D : CochainComplex M ℤ}
    {S T : ℕᵒᵖ ⥤ CochainComplex M ℤ} (a : S ⟶ T) (α : C ⟶ D)
    (u : C ⟶ ∏ᶜ fun n : ℕ ↦ S.obj (op n))
    (v : D ⟶ ∏ᶜ fun n : ℕ ↦ T.obj (op n))
    (hu : u ≫ towerTransitionEndomorphism (K := fun n : ℕ ↦ S.obj (op n))
        (integralOperationsTowerStep S) = 0)
    (hv : v ≫ towerTransitionEndomorphism (K := fun n : ℕ ↦ T.obj (op n))
        (integralOperationsTowerStep T) = 0)
    (hn : α ≫ v = u ≫ Limits.Pi.map (f := fun n : ℕ ↦ S.obj (op n))
      (g := fun n : ℕ ↦ T.obj (op n)) (fun n ↦ a.app (op n))) :
    α ≫ CochainComplex.mappingCocone.lift
        (towerTransitionEndomorphism (K := fun n : ℕ ↦ T.obj (op n))
        (integralOperationsTowerStep T)) v 0 (by simp [hv]) =
      CochainComplex.mappingCocone.lift
        (towerTransitionEndomorphism (K := fun n : ℕ ↦ S.obj (op n))
        (integralOperationsTowerStep S)) u 0 (by simp [hu]) ≫
          integralOperationsRoosMap a := by
  unfold integralOperationsRoosMap
  rw [arrowConeMap]
  exact completedCoconeLift_natural M _ _ _ _ (integralOperationsRoos_square a)
    α u v hu hv hn

private theorem ordinaryIntegralCompletionChain_natural
    {P Q : CochainComplex (integralTowerModules l E Y) ℤ} (a : P ⟶ Q) :
    (ordinaryIntegralPullComplex l E f).map a ≫ ordinaryIntegralCompletionChain l E f Q =
      ordinaryIntegralCompletionChain l E f P ≫
        (integralOperationsPullbackComplexFunctor l E f).map a := by
  have hn : (ordinaryIntegralPullComplex l E f).map a ≫
      ordinaryIntegralProductAugmentation l E f Q =
    ordinaryIntegralProductAugmentation l E f P ≫
      Limits.Pi.map
        (f := fun n : ℕ ↦
          ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n))
        (g := fun n : ℕ ↦
          ((integralOperationsPullbackTowerFunctor l E f).obj Q).obj (op n))
        (fun n ↦ ((integralOperationsPullbackTowerFunctor l E f).map a).app (op n)) := by
    apply Pi.hom_ext
    intro n
    have h := congrArg (fun k ↦ k.app (op n))
      ((ordinaryIntegralQuotientAugmentation l E f).naturality a)
    simpa [ordinaryIntegralProductAugmentation, Category.assoc] using h
  have hz (P : CochainComplex (integralTowerModules l E Y) ℤ) :
      ordinaryIntegralProductAugmentation l E f P ≫
        towerTransitionEndomorphism
          (K := fun n : ℕ ↦
            ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n))
          (integralOperationsTowerStep
            ((integralOperationsPullbackTowerFunctor l E f).obj P)) = 0 := by
    apply CochainComplex.HomComplex.Cochain.ofHom_injective
    simpa only [CochainComplex.HomComplex.δ_zero, zero_add,
      CochainComplex.HomComplex.Cochain.ofHom_zero] using
      ordinaryIntegralCompletionChain_condition l E f P
  exact ordinaryRoosLift_natural (integralTowerModules l E X)
    (S := (integralOperationsPullbackTowerFunctor l E f).obj P)
    (T := (integralOperationsPullbackTowerFunctor l E f).obj Q)
    ((integralOperationsPullbackTowerFunctor l E f).map a)
    ((ordinaryIntegralPullComplex l E f).map a)
    (ordinaryIntegralProductAugmentation l E f P)
    (ordinaryIntegralProductAugmentation l E f Q) (hz P) (hz Q) hn

attribute [local irreducible] ordinaryIntegralCompletionChain
  integralOperationsPullbackComplexFunctor integralDerivedPullback integralDerivedPullbackComparison

private theorem ordinaryNormalizedComparison_existsUnique
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    (p : A ⥤ B) (ff : ((Functor.whiskeringLeft A B C).obj p).FullyFaithful)
    (O F : B ⥤ C) (G : A ⥤ C) (e : p ⋙ F ≅ G) (β : p ⋙ O ⟶ G) :
    ∃! η : O ⟶ F, ∀ P, η.app (p.obj P) ≫ e.hom.app P = β.app P := by
  let α := β ≫ e.inv
  let η := ff.preimage α
  have hη : Functor.whiskerLeft p η = α := ff.map_preimage α
  refine ⟨η, ?_, ?_⟩
  · intro P
    have h := NatTrans.congr_app hη P
    change η.app (p.obj P) = β.app P ≫ e.inv.app P at h
    rw [h, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  · intro η' hη'
    apply ff.map_injective
    ext P
    apply (cancel_mono (e.hom.app P)).1
    have h := NatTrans.congr_app hη P
    change η.app (p.obj P) = β.app P ≫ e.inv.app P at h
    change η'.app (p.obj P) ≫ e.hom.app P = η.app (p.obj P) ≫ e.hom.app P
    rw [hη', h, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

private def ordinaryIntegralComplexCounitNat :
    DerivedCategory.Q ⋙ ordinaryIntegralDerivedPull l E f ⟶
      ordinaryIntegralPullComplex l E f ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv
      (ordinaryIntegralDerivedPull l E f) ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ _)
      (ordinaryIntegralPullCounit l E f) ≫
    Functor.whiskerRight
      ((ordinaryIntegralModulePull l E f).mapHomotopyCategoryFactors (.up ℤ)).hom
      DerivedCategory.Qh ≫
    Functor.whiskerLeft (ordinaryIntegralPullComplex l E f)
      (DerivedCategory.quotientCompQhIso _).hom

private theorem ordinaryIntegralComplexCounitNat_app
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    (ordinaryIntegralComplexCounitNat l E f).app P =
      ordinaryIntegralPullComplexCounit l E f P := by
  unfold ordinaryIntegralComplexCounitNat ordinaryIntegralPullComplexCounit
  rfl

attribute [local irreducible] ordinaryIntegralComplexCounitNat

attribute [local irreducible] integralOperationsPullbackTowerFunctor

private def ordinaryIntegralCompletionNat :
    ordinaryIntegralPullComplex l E f ⟶ integralOperationsPullbackComplexFunctor l E f where
  app P := ordinaryIntegralCompletionChain l E f P
  naturality _ _ a := ordinaryIntegralCompletionChain_natural l E f a

private theorem ordinaryIntegralCompletionNat_app
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    (ordinaryIntegralCompletionNat l E f).app P =
      ordinaryIntegralCompletionChain l E f P := rfl

attribute [local irreducible] ordinaryIntegralCompletionNat

private def ordinaryIntegralComparisonOnGood :
    { β : integralOperationsGoodLocalization l E Y ⋙ ordinaryIntegralDerivedPull l E f ⟶
        integralOperationsPullbackOnGood l E f //
      ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
        β.app P = ordinaryIntegralPullComplexCounit l E f P.obj ≫
          DerivedCategory.Q.map (ordinaryIntegralCompletionChain l E f P.obj) } := by
  let c := ordinaryIntegralComplexCounitNat l E f
  refine ⟨Functor.whiskerLeft (integralOperationsGoodComplex l E Y).ι
    (c ≫ Functor.whiskerRight (ordinaryIntegralCompletionNat l E f) DerivedCategory.Q), ?_⟩
  intro P
  change c.app P.obj ≫ DerivedCategory.Q.map ((ordinaryIntegralCompletionNat l E f).app P.obj) =
    ordinaryIntegralPullComplexCounit l E f P.obj ≫ _
  rw [ordinaryIntegralComplexCounitNat_app, ordinaryIntegralCompletionNat_app]

attribute [local irreducible] ordinaryIntegralComparisonOnGood ordinaryIntegralPullComplex

/-- The specified chain maps descend to a unique natural transformation.
Source: Stacks 06YY, 08TC (blueprint: lem-tw-ordinary-completed-integral-pullback).
Proof: the augmentation is natural on chain maps. Its strict cone map has a zero
second coordinate, so its naturality holds as chain maps, not just on projections.
Both representative constructions invert quasi-isomorphisms on the flat-term
K-flat class by ringed-topoi-derived-pullback and integral-operations-well-defined.
The resolving-class localization therefore descends the comparison. Its restriction
on that class is faithful, proving uniqueness and independence of the resolution. -/
theorem ordinaryIntegralCompletionComparison_existsUnique :
    ∃! η : ordinaryIntegralDerivedPull l E f ⟶ integralDerivedPullback l E f,
      ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
        η.app (DerivedCategory.Q.obj P.obj) ≫
            (integralDerivedPullbackComparison l E f).hom.app P =
          ordinaryIntegralPullComplexCounit l E f P.obj ≫
            DerivedCategory.Q.map (ordinaryIntegralCompletionChain l E f P.obj) := by
  let L := integralOperationsGoodLocalization l E Y
  let O := ordinaryIntegralDerivedPull l E f
  let F := integralDerivedPullback l E f
  let e := integralDerivedPullbackComparison l E f
  let β := (ordinaryIntegralComparisonOnGood l E f).val
  let ff := Classical.choice (good_whisker_fullyFaithful l E Y
    (DerivedCategory (integralTowerModules l E X)))
  have h := ordinaryNormalizedComparison_existsUnique L ff O F _ e β
  change ∃! η : ordinaryIntegralDerivedPull l E f ⟶ integralDerivedPullback l E f,
    ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
      η.app (DerivedCategory.Q.obj P.obj) ≫
        (integralDerivedPullbackComparison l E f).hom.app P =
          (ordinaryIntegralComparisonOnGood l E f).val.app P at h
  obtain ⟨η, hη, hη_unique⟩ := h
  refine ⟨η, ?_, ?_⟩
  · intro P
    exact (hη P).trans ((ordinaryIntegralComparisonOnGood l E f).property P)
  · intro η' hη'
    apply hη_unique η'
    intro P
    exact (hη' P).trans ((ordinaryIntegralComparisonOnGood l E f).property P).symm

/-- The canonical completion comparison, uniquely fixed by the (quotients,0) chain map.
Source: Bhatt--Scholze, Lemma 6.5.9; Stacks 08TC
(blueprint: lem-tw-ordinary-completed-integral-pullback). -/
def ordinaryIntegralCompletionComparison :
    ordinaryIntegralDerivedPull l E f ⟶ integralDerivedPullback l E f :=
  (ordinaryIntegralCompletionComparison_existsUnique l E f).exists.choose

attribute [local irreducible] ordinaryIntegralCompletionComparison

end WeilConjectures
