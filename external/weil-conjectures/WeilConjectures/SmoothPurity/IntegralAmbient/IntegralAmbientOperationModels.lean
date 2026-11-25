/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
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
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
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
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.SmoothPurity.IntegralAmbient.NormalizedIntegralPullbackTower
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement
import WeilConjectures.Algebra.Homology.RingedPresentationOnSites.RingedPullbackPresentationOnSitesSupplement
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import WeilConjectures.Algebra.Homology.Ringed.RingedPullbackCochainPresentation
import WeilConjectures.SmoothPurity.Normalized.NormalizedIntegralTensorTower
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import all WeilConjectures.SmoothPurity.Integral.IntegralTensorTransitionCompatibility

/-! # Ambient completion presentations of integral operations

Source: Stacks Project, sites-cohomology.tex, Tags 06YY, 0G7E, 07A4 and 0941;
sites-modules.tex, Tags 03D7 and 03EL
(blueprint: lem-pur-integral-ambient-operation-models).

All towers and finite operations below are the recorded constructions. The completed
coefficient map is specified by its projections, not by an identification of rings.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.all false

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a₁ b₁ c₁ d₁
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures.IntegralAmbient
open AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [-instance] SheafOfModules.cochainModulesMonoidal
  SheafOfModules.cochainModulesSymmetric SheafOfModules.cochainModulesPreadditive
  SheafOfModules.cochainTensorLocalizationIsMonoidal
  SheafOfModules.cochainTensorLeftPreservesColimits
  SheafOfModules.cochainTensorRightPreservesColimits
attribute [local instance 2000] integralOperationsFiniteHasMap

attribute [local irreducible] constantSheaf

attribute [local irreducible] HasDerivedCategory.standard

/-- The source tensor tower uses the direct-sum total tensor complex.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
def tensorTower (W : Scheme.{t}) :
    (CochainComplex (integralTowerModules l E W) ℤ ×
      CochainComplex (integralTowerModules l E W) ℤ) ⥤
        (ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E W) ℤ) :=
  coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W) ⋙ IntegralOnSlice.tower l E W none

set_option maxHeartbeats 60000

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local irreducible] coefficientTotalTensor SheafOfModules.monoidalCategory
  completedIntegralCoefficientSheafUnrestricted unrestrictedIntegralReductionExistence
  SheafOfModules.changeOfRings PresheafOfModules.sheafification

private theorem tensorLevel_hom_ext (W : Scheme.{t})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) (k : ℤ)
    (H : integralTowerModules l E W)
    {f g : (((tensorTower l E W).obj (P, Q)).obj (op n)).X k ⟶ H}
    (h : ∀ (p q : ℤ) (hpq : p + q = k) (V : W.ProEtᵒᵖ)
      (s : (integralCoefficientCommRingSheaf l E W n).obj.obj V)
      (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
      f.val.app V (IntegralOnSlice.generator l E W none n _ V s
        (coefficientTensorGenerator.{u, t + 1, t} (ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) P Q p q k hpq V x y)) =
      g.val.app V (IntegralOnSlice.generator l E W none n _ V s
        (coefficientTensorGenerator.{u, t + 1, t} (ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) P Q p q k hpq V x y))) :
    f = g := by
  let : EssentiallySmall.{max u (t + 1)} W.ProEt := essentiallySmallSelf _
  dsimp only [tensorTower, Functor.comp_obj, IntegralOnSlice.tower,
    Functor.flip_obj_obj, Functor.ofOpSequence_obj] at f g ⊢
  let F := IntegralOnSlice.reduction l E W none n
  let hF := IntegralOnSlice.reduction_obj l E W none n
  let hmF {M N : integralTowerModules l E W} (f : M ⟶ N) :
      F.map f = eqToHom (hF M) ≫
        SheafOfModules.changeOfRingsHom
          (IntegralOnSlice.projection l E W none n) M f ≫
          eqToHom (hF N).symm :=
    IntegralOnSlice.unrestrictedReduction_map l E W none n f
  letI := extension_preserves_small_colimits.{t + 1, t, u}
    (IntegralOnSlice.projection l E W none n) F hF hmF
  apply total_extension_hom_ext.{t + 1, t, u}
    (IntegralOnSlice.projection l E W none n) F hF hmF P Q k H
  intro p q hpq V s x y
  convert h p q hpq V s x y using 1 <;> rfl

/-- The normalized balanced-tensor isomorphism of whole strict tensor towers.
Source: Stacks 03EL, 07A4 (blueprint: lem-pur-integral-ambient-operation-models).
Proof: in bidegree (p,q) send (x tensor y) tensor a to
(x tensor a) tensor (y tensor 1); the inverse multiplies the two coefficients.
The tensor universal property and direct sums extend these inverse maps. Both
sides have differential dx tensor y + (-1)^p x tensor dy, with unchanged a.
The formulas commute with all quotient transitions and with both input chain maps. -/
theorem tensorTowerModel (W : Scheme.{t}) :
    ∃! d : tensorTower l E W ≅ integralOperationsTensorTowerFunctor l E W,
      ∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) (p q : ℤ)
        (V : W.ProEtᵒᵖ) (a : (integralCoefficientCommRingSheaf l E W n).obj.obj V)
        (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
        (((d.hom.app (P, Q)).app (op n)).f (p + q)).val.app V
          (IntegralOnSlice.generator l E W none n _ V a
            (coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
              (completedIntegralCommRingSheafUnrestricted l E W) P Q p q (p + q) rfl V x y)) =
          integralOperationsTotalTensorSection l E W n P Q p q V
            (unrestrictedIntegralTensorSection l E W n (P.X p) V a x)
            (unrestrictedIntegralTensorSection l E W n (Q.X q) V 1 y) := by
  classical
  obtain ⟨d, hd⟩ := normalizedIntegralTensorTower l E W
  refine ⟨d, hd, ?_⟩
  intro d' hd'
  apply Iso.ext
  apply NatTrans.ext
  funext Z
  apply NatTrans.ext
  funext n
  apply HomologicalComplex.hom_ext
  intro k
  apply tensorLevel_hom_ext l E W Z.1 Z.2 n.unop k
  intro p q hpq V s x y
  subst k
  exact (hd' Z.1 Z.2 n.unop p q V s x y).trans
    (hd Z.1 Z.2 n.unop p q V s x y).symm

/-- The uniquely normalized strict pullback comparison.
Source: Stacks 03EL, 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
def pullTowerIso {X Y : Scheme.{t}} (f : X ⟶ Y) :
    pullTower l E f ≅ integralOperationsPullbackTowerFunctor l E f :=
  (pullTowerModel l E f).exists.choose

/-- The uniquely normalized strict tensor comparison.
Source: Stacks 03EL, 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
def tensorTowerIso (W : Scheme.{t}) :
    tensorTower l E W ≅ integralOperationsTensorTowerFunctor l E W :=
  (tensorTowerModel l E W).exists.choose

/-- The operation augmentation, with finite components given by scalar insertion.
The preceding normalization gives (r tensor x) ↦ pi_n(r) tensor (x tensor 1).
Source: Stacks 03EL, 0941 (blueprint: lem-pur-integral-ambient-operation-models). -/
def pullOperationUnit {X Y : Scheme.{t}} (f : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    (pullComplex l E f).obj P ⟶
      integralOperationsRoos ((integralOperationsPullbackTowerFunctor l E f).obj P) :=
  IntegralOnSlice.roosUnit l E X none ((pullComplex l E f).obj P) ≫
    integralOperationsRoosFunctor.map ((pullTowerIso l E f).hom.app P)

/-- The tensor operation augmentation, with finite components
x tensor y ↦ (x tensor 1) tensor (y tensor 1).
Source: Stacks 03EL, 07A4, 0941 (blueprint: lem-pur-integral-ambient-operation-models). -/
def tensorOperationUnit (W : Scheme.{t})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    (coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q) ⟶
        integralOperationsRoos ((integralOperationsTensorTowerFunctor l E W).obj (P, Q)) :=
  IntegralOnSlice.roosUnit l E W none _ ≫
    integralOperationsRoosFunctor.map ((tensorTowerIso l E W).hom.app (P, Q))

attribute [local irreducible] coefficientMap push pull pullTowerIso tensorTowerIso
  IntegralOnSlice.duality IntegralOnSlice.completion IntegralOnSlice.completionComparison
  IntegralOnSlice.completionUnit IntegralOnSlice.roosUnit

open CochainComplex CochainComplex.HomComplex in
private theorem roosMap_coordinates
    {A : Type*} [Category* A] [Abelian A] [HasCountableProducts A]
    {C C' : ℕᵒᵖ ⥤ CochainComplex A ℤ} (a : C ⟶ C') :
    integralOperationsRoosMap a ≫ mappingCocone.fst
        (towerTransitionEndomorphism (K := fun n ↦ C'.obj (op n))
        (integralOperationsTowerStep C')) =
      mappingCocone.fst (towerTransitionEndomorphism (K := fun n ↦ C.obj (op n))
        (integralOperationsTowerStep C)) ≫
        Limits.Pi.map (fun n : ℕ ↦ a.app (op n)) ∧
    ∀ (p q : ℤ) (h : p + -1 = q),
      (integralOperationsRoosMap a).f p ≫
          (mappingCocone.snd
            (towerTransitionEndomorphism (K := fun n ↦ C'.obj (op n))
        (integralOperationsTowerStep C'))).v p q h =
        (mappingCocone.snd
          (towerTransitionEndomorphism (K := fun n ↦ C.obj (op n))
        (integralOperationsTowerStep C))).v p q h ≫
            (Limits.Pi.map (fun n : ℕ ↦ a.app (op n))).f q := by
  unfold integralOperationsRoosMap
  rw [cofiberMap_eq_coneMap _ _ _ _ (integralOperationsRoos_square a)]
  let φ := towerTransitionEndomorphism (K := fun n ↦ C.obj (op n))
        (integralOperationsTowerStep C)
  let ψ := towerTransitionEndomorphism (K := fun n ↦ C'.obj (op n))
        (integralOperationsTowerStep C')
  let b := Limits.Pi.map (fun n : ℕ ↦ a.app (op n))
  let c := mappingCone.map φ ψ b b (integralOperationsRoos_square a)
  have hc₁ (p : ℤ) : c.f (p + -1) ≫
      (mappingCone.fst ψ).1.v (p + -1) p (by omega) =
      (mappingCone.fst φ).1.v (p + -1) p (by omega) ≫ b.f p := by
    simp [c, mappingCone.ext_from_iff φ p (p + -1) (by omega), mappingCone.map]
  have hc₂ (p : ℤ) : c.f (p + -1) ≫
      (mappingCone.snd ψ).v (p + -1) (p + -1) (add_zero _) =
      (mappingCone.snd φ).v (p + -1) (p + -1) (add_zero _) ≫ b.f (p + -1) := by
    simp [c, mappingCone.ext_from_iff φ p (p + -1) (by omega), mappingCone.map]
  constructor
  · apply HomologicalComplex.hom_ext
    intro p
    change ((CategoryTheory.shiftFunctor _ (-1 : ℤ)).map c).f p ≫ (mappingCocone.fst ψ).f p =
      (mappingCocone.fst φ).f p ≫ b.f p
    simp [mappingCocone.fst,
      Cochain.leftShift_v (mappingCone.fst ψ).1 (-1) 0 (by omega) p p
        (add_zero p) (p + -1) (by omega),
      Cochain.leftShift_v (mappingCone.fst φ).1 (-1) 0 (by omega) p p
        (add_zero p) (p + -1) (by omega)]
    exact hc₁ p
  · intro p q h
    obtain rfl : q = p + -1 := h.symm
    change ((CategoryTheory.shiftFunctor _ (-1 : ℤ)).map c).f p ≫
      (mappingCocone.snd ψ).v p (p + -1) h =
        (mappingCocone.snd φ).v p (p + -1) h ≫ b.f (p + -1)
    simp [mappingCocone.snd,
      Cochain.leftShift_v (mappingCone.snd ψ) (-1) (-1) (by omega)
        p (p + -1) rfl (p + -1) (by omega),
      Cochain.leftShift_v (mappingCone.snd φ) (-1) (-1) (by omega)
        p (p + -1) rfl (p + -1) (by omega),
      Int.negOnePow_even 2 ⟨1, rfl⟩]
    exact hc₂ p

private theorem roosUnit_fst (W : Scheme.{t})
    (P : IntegralOnSlice.Cx l E W none) :
    IntegralOnSlice.roosUnit l E W none P ≫ CochainComplex.mappingCocone.fst
      (towerTransitionEndomorphism
        (K := fun n ↦ ((IntegralOnSlice.tower l E W none).obj P).obj (op n))
        (integralOperationsTowerStep ((IntegralOnSlice.tower l E W none).obj P))) =
      IntegralOnSlice.productAugmentation l E W none P := by
  unfold IntegralOnSlice.roosUnit integralOperationsRoos
  exact CochainComplex.mappingCocone.lift_fst _ _ _ _

private theorem roosUnit_snd (W : Scheme.{t})
    (P : IntegralOnSlice.Cx l E W none)
    (p q : ℤ) (h : p + -1 = q) :
    (IntegralOnSlice.roosUnit l E W none P).f p ≫
      (CochainComplex.mappingCocone.snd (towerTransitionEndomorphism
        (K := fun n ↦ ((IntegralOnSlice.tower l E W none).obj P).obj (op n))
        (integralOperationsTowerStep ((IntegralOnSlice.tower l E W none).obj P)))).v p q h =
      0 := by
  unfold IntegralOnSlice.roosUnit integralOperationsRoos
  exact CochainComplex.mappingCocone.lift_f_snd_v _ _ _ _ p q h

private theorem roosMap_zero_snd
    {A : Type*} [Category* A] [Abelian A] [HasCountableProducts A]
    {C C' : ℕᵒᵖ ⥤ CochainComplex A ℤ} (a : C ⟶ C')
    {P : CochainComplex A ℤ} (c : P ⟶ integralOperationsRoos C)
    (p q : ℤ) (h : p + -1 = q)
    (hc : c.f p ≫ (CochainComplex.mappingCocone.snd
      (towerTransitionEndomorphism (K := fun n ↦ C.obj (op n))
        (integralOperationsTowerStep C))).v p q h = 0) :
    (c ≫ integralOperationsRoosMap a).f p ≫ (CochainComplex.mappingCocone.snd
      (towerTransitionEndomorphism (K := fun n ↦ C'.obj (op n))
        (integralOperationsTowerStep C'))).v p q h = 0 := by
  rw [HomologicalComplex.comp_f, Category.assoc, (roosMap_coordinates a).2 p q h,
    ← Category.assoc, hc, zero_comp]

private theorem roosUnit_map_snd (W : Scheme.{t})
    (P : IntegralOnSlice.Cx l E W none)
    {C : ℕᵒᵖ ⥤ IntegralOnSlice.Cx l E W none}
    (a : (IntegralOnSlice.tower l E W none).obj P ⟶ C)
    (p q : ℤ) (h : p + -1 = q) :
    (IntegralOnSlice.roosUnit l E W none P ≫ integralOperationsRoosMap a).f p ≫
      (CochainComplex.mappingCocone.snd
        (towerTransitionEndomorphism (K := fun n ↦ C.obj (op n))
          (integralOperationsTowerStep C))).v p q h = 0 := by
  exact roosMap_zero_snd a (IntegralOnSlice.roosUnit l E W none P) p q h
    (roosUnit_snd l E W P p q h)

private theorem ambientRoosUnit_coordinates (W : Scheme.{t})
    (P : CochainComplex (integralTowerModules l E W) ℤ)
    {C : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E W) ℤ}
    (a : (IntegralOnSlice.tower l E W none).obj P ⟶ C) :
    (IntegralOnSlice.roosUnit l E W none P ≫ integralOperationsRoosMap a) ≫
      CochainComplex.mappingCocone.fst
        (towerTransitionEndomorphism (K := fun n ↦ C.obj (op n))
          (integralOperationsTowerStep C)) =
      IntegralOnSlice.productAugmentation l E W none P ≫
        Limits.Pi.map (fun n : ℕ ↦ a.app (op n)) ∧
    ∀ (p q : ℤ) (h : p + -1 = q),
      (IntegralOnSlice.roosUnit l E W none P ≫ integralOperationsRoosMap a).f p ≫
        (CochainComplex.mappingCocone.snd
          (towerTransitionEndomorphism (K := fun n ↦ C.obj (op n))
            (integralOperationsTowerStep C))).v p q h = 0 := by
  constructor
  · rw [Category.assoc, (roosMap_coordinates a).1, ← Category.assoc, roosUnit_fst]
  · exact roosUnit_map_snd l E W P a

/-- The pullback tower comparison carries the quotient augmentation to the operation
augmentation, including its zero shifted-product coordinate.
Source: Stacks 03EL, 0941 (blueprint: lem-pur-integral-ambient-operation-models).
Proof: the nth quotient unit sends z to z tensor 1. The normalized scalar association
sends this to the defining finite pullback insertion. Strict tower maps induce the
same product map on both cone coordinates. They therefore preserve the zero second
cochain, while the unshifted coordinate is the product of the finite insertions. -/
theorem pullOperationUnit_coordinates {X Y : Scheme.{t}} (f : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    pullOperationUnit l E f P ≫ CochainComplex.mappingCocone.fst
      (C := integralTowerModules l E X)
      (towerTransitionEndomorphism
        (K := fun n : ℕ ↦ ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n))
        (integralOperationsTowerStep ((integralOperationsPullbackTowerFunctor l E f).obj P))) =
      IntegralOnSlice.productAugmentation l E X none ((pullComplex l E f).obj P) ≫
        Limits.Pi.map (fun n : ℕ ↦ ((pullTowerIso l E f).hom.app P).app (op n)) ∧
    ∀ (p q : ℤ) (h : p + (-1) = q),
      (pullOperationUnit l E f P).f p ≫
        (CochainComplex.mappingCocone.snd
          (C := integralTowerModules l E X) (towerTransitionEndomorphism
          (K := fun n : ℕ ↦ ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n))
          (integralOperationsTowerStep
            ((integralOperationsPullbackTowerFunctor l E f).obj P)))).v p q h = 0 := by
  simpa only [pullOperationUnit, integralOperationsRoosFunctor] using
    ambientRoosUnit_coordinates l E X ((pullComplex l E f).obj P)
      ((pullTowerIso l E f).hom.app P)

/-- The analogous tensor augmentation equation retains the zero shifted-product part.
Source: Stacks 03EL, 07A4, 0941 (blueprint: lem-pur-integral-ambient-operation-models).
Proof: x tensor y maps to (x tensor y) tensor 1, hence under the normalized comparison
to (x tensor 1) tensor (y tensor 1). The strict Roos map is diagonal on product
coordinates, so its shifted-product component remains zero in every degree. -/
theorem tensorOperationUnit_coordinates (W : Scheme.{t})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    tensorOperationUnit l E W P Q ≫ CochainComplex.mappingCocone.fst
      (C := integralTowerModules l E W)
      (towerTransitionEndomorphism
        (K := fun n : ℕ ↦ ((integralOperationsTensorTowerFunctor l E W).obj (P, Q)).obj (op n))
        (integralOperationsTowerStep ((integralOperationsTensorTowerFunctor l E W).obj (P, Q)))) =
      IntegralOnSlice.productAugmentation l E W none
        ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)) ≫
        Limits.Pi.map (fun n : ℕ ↦ ((tensorTowerIso l E W).hom.app (P, Q)).app (op n)) ∧
    ∀ (p q : ℤ) (h : p + (-1) = q),
      (tensorOperationUnit l E W P Q).f p ≫
        (CochainComplex.mappingCocone.snd
          (C := integralTowerModules l E W) (towerTransitionEndomorphism
          (K := fun n : ℕ ↦ ((integralOperationsTensorTowerFunctor l E W).obj (P, Q)).obj (op n))
          (integralOperationsTowerStep
            ((integralOperationsTensorTowerFunctor l E W).obj (P, Q))))).v p q h = 0 := by
  simpa only [tensorOperationUnit, integralOperationsRoosFunctor] using
    ambientRoosUnit_coordinates l E W
      ((coefficientTotalTensor.{u, t + 1, t} (ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q))
      ((tensorTowerIso l E W).hom.app (P, Q))

/-- Ordinary pullback carries flat-term K-flat representatives to such representatives.
Source: Stacks 0G7E (blueprint: lem-pur-integral-ambient-operation-models).
Proof: the module inverse image is the geometric inverse image followed by scalar
extension along coefficientMap. Apply ringed-topos K-flat pullback to this presentation;
flatness of its terms follows from the same ringed pullback theorem. -/
theorem pull_good {X Y : Scheme.{t}} (f : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (hP : integralOperationsGoodComplex l E Y P) :
    IntegralOnSlice.Good l E X none ((pullComplex l E f).obj P) := by
  letI : EssentiallySmall.{max u (t + 1)} Y.ProEt := essentiallySmallSelf _
  letI : EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf _
  letI : HasSheafify (ProEt.topology Y) (Type (max u (t + 1))) :=
    hasSheafifyEssentiallySmallSite _ _
  letI : HasSheafify (ProEt.topology X) (Type (max u (t + 1))) :=
    hasSheafifyEssentiallySmallSite _ _
  let G := Scheme.proEtaleBaseChange f
  let L := G.sheafPullback (Type (max u (t + 1))) (ProEt.topology Y) (ProEt.topology X)
  let a := G.sheafAdjunctionContinuous (Type (max u (t + 1)))
    (ProEt.topology Y) (ProEt.topology X)
  letI : ReflectsLimits (forget (Type (max u (t + 1)))) :=
    reflectsLimits_of_reflectsIsomorphisms
  letI : RepresentablyFlat G := flat_of_preservesFiniteLimits G
  letI : PreservesFiniteLimits (G.op.lan : (Y.ProEtᵒᵖ ⥤ Type (max u (t + 1))) ⥤
      X.ProEtᵒᵖ ⥤ Type (max u (t + 1))) :=
    by
      letI : AB5OfSize.{t, t + 1} (Type (max u (t + 1))) :=
        AB5OfSize_shrink.{t, t + 1, max u (t + 1), max u (t + 1)} _
      exact preservesFiniteLimits_op_lan_of_flat G
  letI : PreservesFiniteLimits L :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits G
      (Type (max u (t + 1))) (ProEt.topology Y) (ProEt.topology X)
  obtain ⟨RI, I, c, T, hT, hobj, hmap, ⟨am⟩⟩ :=
    SheafOfModules.RingedPresentationOnSites.continuous_ringed_pullback_presentation
      G L a (completedIntegralCommRingSheafUnrestricted l E X)
      (completedIntegralCommRingSheafUnrestricted l E Y) (coefficientMap l E f)
  letI := hT
  have am' : T ⊣ push l E f := by
    unfold push
    let q := ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat RingCat)).map
      (coefficientMap l E f))
    have hq : q = (⟨Functor.whiskerRight (coefficientMap l E f).hom
        (forget₂ CommRingCat RingCat)⟩) := rfl
    change T ⊣ SheafOfModules.pushforward q at am
    rw [hq] at am
    exact am
  let e : T ≅ pull l E f := am'.leftAdjointUniq (adjunction l E f)
  obtain ⟨hK, hflat⟩ := SheafOfModules.isKFlat_ringedToposPullback
    L _ a I c T hobj hmap P hP.1 hP.2
  let ec := (NatIso.mapHomologicalComplex e (.up ℤ)).app P
  exact ⟨SheafOfModules.kFlat_iso_independent
    (completedIntegralCommRingSheafUnrestricted l E X) ec hK,
    fun i ↦ SheafOfModules.flatOnSite_of_iso
      (completedIntegralCommRingSheafUnrestricted l E X)
      ((HomologicalComplex.eval _ _ i).mapIso ec) (hflat i)⟩

attribute [local semireducible] coefficientTotalTensor

/-- The direct-sum total tensor of two good representatives is good.
Source: Stacks 07A2, 07A4 (blueprint: lem-pur-integral-ambient-operation-models).
Proof: the total tensor of K-flat complexes is K-flat. Its terms are direct sums
of tensor products of flat module sheaves and are therefore flat. No boundedness
or product totalization is involved. -/
theorem tensor_good (W : Scheme.{t})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ)
    (hP : integralOperationsGoodComplex l E W P)
    (hQ : integralOperationsGoodComplex l E W Q) :
    IntegralOnSlice.Good l E W none
      ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)) := by
  let : EssentiallySmall.{max u (t + 1)} W.ProEt := essentiallySmallSelf _
  have h := SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
    (completedIntegralCommRingSheafUnrestricted l E W) P Q hP.1 hQ.1 hP.2 hQ.2
  exact ⟨h.1, h.2.1⟩

attribute [local irreducible] IntegralOnSlice.tower Functor.mapHomologicalComplex
  DerivedCategory.Q integralOperationsRoos integralOperationsRoosMap

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option maxHeartbeats 200000

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- Shared category and functor data of the recorded tensor comparison.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
structure AmbientTensorPresentation where
  Cx : Type a₁
  [cxCategory : Category.{b₁} Cx]
  D : Type c₁
  [dCategory : Category.{d₁} D]
  Flat : ObjectProperty Cx
  Good : ObjectProperty Cx
  good_flat : ∀ X, Good X → Flat X
  totalTensor : Cx × Cx ⥤ Cx
  Q : Cx ⥤ D
  tensor : D × D ⥤ D
  comparison : Flat.ι.prod Flat.ι ⋙ totalTensor ⋙ Q ≅
    (Flat.ι ⋙ Q).prod (Flat.ι ⋙ Q) ⋙ tensor
/-- Capture the categories, functors and comparison in one record.
Source: Stacks 06YY, 07A4, 08TC
(blueprint: lem-pur-integral-ambient-operation-models). -/
def AmbientTensorPresentation.ofComparison
    {C : Type a₁} [cc : Category.{b₁} C]
    {D : Type c₁} [dd : Category.{d₁} D]
    {K : ObjectProperty C}
    {T : C × C ⥤ C} {Q : C ⥤ D} {S : D × D ⥤ D}
    (cmp : K.ι.prod K.ι ⋙ T ⋙ Q ≅ (K.ι ⋙ Q).prod (K.ι ⋙ Q) ⋙ S)
    (G : ObjectProperty C) (hG : ∀ X, G X → K X) : AmbientTensorPresentation :=
  { Cx := C, cxCategory := cc, D := D, dCategory := dd,
    Flat := K, Good := G, good_flat := hG,
    totalTensor := T, Q := Q, tensor := S, comparison := cmp }
/-- Capture the actual data used by the existing tensor model once.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientTensorPresentation (W : Scheme.{t}) :=
  AmbientTensorPresentation.ofComparison
    (IntegralOnSlice.duality l E W none).models.comparison
    (IntegralOnSlice.Good l E W none) (fun _ h ↦ h.1)

/-- The recorded ambient cochain category.
Source: Stacks 05RU (blueprint: lem-pur-integral-ambient-operation-models). -/
def ambientCx (W : Scheme.{t}) := (ambientTensorPresentation l E W).Cx

set_option warn.classDefReducibility false in
@[irreducible] def ambientCxCategory (W : Scheme.{t}) : Category (ambientCx l E W) :=
  (ambientTensorPresentation l E W).cxCategory

attribute [instance 5000] ambientCxCategory

/-- Good complexes in the recorded ambient cochain category.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
def ambientGood (W : Scheme.{t}) : ObjectProperty (ambientCx l E W) :=
  (ambientTensorPresentation l E W).Good

/-- K-flat complexes in the recorded ambient cochain category.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
abbrev ambientFlat (W : Scheme.{t}) : ObjectProperty (ambientCx l E W) :=
  (ambientTensorPresentation l E W).Flat

/-- Every good representative belongs to the recorded K-flat class.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
theorem ambientGoodFlat (W : Scheme.{t}) (P : ambientCx l E W)
    (h : ambientGood l E W P) : ambientFlat l E W P :=
  (ambientTensorPresentation l E W).good_flat P h

/-- The recorded ambient derived category.
Source: Stacks 05RU (blueprint: lem-pur-integral-ambient-operation-models). -/
def ambientD (W : Scheme.{t}) := (ambientTensorPresentation l E W).D

set_option warn.classDefReducibility false in
/-- Share its recorded category structure throughout the comparisons.
Source: Stacks 05RU (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientDCategory (W : Scheme.{t}) : Category (ambientD l E W) :=
  (ambientTensorPresentation l E W).dCategory

attribute [instance 5000] ambientDCategory

/-- The localization functor of the recorded ambient derived category.
Source: Stacks 05RU (blueprint: lem-pur-integral-ambient-operation-models). -/
def ambientQ (W : Scheme.{t}) : ambientCx l E W ⥤ ambientD l E W :=
  by with_unfolding_all exact (ambientTensorPresentation l E W).Q

/-- Its class of quasi-isomorphisms, taken from the same localization data.
Source: Stacks 05RU (blueprint: lem-pur-integral-ambient-operation-models). -/
def ambientQuasiIso (W : Scheme.{t}) : MorphismProperty (ambientCx l E W) := by
  with_unfolding_all exact ((fun {C : Type _} [c : Category C] (V : MorphismProperty C)
    (_ : MorphismProperty.HasLocalization V) => V) _
      (IntegralOnSlice.hasDerived l E W none))

/-- The recorded ambient functor is a localization.
Source: Stacks 05RU (blueprint: lem-pur-integral-ambient-operation-models). -/
@[instance] theorem ambientQ_isLocalization (W : Scheme.{t}) :
    (ambientQ l E W).IsLocalization (ambientQuasiIso l E W) := by
  with_unfolding_all exact
    @MorphismProperty.HasLocalization.hL _ _ _ (IntegralOnSlice.hasDerived l E W none)

/-- Ordinary pullback in the recorded ambient cochain presentation.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientPullComplex {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ambientCx l E Y ⥤ ambientCx l E X := by
  with_unfolding_all exact pullComplex l E f

/-- The ordinary total tensor of the recorded slice coefficient presentation.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientTotalTensor (W : Scheme.{t}) :
    ambientCx l E W × ambientCx l E W ⥤ ambientCx l E W :=
  by with_unfolding_all exact (ambientTensorPresentation l E W).totalTensor

/-- Pullback preserves the recorded good complexes.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
theorem ambientPullGood {X Y : Scheme.{t}} (f : X ⟶ Y) (P : ambientCx l E Y)
    (hP : ambientGood l E Y P) : ambientGood l E X ((ambientPullComplex l E f).obj P) := by
  with_unfolding_all exact pull_good l E f P hP

/-- Ordinary total tensor preserves the recorded good complexes.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
theorem ambientTensorGood (W : Scheme.{t}) (P Q : ambientCx l E W)
    (hP : ambientGood l E W P) (hQ : ambientGood l E W Q) :
    ambientGood l E W ((ambientTotalTensor l E W).obj (P, Q)) := by
  with_unfolding_all exact tensor_good l E W P Q hP hQ

/-- The Roos functor on the same ambient cochain category.
Source: Stacks 08TC (blueprint: lem-pur-integral-ambient-operation-models). -/
def ambientRoos (W : Scheme.{t}) :
    (ℕᵒᵖ ⥤ ambientCx l E W) ⥤ ambientCx l E W := by
  with_unfolding_all exact
    integralOperationsRoosFunctor (A := IntegralOnSlice.Mod l E W none)

/-- The ordinary quotient tower in the captured cochain category.
Source: Stacks 0941 (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientQuotientTower (W : Scheme.{t}) :
    ambientCx l E W ⥤ (ℕᵒᵖ ⥤ ambientCx l E W) := by
  with_unfolding_all exact IntegralOnSlice.tower l E W none

/-- Its Roos complex functor, with the captured category data.
Source: Stacks 08TC (blueprint: lem-pur-integral-ambient-operation-models). -/
def ambientRoosComplex (W : Scheme.{t}) : ambientCx l E W ⥤ ambientCx l E W :=
  ambientQuotientTower l E W ⋙ ambientRoos l E W

/-- The quotient augmentation into this Roos complex.
Source: Stacks 08TC (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientRoosUnit (W : Scheme.{t}) (P : ambientCx l E W) :
    P ⟶ (ambientRoosComplex l E W).obj P := by
  with_unfolding_all exact IntegralOnSlice.roosUnit l E W none P

/-- The recorded finite pullback tower in this cochain presentation.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientRecordedPullTower {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ambientCx l E Y ⥤ (ℕᵒᵖ ⥤ ambientCx l E X) := by
  with_unfolding_all exact integralOperationsPullbackTowerFunctor l E f

/-- The recorded finite tensor tower in this cochain presentation.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientRecordedTensorTower (W : Scheme.{t}) :
    ambientCx l E W × ambientCx l E W ⥤ (ℕᵒᵖ ⥤ ambientCx l E W) := by
  with_unfolding_all exact integralOperationsTensorTowerFunctor l E W

/-- The recorded finite pullback Roos complex.
Source: Stacks 08TC (blueprint: lem-pur-integral-ambient-operation-models). -/
def ambientRecordedPullComplex {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ambientCx l E Y ⥤ ambientCx l E X :=
  ambientRecordedPullTower l E f ⋙ ambientRoos l E X

/-- The recorded finite tensor Roos complex.
Source: Stacks 08TC (blueprint: lem-pur-integral-ambient-operation-models). -/
def ambientRecordedTensorComplex (W : Scheme.{t}) :
    ambientCx l E W × ambientCx l E W ⥤ ambientCx l E W :=
  ambientRecordedTensorTower l E W ⋙ ambientRoos l E W

/-- The specified pullback tower comparison, sharing its source category data.
Source: Stacks 03EL (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientPullTowerIso {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ambientPullComplex l E f ⋙ ambientQuotientTower l E X ≅
      ambientRecordedPullTower l E f := by
  with_unfolding_all exact pullTowerIso l E f

/-- The specified tensor tower comparison, sharing its source category data.
Source: Stacks 03EL (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientTensorTowerIso (W : Scheme.{t}) :
    ambientTotalTensor l E W ⋙ ambientQuotientTower l E W ≅
      ambientRecordedTensorTower l E W := by
  with_unfolding_all exact tensorTowerIso l E W

/-- The recorded derived pullback in this derived category.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientPull {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ambientD l E Y ⥤ ambientD l E X := by
  with_unfolding_all exact integralDerivedPullback l E f

/-- The recorded completed tensor in this derived category.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientCompletedTensor (W : Scheme.{t}) :
    ambientD l E W × ambientD l E W ⥤ ambientD l E W := by
  with_unfolding_all exact integralCompletedTensor l E W

/-- Localization restricted to the good representatives.
Source: Stacks 06YY, 07A4, 08TC
(blueprint: lem-pur-integral-ambient-operation-models). -/
def ambientGoodLocalization (W : Scheme.{t}) :
    (ambientGood l E W).FullSubcategory ⥤
      ambientD l E W :=
  (ambientGood l E W).ι ⋙ (ambientQ l E W)

/-- The finite pullback operation on good representatives.
Source: Stacks 06YY, 07A4, 08TC
(blueprint: lem-pur-integral-ambient-operation-models). -/
def ambientPullOnGood {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (ambientGood l E Y).FullSubcategory ⥤
      ambientD l E X :=
  (ambientGood l E Y).ι ⋙
    ambientRecordedPullComplex l E f ⋙ (ambientQ l E X)

/-- The finite tensor operation on pairs of good representatives.
Source: Stacks 06YY, 07A4, 08TC
(blueprint: lem-pur-integral-ambient-operation-models). -/
def ambientTensorOnGood (W : Scheme.{t}) :
    (ambientGood l E W).FullSubcategory ×
      (ambientGood l E W).FullSubcategory ⥤
        ambientD l E W :=
  ((ambientGood l E W).ι.prod
    (ambientGood l E W).ι) ⋙
      ambientRecordedTensorComplex l E W ⋙ (ambientQ l E W)

/-- The Roos completion on good representatives.
Source: Stacks 06YY, 07A4, 08TC
(blueprint: lem-pur-integral-ambient-operation-models). -/
def ambientCompletionOnGood (W : Scheme.{t}) :
    (ambientGood l E W).FullSubcategory ⥤ ambientD l E W :=
  (ambientGood l E W).ι ⋙ ambientRoosComplex l E W ⋙ ambientQ l E W

/-- The recorded pullback comparison on good representatives.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientPullComparison {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ambientGoodLocalization l E Y ⋙ ambientPull l E f ≅ ambientPullOnGood l E f := by
  with_unfolding_all exact integralDerivedPullbackComparison l E f

/-- The recorded tensor comparison on good representatives.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientTensorComparison (W : Scheme.{t}) :
    (ambientGoodLocalization l E W).prod (ambientGoodLocalization l E W) ⋙
      ambientCompletedTensor l E W ≅ ambientTensorOnGood l E W := by
  with_unfolding_all exact integralCompletedTensorComparison l E W

/-- Completion in the recorded ambient derived category.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientCompletion (W : Scheme.{t}) : ambientD l E W ⥤ ambientD l E W := by
  with_unfolding_all exact IntegralOnSlice.completion l E W none

/-- The recorded completion comparison.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientCompletionComparison (W : Scheme.{t}) :
    ambientGoodLocalization l E W ⋙ ambientCompletion l E W ≅
      ambientCompletionOnGood l E W := by
  with_unfolding_all exact IntegralOnSlice.completionComparison l E W none

/-- The recorded completion unit.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientCompletionUnit (W : Scheme.{t}) :
    𝟭 (ambientD l E W) ⟶ ambientCompletion l E W :=
  by with_unfolding_all exact IntegralOnSlice.completionUnit l E W none

/-- Ordinary derived tensor in the recorded ambient category.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientOrdinaryTensor (W : Scheme.{t}) :
    ambientD l E W × ambientD l E W ⥤ ambientD l E W :=
  by with_unfolding_all exact (ambientTensorPresentation l E W).tensor

/-- The whole ordinary tensor model comparison, with its category data shared once.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def ambientTensorModelComparison (W : Scheme.{t}) :
    ((ambientFlat l E W).ι.prod (ambientFlat l E W).ι) ⋙
      ambientTotalTensor l E W ⋙ ambientQ l E W ≅
        (((ambientFlat l E W).ι ⋙ ambientQ l E W).prod
          ((ambientFlat l E W).ι ⋙ ambientQ l E W)) ⋙ ambientOrdinaryTensor l E W := by
  unfold ambientTotalTensor ambientQ ambientOrdinaryTensor
  with_unfolding_all exact (ambientTensorPresentation l E W).comparison

attribute [local irreducible] integralOperationsLevelPullback
  Scheme.coefficientProEtaleModulePullback unrestrictedIntegralReductionFunctor
  IntegralOnSlice.reduction IntegralOnSlice.reductionWitness

/-- Construct the universal ambient pullback counit.
Source: Stacks 06YY and 0G7E
(blueprint: lem-pur-integral-ambient-operation-models).

Proof: present pullback using independent-universe inverse image and scalar extension.
Uniqueness of left adjoints identifies it with the recorded pullback. Apply the
ringed derived-pullback theorem, transport its universal counit from homotopy
representatives to cochains, then transport along that left-adjoint isomorphism.
Good complexes remain good under pullback, so the counit is an isomorphism there. -/
theorem rawAmbientDerivedData {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ∃ (F : ambientD l E Y ⥤
        ambientD l E X)
      (ε : ambientQ l E Y ⋙ F ⟶ ambientPullComplex l E f ⋙ ambientQ l E X),
      F.IsLeftDerivedFunctor ε
        (ambientQuasiIso l E Y) ∧
      ∀ P : (ambientGood l E Y).FullSubcategory,
        IsIso (ε.app P.obj) := by
  let : EssentiallySmall.{max u (t + 1)} Y.ProEt := essentiallySmallSelf _
  let : EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf _
  let : HasSheafify (ProEt.topology Y) (Type (max u (t + 1))) :=
    hasSheafifyEssentiallySmallSite _ _
  let : HasSheafify (ProEt.topology X) (Type (max u (t + 1))) :=
    hasSheafifyEssentiallySmallSite _ _
  let G := Scheme.proEtaleBaseChange f
  let L := G.sheafPullback (Type (max u (t + 1))) (ProEt.topology Y) (ProEt.topology X)
  let a := G.sheafAdjunctionContinuous (Type (max u (t + 1)))
    (ProEt.topology Y) (ProEt.topology X)
  let : ReflectsLimits (forget (Type (max u (t + 1)))) :=
    reflectsLimits_of_reflectsIsomorphisms
  let : RepresentablyFlat G := flat_of_preservesFiniteLimits G
  let : PreservesFiniteLimits (G.op.lan : (Y.ProEtᵒᵖ ⥤ Type (max u (t + 1))) ⥤
      X.ProEtᵒᵖ ⥤ Type (max u (t + 1))) :=
    by
      let : AB5OfSize.{t, t + 1} (Type (max u (t + 1))) :=
        AB5OfSize_shrink.{t, t + 1, max u (t + 1), max u (t + 1)} _
      exact preservesFiniteLimits_op_lan_of_flat G
  let : PreservesFiniteLimits L :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits G
      (Type (max u (t + 1))) (ProEt.topology Y) (ProEt.topology X)
  obtain ⟨RI, I, c, T, hT, hobj, hmap, ⟨am⟩⟩ :=
    SheafOfModules.RingedPresentationOnSites.continuous_ringed_pullback_presentation
      G L a (completedIntegralCommRingSheafUnrestricted l E X)
      (completedIntegralCommRingSheafUnrestricted l E Y) (coefficientMap l E f)
  let := hT
  have am' : T ⊣ push l E f := by
    unfold push
    let q := ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat RingCat)).map
      (coefficientMap l E f))
    have hq : q = (⟨Functor.whiskerRight (coefficientMap l E f).hom
        (forget₂ CommRingCat RingCat)⟩) := rfl
    change T ⊣ SheafOfModules.pushforward q at am
    rw [hq] at am
    exact am
  let e : T ≅ pull l E f := am'.leftAdjointUniq (adjunction l E f)
  obtain ⟨F, ε, hkan, hε⟩ :=
    SheafOfModules.ringedPullbackCochainPresentation L _ a I c T hobj hmap
  letI := (fun {A B : Type _} [Category.{_} A] [d : Category.{_} B] (_ : A ⥤ B) ↦ d) F
  let ec := NatIso.mapHomologicalComplex e (.up ℤ)
  let d := Functor.isoWhiskerRight ec
    (DerivedCategory.Q (C := integralTowerModules l E X))
  let εc := ε ≫ d.hom
  have hεc (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
      IsIso (εc.app P.obj) := by
    have hp : integralOperationsGoodComplex l E Y P.obj := by
      with_unfolding_all exact P.property
    unfold integralOperationsGoodComplex at hp
    letI := hε P.obj hp.1 hp.2
    change IsIso (ε.app P.obj ≫ d.hom.app P.obj)
    infer_instance
  with_unfolding_all refine ⟨F, εc, ⟨?_⟩, ?_⟩
  · with_unfolding_all exact (Functor.isRightKanExtension_iff_of_iso₂
      ε εc d (Iso.refl _) (by simp [εc])).mp hkan
  · intro P
    with_unfolding_all exact hεc P

/-- The defining augmentation law of the recorded completion unit.
Source: Stacks 06YY, 07A4, 08TC
(blueprint: lem-pur-integral-ambient-operation-models). -/
theorem rawAmbientCompletionUnit_app (W : Scheme.{t})
    (P : (ambientGood l E W).FullSubcategory) :
    (ambientCompletionUnit l E W).app ((ambientGoodLocalization l E W).obj P) ≫
      (ambientCompletionComparison l E W).hom.app P =
        (ambientQ l E W).map (ambientRoosUnit l E W P.obj) := by
  unfold ambientCompletionUnit ambientCompletionComparison ambientCompletion ambientQ
  with_unfolding_all exact
    ((IntegralOnSlice.completionUnit_existsUnique l E W none).exists.choose_spec
      (show (IntegralOnSlice.Good l E W none).FullSubcategory from P))

/-- Good representatives localize to the ambient derived category.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
theorem rawAmbientGoodLocalization (W : Scheme.{t}) :
    (ambientGoodLocalization l E W).IsLocalization
      ((ambientQuasiIso l E W).inverseImage (ambientGood l E W).ι) := by
  unfold ambientGoodLocalization ambientQ ambientQuasiIso
  with_unfolding_all exact IntegralOnSlice.goodLocalization l E W none

universe a₂ b₂ c₂ d₂ e₂ f₂

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- The operation constructions with their compatibility laws. Carrier categories
and good objects are fixed parameters, so the laws share exactly the same functors.
Source: Stacks 06YY, 07A4, 08TC
(blueprint: lem-pur-integral-ambient-operation-models). -/
structure AmbientOperationData
    (I : Type a₂) [Category.{b₂} I]
    (C : I → Type c₂) [cc : ∀ W, Category.{d₂} (C W)]
    (D : I → Type e₂) [dd : ∀ W, Category.{f₂} (D W)]
    (P K : ∀ W, ObjectProperty (C W))
    (V : ∀ W, MorphismProperty (C W)) where
  Q (W : I) : C W ⥤ D W
  totalTensor (W : I) : C W × C W ⥤ C W
  ordinaryTensor (W : I) : D W × D W ⥤ D W
  roos (W : I) : (ℕᵒᵖ ⥤ C W) ⥤ C W
  quotientTower (W : I) : C W ⥤ (ℕᵒᵖ ⥤ C W)
  pullComplex {X Y : I} (f : X ⟶ Y) : C Y ⥤ C X
  recordedPullTower {X Y : I} (f : X ⟶ Y) : C Y ⥤ (ℕᵒᵖ ⥤ C X)
  recordedTensorTower (W : I) : C W × C W ⥤ (ℕᵒᵖ ⥤ C W)
  completion (W : I) : D W ⥤ D W
  completionUnit (W : I) : 𝟭 (D W) ⟶ completion W
  derivedPull {X Y : I} (f : X ⟶ Y) : D Y ⥤ D X
  completedTensor (W : I) : D W × D W ⥤ D W
  qLocalization (W : I) : (Q W).IsLocalization (V W)
  pullGood {X Y : I} (f : X ⟶ Y) (Z : C Y) : P Y Z → P X ((pullComplex f).obj Z)
  tensorGood (W : I) (Z Z' : C W) : P W Z → P W Z' →
    P W ((totalTensor W).obj (Z, Z'))
  pullTowerIso {X Y : I} (f : X ⟶ Y) :
    pullComplex f ⋙ quotientTower X ≅ recordedPullTower f
  tensorTowerIso (W : I) : totalTensor W ⋙ quotientTower W ≅ recordedTensorTower W
  tensorModelComparison (W : I) :
    (K W).ι.prod (K W).ι ⋙ totalTensor W ⋙ Q W ≅
      ((K W).ι ⋙ Q W).prod ((K W).ι ⋙ Q W) ⋙ ordinaryTensor W
  pullComparison {X Y : I} (f : X ⟶ Y) :
    ((P Y).ι ⋙ Q Y) ⋙ derivedPull f ≅ (P Y).ι ⋙ (recordedPullTower f ⋙ roos X) ⋙ Q X
  tensorComparison (W : I) :
    ((P W).ι ⋙ Q W).prod ((P W).ι ⋙ Q W) ⋙ completedTensor W ≅
      (P W).ι.prod (P W).ι ⋙ (recordedTensorTower W ⋙ roos W) ⋙ Q W
  completionComparison (W : I) :
    ((P W).ι ⋙ Q W) ⋙ completion W ≅ (P W).ι ⋙ (quotientTower W ⋙ roos W) ⋙ Q W
  roosUnit (W : I) (Z : C W) : Z ⟶ (quotientTower W ⋙ roos W).obj Z
  unitLaw (W : I) (Z : (P W).FullSubcategory) :
    (completionUnit W).app (((P W).ι ⋙ Q W).obj Z) ≫
      (completionComparison W).hom.app Z = (Q W).map (roosUnit W Z.obj)
  goodLocalization (W : I) : ((P W).ι ⋙ Q W).IsLocalization ((V W).inverseImage (P W).ι)
  derivedData {X Y : I} (f : X ⟶ Y) :
    ∃ (F : D Y ⥤ D X) (ε : Q Y ⋙ F ⟶ pullComplex f ⋙ Q X),
      F.IsRightKanExtension ε ∧ ∀ Z : (P Y).FullSubcategory, IsIso (ε.app Z.obj)

/-- Equality to a constructed value specifies it uniquely.
Source: equality reflexivity (blueprint: lem-pur-integral-ambient-operation-models). -/
theorem operationDataCopy_existsUnique {A : Type*} (a : A) : ∃! b : A, b = a :=
  ⟨a, rfl, fun _ h ↦ h⟩

/-- Share a constructed value through its proved specification.
Source: the preceding unique construction
(blueprint: lem-pur-integral-ambient-operation-models). -/
@[irreducible] def operationDataCopy {A : Type*} (a : A) : A :=
  (operationDataCopy_existsUnique a).exists.choose

/-- The shared value is the original constructed value.
Source: the preceding unique construction
(blueprint: lem-pur-integral-ambient-operation-models). -/
theorem operationDataCopy_eq {A : Type*} (a : A) : operationDataCopy a = a := by
  unfold operationDataCopy
  exact (operationDataCopy_existsUnique a).exists.choose_spec

/-- Package the recorded constructions and their already proved compatibility laws.
Source: Stacks 06YY, 07A4, 08TC
(blueprint: lem-pur-integral-ambient-operation-models). -/
def rawAmbientPackage : AmbientOperationData Scheme
    (ambientCx l E) (ambientD l E) (ambientGood l E) (ambientFlat l E)
      (ambientQuasiIso l E) where
  Q := ambientQ l E
  totalTensor := ambientTotalTensor l E
  ordinaryTensor := ambientOrdinaryTensor l E
  roos := ambientRoos l E
  quotientTower := ambientQuotientTower l E
  pullComplex := ambientPullComplex l E
  recordedPullTower := ambientRecordedPullTower l E
  recordedTensorTower := ambientRecordedTensorTower l E
  completion := ambientCompletion l E
  completionUnit := ambientCompletionUnit l E
  derivedPull := ambientPull l E
  completedTensor := ambientCompletedTensor l E
  qLocalization := ambientQ_isLocalization l E
  pullGood := ambientPullGood l E
  tensorGood := ambientTensorGood l E
  pullTowerIso := ambientPullTowerIso l E
  tensorTowerIso := ambientTensorTowerIso l E
  tensorModelComparison := ambientTensorModelComparison l E
  pullComparison := ambientPullComparison l E
  tensorComparison := ambientTensorComparison l E
  completionComparison := ambientCompletionComparison l E
  roosUnit := ambientRoosUnit l E
  unitLaw := rawAmbientCompletionUnit_app l E
  goodLocalization := rawAmbientGoodLocalization l E
  derivedData f := by
    obtain ⟨F, ε, hF, hε⟩ := rawAmbientDerivedData l E f
    exact ⟨F, ε, hF.isRightKanExtension, hε⟩

/-- The same recorded operations, shared as one specified record.
Source: the preceding constructed package
(blueprint: lem-pur-integral-ambient-operation-models).

The specifying theorem is proved by reflexivity. It determines the entire record by
literal equality to rawAmbientPackage, rather than selecting unspecified operation data. -/
@[irreducible] def ambientPackage := operationDataCopy (rawAmbientPackage l E)

/-- No operation is changed by sharing the package.
Source: the preceding unique construction
(blueprint: lem-pur-integral-ambient-operation-models). -/
theorem ambientPackage_eq : ambientPackage l E = rawAmbientPackage l E := by
  unfold ambientPackage
  exact operationDataCopy_eq _
/-- The localization functor of the recorded ambient derived category.
Source: Stacks 05RU (blueprint: lem-pur-integral-ambient-operation-models). -/
def modelQ (W : Scheme.{t}) : ambientCx l E W ⥤ ambientD l E W :=
  (ambientPackage l E).Q W

/-- Ordinary pullback in the recorded ambient cochain presentation.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
def modelPullComplex {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ambientCx l E Y ⥤ ambientCx l E X :=
  (ambientPackage l E).pullComplex f

/-- The ordinary total tensor of the recorded slice coefficient presentation.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
def modelTotalTensor (W : Scheme.{t}) :
    ambientCx l E W × ambientCx l E W ⥤ ambientCx l E W :=
  (ambientPackage l E).totalTensor W

/-- Pullback preserves the recorded good complexes.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
theorem modelPullGood {X Y : Scheme.{t}} (f : X ⟶ Y) (P : ambientCx l E Y)
    (hP : ambientGood l E Y P) : ambientGood l E X ((modelPullComplex l E f).obj P) :=
  (ambientPackage l E).pullGood f P hP

/-- Ordinary total tensor preserves the recorded good complexes.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
theorem modelTensorGood (W : Scheme.{t}) (P Q : ambientCx l E W)
    (hP : ambientGood l E W P) (hQ : ambientGood l E W Q) :
    ambientGood l E W ((modelTotalTensor l E W).obj (P, Q)) :=
  (ambientPackage l E).tensorGood W P Q hP hQ

/-- The Roos functor on the same ambient cochain category.
Source: Stacks 08TC (blueprint: lem-pur-integral-ambient-operation-models). -/
def modelRoos (W : Scheme.{t}) :
    (ℕᵒᵖ ⥤ ambientCx l E W) ⥤ ambientCx l E W :=
  (ambientPackage l E).roos W

/-- The ordinary quotient tower in the captured cochain category.
Source: Stacks 0941 (blueprint: lem-pur-integral-ambient-operation-models). -/
def modelQuotientTower (W : Scheme.{t}) :
    ambientCx l E W ⥤ (ℕᵒᵖ ⥤ ambientCx l E W) :=
  (ambientPackage l E).quotientTower W

/-- Its Roos complex functor, with the captured category data.
Source: Stacks 08TC (blueprint: lem-pur-integral-ambient-operation-models). -/
def modelRoosComplex (W : Scheme.{t}) : ambientCx l E W ⥤ ambientCx l E W :=
  modelQuotientTower l E W ⋙ modelRoos l E W

/-- The quotient augmentation into this Roos complex.
Source: Stacks 08TC (blueprint: lem-pur-integral-ambient-operation-models). -/
def modelRoosUnit (W : Scheme.{t}) (P : ambientCx l E W) :
    P ⟶ (modelRoosComplex l E W).obj P :=
  (ambientPackage l E).roosUnit W P

/-- The recorded finite pullback tower in this cochain presentation.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
def modelRecordedPullTower {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ambientCx l E Y ⥤ (ℕᵒᵖ ⥤ ambientCx l E X) :=
  (ambientPackage l E).recordedPullTower f

/-- The recorded finite tensor tower in this cochain presentation.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
def modelRecordedTensorTower (W : Scheme.{t}) :
    ambientCx l E W × ambientCx l E W ⥤ (ℕᵒᵖ ⥤ ambientCx l E W) :=
  (ambientPackage l E).recordedTensorTower W

/-- The recorded finite pullback Roos complex.
Source: Stacks 08TC (blueprint: lem-pur-integral-ambient-operation-models). -/
def modelRecordedPullComplex {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ambientCx l E Y ⥤ ambientCx l E X :=
  modelRecordedPullTower l E f ⋙ modelRoos l E X

/-- The recorded finite tensor Roos complex.
Source: Stacks 08TC (blueprint: lem-pur-integral-ambient-operation-models). -/
def modelRecordedTensorComplex (W : Scheme.{t}) :
    ambientCx l E W × ambientCx l E W ⥤ ambientCx l E W :=
  modelRecordedTensorTower l E W ⋙ modelRoos l E W

/-- The specified pullback tower comparison, sharing its source category data.
Source: Stacks 03EL (blueprint: lem-pur-integral-ambient-operation-models). -/
def modelPullTowerIso {X Y : Scheme.{t}} (f : X ⟶ Y) :
    modelPullComplex l E f ⋙ modelQuotientTower l E X ≅
      modelRecordedPullTower l E f :=
  (ambientPackage l E).pullTowerIso f

/-- The specified tensor tower comparison, sharing its source category data.
Source: Stacks 03EL (blueprint: lem-pur-integral-ambient-operation-models). -/
def modelTensorTowerIso (W : Scheme.{t}) :
    modelTotalTensor l E W ⋙ modelQuotientTower l E W ≅
      modelRecordedTensorTower l E W :=
  (ambientPackage l E).tensorTowerIso W

/-- The recorded derived pullback in this derived category.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
def modelPull {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ambientD l E Y ⥤ ambientD l E X :=
  (ambientPackage l E).derivedPull f

/-- The recorded completed tensor in this derived category.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
def modelCompletedTensor (W : Scheme.{t}) :
    ambientD l E W × ambientD l E W ⥤ ambientD l E W :=
  (ambientPackage l E).completedTensor W

/-- Localization restricted to the good representatives in the shared data.
Source: Stacks 06YY, 07A4, 08TC
(blueprint: lem-pur-integral-ambient-operation-models). -/
def modelGoodLocalization (W : Scheme.{t}) :
    (ambientGood l E W).FullSubcategory ⥤
      ambientD l E W :=
  (ambientGood l E W).ι ⋙ (modelQ l E W)

/-- The recorded finite pullback on good representatives in the shared data.
Source: Stacks 06YY, 07A4, 08TC
(blueprint: lem-pur-integral-ambient-operation-models). -/
def modelPullOnGood {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (ambientGood l E Y).FullSubcategory ⥤
      ambientD l E X :=
  (ambientGood l E Y).ι ⋙
    modelRecordedPullComplex l E f ⋙ (modelQ l E X)

/-- The recorded finite tensor on pairs of good representatives in the shared data.
Source: Stacks 06YY, 07A4, 08TC
(blueprint: lem-pur-integral-ambient-operation-models). -/
def modelTensorOnGood (W : Scheme.{t}) :
    (ambientGood l E W).FullSubcategory ×
      (ambientGood l E W).FullSubcategory ⥤
        ambientD l E W :=
  ((ambientGood l E W).ι.prod
    (ambientGood l E W).ι) ⋙
      modelRecordedTensorComplex l E W ⋙ (modelQ l E W)

/-- The ordinary tensor as a functor into good representatives.
Source: Stacks 06YY, 07A4, 08TC
(blueprint: lem-pur-integral-ambient-operation-models). -/
def modelTensorGoodLift (W : Scheme.{t}) :
    (ambientGood l E W).FullSubcategory ×
      (ambientGood l E W).FullSubcategory ⥤
        (ambientGood l E W).FullSubcategory :=
  ObjectProperty.lift _ (((ambientGood l E W).ι.prod
    (ambientGood l E W).ι) ⋙
      modelTotalTensor l E W)
    (fun P ↦ modelTensorGood l E W P.1.obj P.2.obj P.1.property P.2.property)

/-- The ordinary pullback as a functor into good representatives.
Source: Stacks 06YY, 07A4, 08TC
(blueprint: lem-pur-integral-ambient-operation-models). -/
def modelPullGoodLift {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (ambientGood l E Y).FullSubcategory ⥤ (ambientGood l E X).FullSubcategory :=
  (ambientGood l E X).lift ((ambientGood l E Y).ι ⋙ modelPullComplex l E f)
    (fun P ↦ modelPullGood l E f P.obj P.property)

/-- The quotient-tower Roos completion on good representatives.
Source: Stacks 06YY, 07A4, 08TC
(blueprint: lem-pur-integral-ambient-operation-models). -/
def modelCompletionOnGood (W : Scheme.{t}) :
    (ambientGood l E W).FullSubcategory ⥤ ambientD l E W :=
  (ambientGood l E W).ι ⋙ modelRoosComplex l E W ⋙ modelQ l E W

/-- The recorded pullback comparison on good representatives.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
def modelPullComparison {X Y : Scheme.{t}} (f : X ⟶ Y) :
    modelGoodLocalization l E Y ⋙ modelPull l E f ≅ modelPullOnGood l E f :=
  (ambientPackage l E).pullComparison f

/-- The recorded tensor comparison on good representatives.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
def modelTensorComparison (W : Scheme.{t}) :
    (modelGoodLocalization l E W).prod (modelGoodLocalization l E W) ⋙
      modelCompletedTensor l E W ≅ modelTensorOnGood l E W :=
  (ambientPackage l E).tensorComparison W

/-- Completion in the recorded ambient derived category.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
def modelCompletion (W : Scheme.{t}) : ambientD l E W ⥤ ambientD l E W :=
  (ambientPackage l E).completion W

/-- The recorded completion comparison.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
def modelCompletionComparison (W : Scheme.{t}) :
    modelGoodLocalization l E W ⋙ modelCompletion l E W ≅
      modelCompletionOnGood l E W :=
  (ambientPackage l E).completionComparison W

/-- The recorded completion unit.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
def modelCompletionUnit (W : Scheme.{t}) :
    𝟭 (ambientD l E W) ⟶ modelCompletion l E W :=
  (ambientPackage l E).completionUnit W

/-- Ordinary derived tensor in the recorded ambient category.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
def modelOrdinaryTensor (W : Scheme.{t}) :
    ambientD l E W × ambientD l E W ⥤ ambientD l E W :=
  (ambientPackage l E).ordinaryTensor W

/-- The derived image of the recorded pullback tower comparison.
Source: Stacks 03EL (blueprint: lem-pur-integral-ambient-operation-models). -/
def modelPullTowerMap {X Y : Scheme.{t}} (f : X ⟶ Y)
    (P : ambientCx l E Y) :
    (modelQ l E X).obj ((modelRoosComplex l E X).obj
      ((modelPullComplex l E f).obj P)) ⟶
        (modelQ l E X).obj ((modelRecordedPullComplex l E f).obj P) := by
  dsimp only [modelRoosComplex, modelRecordedPullComplex, modelRecordedTensorComplex]
  exact ((modelQ l E X).map
    ((modelRoos l E X).map ((modelPullTowerIso l E f).hom.app P)))

/-- The derived image of the specified pullback augmentation.
Source: Stacks 08TC (blueprint: lem-pur-integral-ambient-operation-models). -/
def modelPullUnitMap {X Y : Scheme.{t}} (f : X ⟶ Y)
    (P : ambientCx l E Y) :
    (modelQ l E X).obj ((modelPullComplex l E f).obj P) ⟶
      (modelQ l E X).obj ((modelRecordedPullComplex l E f).obj P) := by
  dsimp only [modelRoosComplex, modelRecordedPullComplex, modelRecordedTensorComplex]
  exact ((modelQ l E X).map
    (modelRoosUnit l E X ((modelPullComplex l E f).obj P) ≫
      (modelRoos l E X).map ((modelPullTowerIso l E f).hom.app P)))

/-- The derived image of the specified strict tensor tower map.
Source: Stacks 03EL (blueprint: lem-pur-integral-ambient-operation-models). -/
def modelTensorTowerMap (W : Scheme.{t}) (P Q : ambientCx l E W) :
    (modelQ l E W).obj
      ((modelRoosComplex l E W).obj ((modelTotalTensor l E W).obj (P, Q))) ⟶
      (modelQ l E W).obj ((modelRecordedTensorComplex l E W).obj (P, Q)) := by
  dsimp only [modelRoosComplex, modelRecordedPullComplex, modelRecordedTensorComplex]
  exact ((modelQ l E W).map
    ((modelRoos l E W).map ((modelTensorTowerIso l E W).hom.app (P, Q))))

/-- The derived image of the specified tensor augmentation.
Source: Stacks 08TC (blueprint: lem-pur-integral-ambient-operation-models). -/
def modelTensorUnitMap (W : Scheme.{t}) (P Q : ambientCx l E W) :
    (modelQ l E W).obj ((modelTotalTensor l E W).obj (P, Q)) ⟶
      (modelQ l E W).obj ((modelRecordedTensorComplex l E W).obj (P, Q)) := by
  dsimp only [modelRoosComplex, modelRecordedPullComplex, modelRecordedTensorComplex]
  exact ((modelQ l E W).map
    (modelRoosUnit l E W ((modelTotalTensor l E W).obj (P, Q)) ≫
      (modelRoos l E W).map ((modelTensorTowerIso l E W).hom.app (P, Q))))

/-- The whole ordinary tensor model comparison, with its category data shared once.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
def modelTensorModelComparison (W : Scheme.{t}) :
    ((ambientFlat l E W).ι.prod (ambientFlat l E W).ι) ⋙
      modelTotalTensor l E W ⋙ modelQ l E W ≅
        (((ambientFlat l E W).ι ⋙ modelQ l E W).prod
          ((ambientFlat l E W).ι ⋙ modelQ l E W)) ⋙ modelOrdinaryTensor l E W :=
  (ambientPackage l E).tensorModelComparison W

/-- Localization for the shared ambient operation record.
Source: Stacks 05RU (blueprint: lem-pur-integral-ambient-operation-models). -/
@[instance] theorem modelQ_isLocalization (W : Scheme.{t}) :
    (modelQ l E W).IsLocalization (ambientQuasiIso l E W) :=
  (ambientPackage l E).qLocalization W

private theorem modelDerivedData {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ∃ (F : ambientD l E Y ⥤ ambientD l E X)
      (ε : modelQ l E Y ⋙ F ⟶ modelPullComplex l E f ⋙ modelQ l E X),
      F.IsLeftDerivedFunctor ε (ambientQuasiIso l E Y) ∧
        ∀ P : (ambientGood l E Y).FullSubcategory, IsIso (ε.app P.obj) := by
  obtain ⟨F, ε, hF, hε⟩ := (ambientPackage l E).derivedData f
  exact ⟨F, ε, ⟨hF⟩, hε⟩

private theorem modelCompletionUnit_app (W : Scheme.{t})
    (P : (ambientGood l E W).FullSubcategory) :
    (modelCompletionUnit l E W).app ((modelGoodLocalization l E W).obj P) ≫
      (modelCompletionComparison l E W).hom.app P =
        (modelQ l E W).map (modelRoosUnit l E W P.obj) :=
  (ambientPackage l E).unitLaw W P

/-- The recorded ordinary tensor comparison on good representatives.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
def tensorRepresentative (W : Scheme.{t})
    (P Q : (ambientGood l E W).FullSubcategory) :
    (modelQ l E W).obj ((modelTotalTensor l E W).obj (P.obj, Q.obj)) ≅
      (modelOrdinaryTensor l E W).obj
        ((modelQ l E W).obj P.obj, (modelQ l E W).obj Q.obj) :=
  (modelTensorModelComparison l E W).app
    (⟨P.obj, ambientGoodFlat l E W P.obj P.property⟩,
      ⟨Q.obj, ambientGoodFlat l E W Q.obj Q.property⟩)

attribute [local irreducible] tensorRepresentative

private theorem ambientPullUnitMap_factor {X Y : Scheme.{t}} (f : X ⟶ Y)
    (P : ambientCx l E Y) :
    (modelQ l E X).map
        (modelRoosUnit l E X ((modelPullComplex l E f).obj P)) ≫
      modelPullTowerMap l E f P = modelPullUnitMap l E f P := by
  unfold modelPullUnitMap modelPullTowerMap
  dsimp only [id, modelRoosComplex, modelRecordedPullComplex, Functor.comp_obj]
  exact ((modelQ l E X).map_comp _ _).symm

private theorem ambientTensorUnitMap_factor (W : Scheme.{t}) (P Q : ambientCx l E W) :
    (modelQ l E W).map
        (modelRoosUnit l E W ((modelTotalTensor l E W).obj (P, Q))) ≫
      modelTensorTowerMap l E W P Q = modelTensorUnitMap l E W P Q := by
  unfold modelTensorUnitMap modelTensorTowerMap
  dsimp only [id, modelRoosComplex, modelRecordedTensorComplex, Functor.comp_obj]
  exact ((modelQ l E W).map_comp _ _).symm

private theorem unitComposite
    {D : Type a₁} [Category.{b₁} D] (C : D ⥤ D) (η : 𝟭 D ⟶ C)
    {A B U Z T : D} (s : A ⟶ B) (c : C.obj B ⟶ Z) (d : Z ⟶ T) (r : B ⟶ Z)
    (e : C.obj A ⟶ U) (k : U ⟶ T)
    (he : e ≫ k = C.map s ≫ c ≫ d) (hr : η.app B ≫ c = r) :
    η.app A ≫ e ≫ k = s ≫ r ≫ d := by
  rw [he, ← η.naturality_assoc]
  dsimp only [Functor.id_map]
  rw [reassoc_of% hr]

@[irreducible] private def descendComparison
    {R S A D : Type*} [Category* R] [Category* S] [Category* A] [Category* D]
    (L : R ⥤ S) (hL : ((Functor.whiskeringLeft _ _ D).obj L).FullyFaithful)
    {F G : S ⥤ D} {H : R ⥤ A} {Q V : A ⥤ D} {T : R ⥤ D}
    (C : D ⥤ D) (e : L ⋙ F ≅ H ⋙ Q) (c : Q ⋙ C ≅ V)
    (b : H ⋙ V ≅ T) (g : L ⋙ G ≅ T) : F ⋙ C ≅ G :=
  hL.isoEquiv.symm
    (((Functor.associator L F C).symm ≪≫ Functor.isoWhiskerRight e C ≪≫
      Functor.associator H Q C ≪≫ Functor.isoWhiskerLeft H c ≪≫ b) ≪≫ g.symm)

private theorem descentComparison_properties
    {R S A D : Type*} [Category* R] [Category* S] [Category* A] [Category* D]
    (L : R ⥤ S) (hL : ((Functor.whiskeringLeft _ _ D).obj L).FullyFaithful)
    {F G : S ⥤ D} {H : R ⥤ A} {Q V : A ⥤ D} {T : R ⥤ D}
    (C : D ⥤ D) (η : 𝟭 D ⟶ C)
    (e : L ⋙ F ≅ H ⋙ Q) (c : Q ⋙ C ≅ V) (b : H ⋙ V ≅ T) (g : L ⋙ G ≅ T)
    (u : ∀ P : A, Q.obj P ⟶ V.obj P)
    (hu : ∀ P : A, η.app (Q.obj P) ≫ c.hom.app P = u P) :
    (∀ P : R, (descendComparison L hL C e c b g).hom.app (L.obj P) ≫ g.hom.app P =
      C.map (e.hom.app P) ≫ c.hom.app (H.obj P) ≫ b.hom.app P) ∧
    ∀ P : R, η.app (F.obj (L.obj P)) ≫
      (descendComparison L hL C e c b g).hom.app (L.obj P) ≫ g.hom.app P =
        e.hom.app P ≫ u (H.obj P) ≫ b.hom.app P := by
  let d : L ⋙ (F ⋙ C) ≅ T :=
    (Functor.associator L F C).symm ≪≫ Functor.isoWhiskerRight e C ≪≫
      Functor.associator H Q C ≪≫ Functor.isoWhiskerLeft H c ≪≫ b
  let α := descendComparison L hL C e c b g
  have hα : Functor.isoWhiskerLeft L α = d ≪≫ g.symm := by
    unfold α descendComparison
    exact hL.isoEquiv.apply_symm_apply _
  have hα' : Functor.isoWhiskerLeft L α ≪≫ g = d := by
    rw [hα]
    simp
  have hn (P : R) : α.hom.app (L.obj P) ≫ g.hom.app P =
      C.map (e.hom.app P) ≫ c.hom.app (H.obj P) ≫ b.hom.app P :=
    by
      have hh := congrArg (fun a ↦ a.hom.app P) hα'
      simpa only [d, Iso.trans_hom, NatTrans.comp_app,
        Iso.symm_hom, Functor.associator_inv_app, Functor.associator_hom_app,
        Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
        Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Category.id_comp, Category.comp_id] using hh
  refine ⟨hn, ?_⟩
  intro P
  exact unitComposite C η _ _ _ _ _ _ (hn P) (hu (H.obj P))

set_option genSizeOfSpec false in
set_option genInjectivity false in
private structure DescendedCompletion
    {R S A D : Type*} [Category* R] [Category* S] [Category* A] [Category* D]
    (L : R ⥤ S) {F G : S ⥤ D} {H : R ⥤ A} {Q V : A ⥤ D} {T : R ⥤ D}
    (C : D ⥤ D) (η : 𝟭 D ⟶ C)
    (e : L ⋙ F ≅ H ⋙ Q) (c : Q ⋙ C ≅ V) (b : H ⋙ V ≅ T) (g : L ⋙ G ≅ T)
    (u : ∀ P : A, Q.obj P ⟶ V.obj P) where
  comparison : F ⋙ C ≅ G
  normalization : ∀ P : R,
    comparison.hom.app (L.obj P) ≫ g.hom.app P =
      C.map (e.hom.app P) ≫ c.hom.app (H.obj P) ≫ b.hom.app P
  augmentation : ∀ P : R,
    η.app (F.obj (L.obj P)) ≫ comparison.hom.app (L.obj P) ≫ g.hom.app P =
      e.hom.app P ≫ u (H.obj P) ≫ b.hom.app P

private theorem descendCompletion_existsUnique
    {R S A D : Type*} [Category* R] [Category* S] [Category* A] [Category* D]
    (L : R ⥤ S) (hL : ((Functor.whiskeringLeft _ _ D).obj L).FullyFaithful)
    {F G : S ⥤ D} {H : R ⥤ A} {Q V : A ⥤ D} {T : R ⥤ D}
    (C : D ⥤ D) (η : 𝟭 D ⟶ C)
    (e : L ⋙ F ≅ H ⋙ Q) (c : Q ⋙ C ≅ V) (b : H ⋙ V ≅ T) (g : L ⋙ G ≅ T)
    (u : ∀ P : A, Q.obj P ⟶ V.obj P)
    (hu : ∀ P : A, η.app (Q.obj P) ≫ c.hom.app P = u P) :
    ∃! p : DescendedCompletion L C η e c b g u, True := by
  let α := descendComparison L hL C e c b g
  let hn := descentComparison_properties L hL C η e c b g u hu
  refine ⟨⟨α, hn.1, hn.2⟩, trivial, ?_⟩
  intro p _
  have hc : p.comparison = α := by
    apply Iso.ext
    apply hL.map_injective
    apply NatTrans.ext
    funext P
    change p.comparison.hom.app (L.obj P) = α.hom.app (L.obj P)
    apply (cancel_mono (g.hom.app P)).mp
    exact (p.normalization P).trans (hn.1 P).symm
  cases p with
  | mk comparison normalization augmentation =>
    dsimp only at hc
    cases hc
    rfl

@[irreducible] private def descendCompletion
    {R S A D : Type*} [Category* R] [Category* S] [Category* A] [Category* D]
    (L : R ⥤ S) (hL : ((Functor.whiskeringLeft _ _ D).obj L).FullyFaithful)
    {F G : S ⥤ D} {H : R ⥤ A} {Q V : A ⥤ D} {T : R ⥤ D}
    (C : D ⥤ D) (η : 𝟭 D ⟶ C)
    (e : L ⋙ F ≅ H ⋙ Q) (c : Q ⋙ C ≅ V) (b : H ⋙ V ≅ T) (g : L ⋙ G ≅ T)
    (u : ∀ P : A, Q.obj P ⟶ V.obj P)
    (hu : ∀ P : A, η.app (Q.obj P) ≫ c.hom.app P = u P) :
    DescendedCompletion L C η e c b g u :=
  (descendCompletion_existsUnique L hL C η e c b g u hu).exists.choose

@[irreducible] private def sourceWhisker (W : Scheme.{t})
    (D : Type a₁) [Category.{b₁} D] :
    (((Functor.whiskeringLeft _ _ D).obj
      (modelGoodLocalization l E W)).FullyFaithful) := by
  let V := (ambientQuasiIso l E W).inverseImage (ambientGood l E W).ι
  have hL : (modelGoodLocalization l E W).IsLocalization V := by
    exact (ambientPackage l E).goodLocalization W
  exact Localization.fullyFaithfulWhiskeringLeft (modelGoodLocalization l E W) V D

@[irreducible] private def sourceProdWhisker (W : Scheme.{t})
    (D : Type a₁) [Category.{b₁} D] :
    (((Functor.whiskeringLeft _ _ D).obj
      ((modelGoodLocalization l E W).prod (modelGoodLocalization l E W))).FullyFaithful) := by
  let V := (ambientQuasiIso l E W).inverseImage (ambientGood l E W).ι
  have hL : (modelGoodLocalization l E W).IsLocalization V := by
    exact (ambientPackage l E).goodLocalization W
  letI := hL
  haveI : V.ContainsIdentities := by
    refine ⟨fun P ↦ ?_⟩
    with_unfolding_all exact (quasiIso_of_isIso
      (𝟙 (show IntegralOnSlice.Cx l E W none from P.obj)))
  exact Localization.fullyFaithfulWhiskeringLeft
    ((modelGoodLocalization l E W).prod (modelGoodLocalization l E W)) (V.prod V) D

set_option genSizeOfSpec false in
set_option genInjectivity false in
private structure DerivedPresentation (X Y : Scheme.{t}) (f : X ⟶ Y) where
  F : ambientD l E Y ⥤
    ambientD l E X
  ε : modelQ l E Y ⋙ F ⟶ modelPullComplex l E f ⋙ modelQ l E X
  derived : F.IsLeftDerivedFunctor ε
    (ambientQuasiIso l E Y)
  good : ∀ P : (ambientGood l E Y).FullSubcategory,
    IsIso (ε.app P.obj)

@[irreducible] private def derivedPresentation {X Y : Scheme.{t}} (f : X ⟶ Y) :
    DerivedPresentation l E X Y f :=
  let h := modelDerivedData l E f
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.1,
    h.choose_spec.choose_spec.2⟩

@[irreducible] private def liftedTensorComparison
    {C D : Type*} [Category* C] [Category* D]
    (K P : ObjectProperty C) (k : ∀ X : P.FullSubcategory, K X.obj)
    (T : C × C ⥤ C) (Q : C ⥤ D) (S : D × D ⥤ D)
    (c : K.ι.prod K.ι ⋙ T ⋙ Q ≅ (K.ι ⋙ Q).prod (K.ι ⋙ Q) ⋙ S)
    (h : ∀ X : P.FullSubcategory × P.FullSubcategory,
      P ((P.ι.prod P.ι ⋙ T).obj X)) :
    (P.ι ⋙ Q).prod (P.ι ⋙ Q) ⋙ S ≅
      P.lift (P.ι.prod P.ι ⋙ T) h ⋙ (P.ι ⋙ Q) :=
  let M := K.lift P.ι k
  NatIso.ofComponents (fun X ↦ (c.app ((M.prod M).obj X)).symm)
    (fun f ↦ c.inv.naturality ((M.prod M).map f))

private theorem liftedTensorComparison_app
    {C D : Type*} [Category* C] [Category* D]
    (K P : ObjectProperty C) (k : ∀ X : P.FullSubcategory, K X.obj)
    (T : C × C ⥤ C) (Q : C ⥤ D) (S : D × D ⥤ D)
    (c : K.ι.prod K.ι ⋙ T ⋙ Q ≅ (K.ι ⋙ Q).prod (K.ι ⋙ Q) ⋙ S)
    (h : ∀ X : P.FullSubcategory × P.FullSubcategory,
      P ((P.ι.prod P.ι ⋙ T).obj X)) (X : P.FullSubcategory × P.FullSubcategory) :
    (liftedTensorComparison K P k T Q S c h).hom.app X =
      c.inv.app (⟨X.1.obj, k X.1⟩, ⟨X.2.obj, k X.2⟩) := by
  unfold liftedTensorComparison
  rfl

@[irreducible] private def globalTensorComparison (W : Scheme.{t}) :
    ((modelGoodLocalization l E W).prod
      (modelGoodLocalization l E W)) ⋙ modelOrdinaryTensor l E W ≅
        modelTensorGoodLift l E W ⋙ modelGoodLocalization l E W := by
  let K := ambientFlat l E W
  unfold modelTensorGoodLift modelGoodLocalization
  exact (liftedTensorComparison K (ambientGood l E W)
    (fun P ↦ ambientGoodFlat l E W P.obj P.property) (modelTotalTensor l E W) (modelQ l E W)
    (modelOrdinaryTensor l E W)
    (modelTensorModelComparison l E W)
    (fun P ↦ modelTensorGood l E W P.1.obj P.2.obj P.1.property P.2.property))

private theorem globalTensorComparison_app (W : Scheme.{t})
    (P Q : (ambientGood l E W).FullSubcategory) :
    (globalTensorComparison l E W).hom.app (P, Q) =
      (tensorRepresentative l E W P Q).inv := by
  unfold globalTensorComparison tensorRepresentative
  exact (liftedTensorComparison_app
    (ambientFlat l E W)
    (ambientGood l E W) (fun P ↦ ambientGoodFlat l E W P.obj P.property)
    (modelTotalTensor l E W) (modelQ l E W) (modelOrdinaryTensor l E W)
    (modelTensorModelComparison l E W)
    (fun P ↦ modelTensorGood l E W P.1.obj P.2.obj P.1.property P.2.property) (P, Q))

@[irreducible] private def liftedTowerRoosComparison
    {A B C T D : Type*} [Category* A] [Category* B] [Category* C]
    [Category* T] [Category* D]
    (P : ObjectProperty C) (H : A ⥤ B) (F : B ⥤ C)
    (h : ∀ X : A, P ((H ⋙ F).obj X))
    (U : C ⥤ T) (V : B ⥤ T) (R : T ⥤ C) (Q : C ⥤ D) (b : F ⋙ U ≅ V) :
    P.lift (H ⋙ F) h ⋙ (P.ι ⋙ (U ⋙ R) ⋙ Q) ≅ H ⋙ (V ⋙ R) ⋙ Q :=
  NatIso.ofComponents (fun X ↦ Q.mapIso (R.mapIso (b.app (H.obj X)))) (by
    intro X Y f
    dsimp [ObjectProperty.lift]
    simp only [← Functor.map_comp]
    have hb := b.hom.naturality (H.map f)
    simp only [Functor.comp_map] at hb
    exact congrArg (fun k ↦ Q.map (R.map k)) hb)

private theorem liftedTowerRoosComparison_app
    {A B C T D : Type*} [Category* A] [Category* B] [Category* C]
    [Category* T] [Category* D]
    (P : ObjectProperty C) (H : A ⥤ B) (F : B ⥤ C)
    (h : ∀ X : A, P ((H ⋙ F).obj X))
    (U : C ⥤ T) (V : B ⥤ T) (R : T ⥤ C) (Q : C ⥤ D) (b : F ⋙ U ≅ V) (X : A) :
    (liftedTowerRoosComparison P H F h U V R Q b).hom.app X =
      Q.map (R.map (b.hom.app (H.obj X))) := by
  unfold liftedTowerRoosComparison
  rfl

@[irreducible] private def globalTensorRoosComparison (W : Scheme.{t}) :
    modelTensorGoodLift l E W ⋙ modelCompletionOnGood l E W ≅
        modelTensorOnGood l E W :=
  liftedTowerRoosComparison (ambientGood l E W)
    ((ambientGood l E W).ι.prod (ambientGood l E W).ι)
    (modelTotalTensor l E W)
    (fun P ↦ modelTensorGood l E W P.1.obj P.2.obj P.1.property P.2.property)
    (modelQuotientTower l E W) (modelRecordedTensorTower l E W)
    (modelRoos l E W) (modelQ l E W) (modelTensorTowerIso l E W)

private theorem globalTensorRoosComparison_app (W : Scheme.{t})
    (P Q : (ambientGood l E W).FullSubcategory) :
    (globalTensorRoosComparison l E W).hom.app (P, Q) = modelTensorTowerMap l E W P.obj Q.obj := by
  unfold globalTensorRoosComparison modelTensorTowerMap
  exact (liftedTowerRoosComparison_app
    (ambientGood l E W)
    ((ambientGood l E W).ι.prod
      (ambientGood l E W).ι)
    (modelTotalTensor l E W)
    (fun P ↦ modelTensorGood l E W P.1.obj P.2.obj P.1.property P.2.property)
    (modelQuotientTower l E W) (modelRecordedTensorTower l E W)
    (modelRoos l E W) (modelQ l E W) (modelTensorTowerIso l E W) (P, Q))

@[irreducible] private def globalPullRoosComparison {X Y : Scheme.{t}} (f : X ⟶ Y) :
    modelPullGoodLift l E f ⋙ modelCompletionOnGood l E X ≅
          modelPullOnGood l E f :=
  liftedTowerRoosComparison (ambientGood l E X) (ambientGood l E Y).ι
    (modelPullComplex l E f) (fun P ↦ modelPullGood l E f P.obj P.property)
    (modelQuotientTower l E X) (modelRecordedPullTower l E f)
    (modelRoos l E X) (modelQ l E X) (modelPullTowerIso l E f)

private theorem globalPullRoosComparison_app {X Y : Scheme.{t}} (f : X ⟶ Y)
    (P : (ambientGood l E Y).FullSubcategory) :
    (globalPullRoosComparison l E f).hom.app P = modelPullTowerMap l E f P.obj := by
  unfold globalPullRoosComparison modelPullTowerMap
  exact liftedTowerRoosComparison_app (ambientGood l E X) (ambientGood l E Y).ι
    (modelPullComplex l E f) (fun P ↦ modelPullGood l E f P.obj P.property)
    (modelQuotientTower l E X) (modelRecordedPullTower l E f)
    (modelRoos l E X) (modelQ l E X) (modelPullTowerIso l E f) P

set_option maxHeartbeats 200000

/-- Completion of ordinary ambient pullback and tensor is precisely the recorded
finite-quotient integral pullback and completed tensor, naturally on all derived objects.
The equalities specify that these are the derived limits of modelPullTowerIso and
 modelTensorTowerIso, and identify both operation augmentations, including their zero
shifted-product coordinates recorded above.
Source: Stacks 06YY, 0G7E, 07A4, 0941; sites-modules.tex, 03EL
(blueprint: lem-pur-integral-ambient-operation-models).

Proof: present ordinary pullback by independent-universe algebraic inverse image
and scalar extension. Uniqueness of left adjoints identifies this presentation with
pull. Apply the ringed derived-pullback theorem and transport its universal counit
from homotopy representatives to cochains. The counit is invertible on good complexes.
On those representatives, compose its image under completion, completionComparison,
and the Roos image of modelPullTowerIso. Fully faithful whiskering along good localization
descends this comparison against modelPullComparison.
For tensor, restrict the specified ordinary tensor model to good complexes, invert
its comparison, and compose completionComparison with the Roos image of modelTensorTowerIso.
Fully faithful whiskering along the product localization descends this comparison
against modelTensorComparison. Evaluating the two descent equations gives
the stated normalizations. Finally, naturality of completionUnit and its defining
equation on good complexes identify both augmentations; functoriality of Q combines
the Roos unit with the strict tower map. No boundedness, completeness, or
constructibility condition is imposed. -/
theorem integralAmbientOperationModels {X Y : Scheme.{t}} (f : X ⟶ Y)
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    ∃ (F : ambientD l E Y ⥤
        ambientD l E X)
      (ε : modelQ l E Y ⋙ F ⟶ modelPullComplex l E f ⋙ modelQ l E X)
      (α : F ⋙ modelCompletion l E X ≅ modelPull l E f),
      F.IsLeftDerivedFunctor ε
        (ambientQuasiIso l E Y) ∧
      (∀ P : (ambientGood l E Y).FullSubcategory,
        IsIso (ε.app P.obj)) ∧
      (∀ P : (ambientGood l E Y).FullSubcategory,
        α.hom.app ((modelGoodLocalization l E Y).obj P) ≫
            (modelPullComparison l E f).hom.app P =
          (modelCompletion l E X).map (ε.app P.obj) ≫
            (modelCompletionComparison l E X).hom.app
              ((modelPullGoodLift l E f).obj P) ≫
            modelPullTowerMap l E f P.obj) ∧
      (∀ P : (ambientGood l E Y).FullSubcategory,
        (modelCompletionUnit l E X).app (F.obj ((modelGoodLocalization l E Y).obj P)) ≫
            α.hom.app ((modelGoodLocalization l E Y).obj P) ≫
            (modelPullComparison l E f).hom.app P =
          ε.app P.obj ≫ modelPullUnitMap l E f P.obj) ∧
      ∀ W : Scheme.{t}, W = X ∨ W = Y →
        ∃ β : (modelOrdinaryTensor l E W) ⋙
            modelCompletion l E W ≅ modelCompletedTensor l E W,
          (∀ P Q : (ambientGood l E W).FullSubcategory,
            β.hom.app
              (((modelGoodLocalization l E W).prod (modelGoodLocalization l E W)).obj (P, Q)) ≫
                (modelTensorComparison l E W).hom.app (P, Q) =
              (modelCompletion l E W).map
                (tensorRepresentative l E W P Q).inv ≫
              (modelCompletionComparison l E W).hom.app
                ((modelTensorGoodLift l E W).obj (P, Q)) ≫
              modelTensorTowerMap l E W P.obj Q.obj) ∧
          (∀ P Q : (ambientGood l E W).FullSubcategory,
            (modelCompletionUnit l E W).app
                ((modelOrdinaryTensor l E W).obj
                  (((modelGoodLocalization l E W).prod (modelGoodLocalization l E W)).obj (P, Q))) ≫
                β.hom.app
              (((modelGoodLocalization l E W).prod (modelGoodLocalization l E W)).obj (P, Q)) ≫
                (modelTensorComparison l E W).hom.app (P, Q) =
              (tensorRepresentative l E W P Q).inv ≫
                modelTensorUnitMap l E W P.obj Q.obj) := by
  classical
  let d := derivedPresentation l E f
  let H := modelPullGoodLift l E f
  let e : modelGoodLocalization l E Y ⋙ d.F ≅ H ⋙ modelGoodLocalization l E X :=
    NatIso.ofComponents (fun P ↦ @asIso _ _ _ _ (d.ε.app P.obj) (d.good P))
      (fun a ↦ d.ε.naturality a.hom)
  let ap := descendCompletion (modelGoodLocalization l E Y)
    (sourceWhisker l E Y (ambientD l E X))
    (modelCompletion l E X) (modelCompletionUnit l E X) e
    (modelCompletionComparison l E X) (globalPullRoosComparison l E f)
    (modelPullComparison l E f)
    (fun P ↦ (modelQ l E X).map (modelRoosUnit l E X P.obj))
    (modelCompletionUnit_app l E X)
  refine ⟨d.F, d.ε, ap.comparison, d.derived, d.good, ?_, ?_, ?_⟩
  · intro P
    have hp := ap.normalization P
    dsimp only [H, e, NatIso.ofComponents, asIso] at hp
    refine hp.trans ?_
    with_unfolding_all exact (congrArg (fun k ↦
      (modelCompletion l E X).map (d.ε.app P.obj) ≫
        (modelCompletionComparison l E X).hom.app ((modelPullGoodLift l E f).obj P) ≫ k)
      (globalPullRoosComparison_app l E f P))
  · intro P
    have hp := ap.augmentation P
    dsimp only [H, e, NatIso.ofComponents, asIso] at hp
    refine hp.trans ?_
    calc
      _ = d.ε.app P.obj ≫
          (modelQ l E X).map
            (modelRoosUnit l E X ((modelPullGoodLift l E f).obj P).obj) ≫
          modelPullTowerMap l E f P.obj := by
        with_unfolding_all exact (congrArg (fun k ↦ d.ε.app P.obj ≫
          (modelQ l E X).map
            (modelRoosUnit l E X ((modelPullGoodLift l E f).obj P).obj) ≫ k)
          (globalPullRoosComparison_app l E f P))
      _ = _ := by
        dsimp only [modelPullGoodLift, ObjectProperty.lift, Functor.comp_obj,
          ObjectProperty.ι_obj]
        with_unfolding_all exact (congrArg (fun k ↦ d.ε.app P.obj ≫ k)
          (ambientPullUnitMap_factor l E f P.obj))
  · intro W _
    let Ht := modelTensorGoodLift l E W
    let bp := descendCompletion
      ((modelGoodLocalization l E W).prod (modelGoodLocalization l E W))
      (sourceProdWhisker l E W (ambientD l E W))
      (modelCompletion l E W) (modelCompletionUnit l E W)
      (globalTensorComparison l E W) (modelCompletionComparison l E W)
      (globalTensorRoosComparison l E W) (modelTensorComparison l E W)
      (fun P ↦ (modelQ l E W).map (modelRoosUnit l E W P.obj))
      (modelCompletionUnit_app l E W)
    refine ⟨bp.comparison, ?_, ?_⟩
    · intro P Q
      have hp := bp.normalization (P, Q)
      refine hp.trans ?_
      with_unfolding_all exact (congrArg₂ (fun u v ↦ (modelCompletion l E W).map u ≫
        (modelCompletionComparison l E W).hom.app ((modelTensorGoodLift l E W).obj (P, Q)) ≫ v)
        (globalTensorComparison_app l E W P Q) (globalTensorRoosComparison_app l E W P Q))
    · intro P Q
      have hp := bp.augmentation (P, Q)
      refine hp.trans ?_
      calc
        _ = (tensorRepresentative l E W P Q).inv ≫
            (modelQ l E W).map
              (modelRoosUnit l E W ((modelTensorGoodLift l E W).obj (P, Q)).obj) ≫
            modelTensorTowerMap l E W P.obj Q.obj := by
          with_unfolding_all exact (congrArg₂ (fun u v ↦ u ≫
            (modelQ l E W).map
              (modelRoosUnit l E W ((modelTensorGoodLift l E W).obj (P, Q)).obj) ≫ v)
            (globalTensorComparison_app l E W P Q) (globalTensorRoosComparison_app l E W P Q))
        _ = _ := by
          dsimp only [modelTensorGoodLift, ObjectProperty.lift, Functor.comp_obj,
            Functor.prod_obj, ObjectProperty.ι_obj]
          with_unfolding_all exact (congrArg (fun k ↦ (tensorRepresentative l E W P Q).inv ≫ k)
            (ambientTensorUnitMap_factor l E W P.obj Q.obj))

end WeilConjectures.IntegralAmbient
