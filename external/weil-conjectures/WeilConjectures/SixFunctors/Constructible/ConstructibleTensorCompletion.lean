/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralDerivedOperations
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SixFunctors.Supporting.DerivedCompleteUnrestricted
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.BifunctorShift

import WeilConjectures.SixFunctors.ConstructibleTensorModel.ConstructibleTensorCompletionAssembly

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
/-!
# Ordinary tensor and completed tensor of constructible integral complexes

Source: Bhatt--Scholze, Lemma 6.5.5, pp. 49--50, Definition 3.4.10 and
Lemma 3.4.12(4), pp. 22--23 (blueprint: lem-fix-constructible-tensor-completion).
The existential tensor presentation retains its natural K-flat comparison, and the
completion comparison retains both coordinates of the actual product mapping fiber.
The index n denotes the positive exponent n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : AlgebraicGeometry.Scheme.{u})

/-- The existing small-model size at exactly the completed-coefficient universe.
Source: Stacks 098K (blueprint: lem-fix-constructible-tensor-completion). -/
instance (priority := 3100) constructibleTensorSiteSmall :
    EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0, u, u + 1} _

/-- The existing sheaf tensor on completed coefficients, with no completion applied.
Source: Stacks 03EK; Bhatt--Scholze Lemma 6.5.5
(blueprint: lem-fix-constructible-tensor-completion). -/
abbrev constructibleTensorOrdinary :=
  @MonoidalCategory.curriedTensor (integralTowerModules l E W) _
    (SheafOfModules.monoidalCategory (completedIntegralCommRingSheafUnrestricted l E W))

/-- Zero preservation of the existing tensor in its first argument.
Source: Stacks 03EK (blueprint: lem-fix-constructible-tensor-completion). -/
instance constructibleTensorZero :
    (constructibleTensorOrdinary l E W).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients.{u + 1, u, u + 1}
    (completedIntegralCommRingSheafUnrestricted l E W)

/-- Zero preservation of the existing tensor in its second argument.
Source: Stacks 03EK (blueprint: lem-fix-constructible-tensor-completion). -/
instance constructibleTensorObjZero (M : integralTowerModules l E W) :
    ((constructibleTensorOrdinary l E W).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients.{u + 1, u, u + 1}
    (completedIntegralCommRingSheafUnrestricted l E W) M

/-- Mathlib's signed direct-sum total tensor, specialized to the completed ring sheaf.
Source: Stacks 06YL (blueprint: lem-fix-constructible-tensor-completion). -/
abbrev constructibleTensorTotal :=
  Functor.uncurry.obj ((constructibleTensorOrdinary l E W).map₂CochainComplex)

/-- A homogeneous pure tensor in a direct-sum totalization summand.
Source: Stacks 03EK and 06YL (blueprint: lem-fix-constructible-tensor-completion). -/
def constructibleTensorTotalSection
    (P Q : CochainComplex (integralTowerModules l E W) ℤ)
    (p q : ℤ) (U : W.ProEtᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    (((constructibleTensorTotal l E W).obj (P, Q)).X (p + q)).val.obj U :=
  letI : MonoidalCategory (PresheafOfModules.{u + 1}
      (completedIntegralCoefficientSheafUnrestricted l E W).obj) :=
    PresheafOfModules.monoidalCategory
    (R := (completedIntegralCommRingSheafUnrestricted l E W).obj)
  (CochainComplex.ιMapBifunctor P Q (constructibleTensorOrdinary l E W)
    p q (p + q) rfl).val.app U
    ((SheafOfModules.tensorObjIsoSheafification
      (R := completedIntegralCommRingSheafUnrestricted l E W) (P.X p) (Q.X q)).inv.val.app U
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 (completedIntegralCoefficientSheafUnrestricted l E W).obj)).unit.app
          ((P.X p).val ⊗ (Q.X q).val)).app U
            (x ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E W).obj.obj U] y)))

/-- The boundary 1-s for the specified strict finite-tensor quotient tower.
Source: Bhatt--Scholze Definition 3.4.10
(blueprint: lem-fix-constructible-tensor-completion). -/
abbrev constructibleTensorBoundary
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :=
  towerTransitionEndomorphism
    (K := fun n ↦ (integralOperationsTensorLevel l E W n).obj (P, Q))
    (integralOperationsTowerStep
      ((integralOperationsTensorTowerFunctor l E W).obj (P, Q)))

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  IntegralOnSlice.abSheafify IntegralOnSlice.abLocallyBijective
attribute [-instance] IntegralAmbient.ambientCxCategory IntegralAmbient.ambientDCategory
attribute [local instance 3100] integralTowerHasDerivedCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local irreducible] IntegralOnSlice.duality IntegralOnSlice.roosUnit
  IntegralAmbient.tensorTowerIso IntegralAmbient.tensorOperationUnit

open ConstructibleTensorModel

set_option backward.isDefEq.respectTransparency true in
/-- The actual quotient-map completion comparison is invertible on constructible pairs;
the ordinary ambient tensor is derived complete. Both tensor presentation and comparison
are supplied, rather than assumed. The natural representative isomorphism identifies T
with the localization of signed total tensor on flat-term K-flat complexes. The chain
map chi has the coefficient quotient maps as its first product coordinates and zero
shifted coordinate, so it is the specified mapping-fiber map, not an arbitrary lift.
The natural transformation tau descends precisely chi using those comparisons.

Source: Bhatt--Scholze Lemma 6.5.5, pp. 49--50; Definition 3.4.10 and Lemma 3.4.12(4)
(blueprint: lem-fix-constructible-tensor-completion).

Proof:
1. Use the recorded ordinary tensor in IntegralOnSlice.duality. Restrict its natural
K-flat representative comparison to the flat-term K-flat complexes in the statement.
2. Compose the canonical Roos augmentation with the normalized strict tensor-tower
isomorphism of IntegralAmbient. Its product coordinates are the quotient maps on
pure tensors and its shifted coordinate is zero.
3. Whiskering by the product of the good-complex localizations is fully faithful.
Descend the whole-tower comparison to an isomorphism from completion of the ordinary
tensor to the specified completed tensor. Its augmentation equation identifies the
composite with the canonical completion unit with exactly the chain map in step 2.
4. Apply simultaneous projective chart refinement to the two constructible objects.
It supplies a finite qcqs open--closed tree and finite common projective charts on
every nonempty leaf. Their composite weakly etale arrows form a pro-etale cover:
they cover on points, have quasi-compact domains, and the index set is finite.
5. Apply projectiveTensorChartComplete on each chart, using its bounded sheaf models
and finite-free retracts. The canonical completion locality theorem detects global
completeness from these chart restrictions. Empty leaves use empty chart families.
6. The same locality theorem identifies completeness with invertibility of the
canonical unit. Composing it with the descended isomorphism from step 3 proves
invertibility of the specified completed-tensor comparison on constructible pairs. -/
theorem constructibleTensorCompletion [CompactSpace W] [QuasiSeparatedSpace W]
    [∀ w : W, Invertible (l : W.residueField w)] :
    ∃ (T : DerivedCategory (integralTowerModules l E W) ×
        DerivedCategory (integralTowerModules l E W) ⥤
          DerivedCategory (integralTowerModules l E W))
      (e : ((integralOperationsGoodComplex l E W).ι.prod
          (integralOperationsGoodComplex l E W).ι) ⋙ constructibleTensorTotal l E W ⋙
          DerivedCategory.Q ≅
        ((integralOperationsGoodLocalization l E W).prod
          (integralOperationsGoodLocalization l E W)) ⋙ T)
      (chi : constructibleTensorTotal l E W ⟶ integralOperationsTensorComplexFunctor l E W),
      (∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (p q : ℤ) (n : ℕ)
        (U : W.ProEtᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        (((chi.app (P, Q) ≫ CochainComplex.mappingCocone.fst
          (constructibleTensorBoundary l E W P Q) ≫
          Pi.π (fun n ↦ (integralOperationsTensorLevel l E W n).obj (P, Q)) n).f
            (p + q)).val.app U)
          (constructibleTensorTotalSection l E W P Q p q U x y) =
        integralOperationsTotalTensorSection l E W n P Q p q U
          (unrestrictedIntegralTensorSection l E W n (P.X p) U 1 x)
          (unrestrictedIntegralTensorSection l E W n (Q.X q) U 1 y)) ∧
      (∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (i j : ℤ)
        (h : i + -1 = j),
        (chi.app (P, Q)).f i ≫ (CochainComplex.mappingCocone.snd
          (constructibleTensorBoundary l E W P Q)).v i j h = 0) ∧
      ∃ tau : T ⟶ integralCompletedTensor l E W,
        (∀ (P Q : (integralOperationsGoodComplex l E W).FullSubcategory),
          e.hom.app (P, Q) ≫ tau.app (DerivedCategory.Q.obj P.obj,
              DerivedCategory.Q.obj Q.obj) ≫
            (integralCompletedTensorComparison l E W).hom.app (P, Q) =
          DerivedCategory.Q.map (chi.app (P.obj, Q.obj))) ∧
        ∀ M N : DerivedCategory (integralTowerModules l E W),
          sfIntegralConstructible l E W M → sfIntegralConstructible l E W N →
          IsDerivedCompleteUnrestricted l E W (T.obj (M, N)) ∧ IsIso (tau.app (M, N)) := by
  with_unfolding_all exact constructibleTensorCompletionNative l E W

end WeilConjectures
