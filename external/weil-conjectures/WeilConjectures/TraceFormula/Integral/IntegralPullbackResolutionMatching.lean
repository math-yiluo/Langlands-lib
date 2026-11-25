/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Integral.IntegralPullbackComparisonRealization
public import WeilConjectures.TraceFormula.Integral.IntegralTowerInverseImageUnit
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
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
public import WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparisonDerived
public import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
import WeilConjectures.TraceFormula.Integral.IntegralPullbackReductionCounit

set_option linter.privateModule false

/-!
# The counit identity for the integral inverse-image comparison

Source: blueprint Global powers in
`sec-trace-formula/sk-thm-trace-transport/thm-trf-l-function-euler-product.proof.md`;
Stacks Project, Tags 0FND, 0DVC, 03CZ, 06YY and 0941
(blueprint: lem-trf-integral-pullback-resolution-matching).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures

private theorem counitIdentity_transport
    {A B C : Type*} [Category A] [Category B] [Category C]
    (H F : A ⥤ B) (L : B ⥤ C) (T : A ⥤ C)
    (γ : F ⋙ L ⟶ T) (β : H ⋙ L ⟶ T)
    {X Y : A} (r : X ≅ Y) (aX : H.obj X ⟶ F.obj X) (aY : H.obj Y ⟶ F.obj Y)
    (ha : H.map r.hom ≫ aY = aX ≫ F.map r.hom)
    (hX : L.map aX ≫ γ.app X = β.app X) :
    L.map aY ≫ γ.app Y = β.app Y := by
  apply (cancel_epi (L.map (H.map r.hom))).1
  calc
    _ = L.map (H.map r.hom ≫ aY) ≫ γ.app Y := by
      rw [Functor.map_comp, Category.assoc]
    _ = L.map (aX ≫ F.map r.hom) ≫ γ.app Y := by rw [ha]
    _ = L.map aX ≫ γ.app X ≫ T.map r.hom := by
      rw [Functor.map_comp, Category.assoc, ← γ.naturality]
      rfl
    _ = (H ⋙ L).map r.hom ≫ β.app Y := by
      rw [← Category.assoc, hX, β.naturality]
    _ = _ := rfl

private theorem chosenResolution_formula
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {W Z : Scheme.{u}} (h : Z ⟶ W) [IsIso h]
    (hW : ∀ w : W, IsUnit (l : W.presheaf.stalk w))
    (hZ : ∀ z : Z, IsUnit (l : Z.presheaf.stalk z))
    (M : DerivedCategory (integralTowerModules l E W)) :
    ∃ (K : CochainComplex (integralTowerModules l E W) ℤ)
      (eK : DerivedCategory.Q.obj K ≅ M)
      (P : (integralOperationsGoodComplex l E W).FullSubcategory)
      (q : P.obj ⟶ K) (hq : QuasiIso q),
      let := hq
      inverseImagePullbackComparisonDerived l E h hZ hW M =
        (inverseImageIntegralDerived l E h).map eK.inv ≫
        (inverseImageIntegralModules l E h).mapDerivedCategoryFactors.hom.app K ≫
        inv (DerivedCategory.Q.map
          (((inverseImageIntegralModules l E h).mapHomologicalComplex (.up ℤ)).map q)) ≫
        DerivedCategory.Q.map (inverseImageRoosComparisonComplex l E h P.obj) ≫
        (integralDerivedPullbackComparison l E h).inv.app P ≫
        (integralDerivedPullback l E h).map (DerivedCategory.Q.map q) ≫
        (integralDerivedPullback l E h).map eK.hom := by
  unfold inverseImagePullbackComparisonDerived
  extract_lets K e hp P q hq
  let P' : (integralOperationsGoodComplex.{u, u} l E W).FullSubcategory :=
    ⟨P, hq.1, fun i ↦ (exactFunctor _ _).prop_of_iso
      (@SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1}
        W.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} _)
        (ProEt.topology W) (completedIntegralCommRingSheafUnrestricted.{u, u} l E W)
        (P.X i)).symm (hq.2.1 i)⟩
  refine ⟨K, e, P', q, hq.2.2.1, ?_⟩
  simp only [inverseImagePullbackComparison, Category.assoc]
  rfl

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (D : IntegralComparisonSystem.{u} l)
  {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)

end WeilConjectures
