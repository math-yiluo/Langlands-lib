/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralScalarOperations.IntegralOperationsScalarExtension
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement

import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
import all WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeData
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # The normalized ordinary scalar tensor chain comparison

Source: Stacks 03EL and 07A4
(blueprint: lem-weil-normalized-ordinary-scalar-tensor-chain).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  coefficientTotalTensor integralOrdinaryTensorSection integralCompletedScalarMap
  integralOrdinaryScalar completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted
attribute [-instance] scalarReductionSourceDerived scalarReductionTargetDerived
attribute [-instance] integralOperationsSiteSmall
attribute [local instance 3000] integralTowerHasDerivedCategory
attribute [local instance 50000] hasSheafCompose_of_preservesLimitsOfSize

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    EssentiallySmall.{u+1} W.ProEt := essentiallySmallSelf.{0, u, u+1} _

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology
  integralOperationsAbSheafify integralOperationsAbLocallyBijective
  integralOperationsCommHasDerivedCategory
  SheafOfModules.cochainModulesMonoidal SheafOfModules.cochainModulesSymmetric
  SheafOfModules.cochainModulesPreadditive

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{u+1} :=
  integralCoefficientAbSheafify.{u, u} W

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    (AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
      AddCommGrpCat.{u+1} := integralCoefficientAbLocallyBijective.{u, u} W

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The ordinary total tensor comparison, uniquely fixed on pure scalar generators.
Source: Stacks, Modules on Sites, Tag 03EL, tensor-product section; Tag 07A4.
(blueprint: lem-weil-normalized-ordinary-scalar-tensor-chain).
Proof: identify the ordinary scalar functor with the recorded sheaf change-of-rings
functor by its object and morphism formulas. Apply the existing normalized complex
tensor comparison. The sheafification adjunction unit identifies its scalar
sections with the prescribed ordinary tensor sections, proving normalization.
For uniqueness, apply the scalar-extension adjunction in each degree. Equality
of the two adjoint maps follows on all pure bidegree generators from the two
normalization formulas; total tensor generation gives equality in every degree.
Chain-map, natural-transformation, and isomorphism extensionality finish. -/
theorem normalizedIntegralOrdinaryTensorChain (W : AlgebraicGeometry.Scheme.{u}) :
    ∃! α : coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) ⋙
          (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).prod
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
          coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l L W),
      ∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (p q : ℤ)
        (U : W.ProEtᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((α.hom.app (P, Q)).f (p + q)).val.app U
          (integralOrdinaryTensorSection l E L ι W
            (((coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
              (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)).X (p + q)) U 1
            (coefficientTensorGenerator.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
              (completedIntegralCommRingSheafUnrestricted l E W) P Q p q (p + q) rfl U x y)) =
        coefficientTensorGenerator.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l L W)
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q) p q (p + q) rfl U
          (integralOrdinaryTensorSection l E L ι W (P.X p) U 1 x)
          (integralOrdinaryTensorSection l E L ι W (Q.X q) U 1 y) := by
  let J := AlgebraicGeometry.Scheme.ProEt.topology W
  let R := completedIntegralCommRingSheafUnrestricted l E W
  let S := completedIntegralCommRingSheafUnrestricted l L W
  let φ := integralCompletedScalarMap l E L ι W
  let F := integralOrdinaryScalar l E L ι W
  have hobj : ∀ M, F.obj M = SheafOfModules.changeOfRings φ M :=
    integralOrdinaryScalar_obj l E L ι W
  have hmap : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (hobj M) ≫
      SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (hobj N).symm := by
    intro M N f
    exact integralOrdinaryScalar_map l E L ι W f
  have hsection (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ)
      (x : M.val.obj U) : tensorSection φ F hobj M U 1 x =
        integralOrdinaryTensorSection l E L ι W M U 1 x := by
    unfold tensorSection integralOrdinaryTensorSection
    with_unfolding_all rfl
  obtain ⟨D⟩ := SheafOfModules.nonempty_derivedChangeOfRingsCochainModel.{u + 1, u, u + 1,
      u + 2, u + 2} φ
  rcases D with @⟨G, hG, hmG, haG, hpG, T, hT, ε, hu, ht, hc⟩
  have he : G = F := by
    refine CategoryTheory.Functor.ext (F := G) (G := F)
      (fun M ↦ (hG M).trans (hobj M).symm) ?_
    intro M N f
    rw [hmG, hmap]
    simp
  subst G
  let D : SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1,
      u + 2, u + 2} φ :=
    { E := F, obj_eq := hG, map_eq := hmG, additive := haG, preserves := hpG,
      T := T, pointwise := hT, ε := ε, universal := hu, triangulated := ht, computes := hc }
  obtain ⟨κ, hκ, _⟩ := ringedFiniteFreeHomBaseChange_complex.{u + 1, u, u, u + 2} J φ D
  have hs (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ)
      (x : M.val.obj U) :
      ringedFiniteFreeScalarSection.{u + 1, u, u} J φ D.E D.obj_eq M U 1 x =
        integralOrdinaryTensorSection l E L ι W M U 1 x := by
    unfold ringedFiniteFreeScalarSection integralOrdinaryTensorSection
    have hη :=
      PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app.{u + 1, u,
        u + 1, u + 1} (J := J)
        (𝟙 (SheafOfModules.derivedChangeRingIndependentCoefficients J S).obj)
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M)
    with_unfolding_all exact (congrArg ((eqToHom (D.obj_eq M).symm).val.app U)
      (ConcreteCategory.congr_hom (congr_app hη U) _))
  have hnorm : ∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (p q : ℤ)
        (U : W.ProEtᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((κ.hom.app (P, Q)).f (p + q)).val.app U
          (integralOrdinaryTensorSection l E L ι W
            (((coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
              (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)).X (p + q)) U 1
            (coefficientTensorGenerator.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
              (completedIntegralCommRingSheafUnrestricted l E W) P Q p q (p + q) rfl U x y)) =
        coefficientTensorGenerator.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l L W)
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q) p q (p + q) rfl U
          (integralOrdinaryTensorSection l E L ι W (P.X p) U 1 x)
          (integralOrdinaryTensorSection l E L ι W (Q.X q) U 1 y) := by
    intro P Q p q U x y
    simpa only [hs] using hκ P Q p q U x y
  refine ⟨κ, hnorm, ?_⟩
  intro β hβ
  apply Iso.ext
  apply NatTrans.ext
  funext PQ
  rcases PQ with ⟨P, Q⟩
  apply HomologicalComplex.hom_ext
  intro n
  apply tensorSection_ext φ F hobj
  intro U z
  let adj := (CategoryTheory.CochainPullback.extensionAdjunction φ).ofNatIsoLeft
    (tensorPresentation φ F hobj hmap).symm
  have hh : adj.unit.app (((coefficientTotalTensor.{u, u + 1, u} J R).obj (P, Q)).X n) ≫
        (CategoryTheory.CochainPullback.restrictionFunctor φ).map
          ((β.hom.app (P, Q)).f n) =
      adj.unit.app (((coefficientTotalTensor.{u, u + 1, u} J R).obj (P, Q)).X n) ≫
        (CategoryTheory.CochainPullback.restrictionFunctor φ).map
          ((κ.hom.app (P, Q)).f n) := by
    apply CategoryTheory.ScalarHomTensor.total_pure_hom_ext.{u + 1, u, u} P Q n
    intro p q hpq V x y
    subst n
    change ((β.hom.app (P, Q)).f (p + q)).val.app V
        ((adj.unit.app _).val.app V
          (coefficientTensorGenerator.{u, u + 1, u} J R P Q p q (p + q) rfl V x y)) =
      ((κ.hom.app (P, Q)).f (p + q)).val.app V
        ((adj.unit.app _).val.app V
          (coefficientTensorGenerator.{u, u + 1, u} J R P Q p q (p + q) rfl V x y))
    simp only [adj, tensorAdjunction_unit φ F hobj hmap]
    simpa only [hsection, J, R] using
      (hβ P Q p q V x y).trans (hnorm P Q p q V x y).symm
  have hh' := congrArg (fun f ↦ f.val.app U z) hh
  change ((β.hom.app (P, Q)).f n).val.app U ((adj.unit.app _).val.app U z) =
    ((κ.hom.app (P, Q)).f n).val.app U ((adj.unit.app _).val.app U z) at hh'
  simp only [adj, tensorAdjunction_unit φ F hobj hmap] at hh'
  exact hh'

end WeilConjectures
