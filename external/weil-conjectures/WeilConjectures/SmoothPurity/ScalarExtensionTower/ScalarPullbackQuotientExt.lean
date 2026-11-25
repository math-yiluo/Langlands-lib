/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarPullbackRoosCoordinates
import all WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement

/-! # Uniqueness of strict scalar/pullback quotient comparisons

Source: Stacks 03D3, 06YY and 07A4. Three ordinary adjunctions detect strict
comparison maps on their nested tensor-unit generators.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] integralOrdinaryScalar integralOrdinaryTensorSection
  integralCompletedScalarMap completedIntegralCoefficientSheafUnrestricted
  HasDerivedCategory.standard unrestrictedIntegralReductionFunctor
  completedIntegralCommRingProjectionUnrestricted scalarReductionExistence
  AlgebraicGeometry.Scheme.coefficientProEtaleModuleAdjunction
  AlgebraicGeometry.Scheme.coefficientProEtaleModulePullback Functor.leftAdjoint

private theorem scalarTranspose_apply (Y : Scheme.{u})
    (M : integralTowerModules l E Y) (N : integralTowerModules l L Y)
    (a : (integralOrdinaryScalar l E L ι Y).obj M ⟶ N)
    (U : Y.ProEtᵒᵖ) (x : M.val.obj U) :
    (((scalarAdjunction l E L ι Y).homEquiv M N) a).val.app U x =
      a.val.app U (integralOrdinaryTensorSection l E L ι Y M U 1 x) := by
  rw [Adjunction.homEquiv_unit]
  change a.val.app U (((scalarAdjunction l E L ι Y).unit.app M).val.app U x) = _
  rw [scalarAdjunction_unit]

private noncomputable def quotientAdjunction (Y : Scheme.{u}) (n : ℕ) :=
  (CochainPullback.extensionAdjunction
    (completedIntegralCommRingProjectionUnrestricted l L Y n)).ofNatIsoLeft
      (tensorPresentation (completedIntegralCommRingProjectionUnrestricted l L Y n)
        (unrestrictedIntegralReductionFunctor l L Y n) (unrestrictedReduction_obj l L Y n)
        (unrestrictedReduction_map l L Y n)).symm

private theorem quotientTranspose_apply (Y : Scheme.{u}) (n : ℕ)
    (M : integralTowerModules l L Y) (N : integralOperationsFiniteModules l L Y n)
    (a : (unrestrictedIntegralReductionFunctor l L Y n).obj M ⟶ N)
    (U : Y.ProEtᵒᵖ) (x : M.val.obj U) :
    (((quotientAdjunction l L Y n).homEquiv M N) a).val.app U x =
      a.val.app U (unrestrictedIntegralTensorSection l L Y n M U 1 x) := by
  rw [Adjunction.homEquiv_unit]
  change a.val.app U (((quotientAdjunction l L Y n).unit.app M).val.app U x) = _
  have hu := tensorAdjunction_unit
    (completedIntegralCommRingProjectionUnrestricted l L Y n)
    (unrestrictedIntegralReductionFunctor l L Y n) (unrestrictedReduction_obj l L Y n)
    (unrestrictedReduction_map l L Y n) M U x
  have ht : tensorSection (completedIntegralCommRingProjectionUnrestricted l L Y n)
      (unrestrictedIntegralReductionFunctor l L Y n) (unrestrictedReduction_obj l L Y n)
      M U 1 x = unrestrictedIntegralTensorSection l L Y n M U 1 x := by
    with_unfolding_all rfl
  dsimp only [quotientAdjunction]
  exact congrArg (fun y ↦ a.val.app U y) (hu.trans ht)

private theorem pulledScalarGenerators_ext {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : integralTowerModules l E Y) (N : integralOperationsFiniteModules l L X n)
    (a b : (SheafOfModules.restrictScalars (integralOperationsProjection l L X n)).obj
        ((integralOperationsLevelPullback l L f n).obj
          ((unrestrictedIntegralReductionFunctor l L Y n).obj
            ((integralOrdinaryScalar l E L ι Y).obj M))) ⟶
      (SheafOfModules.restrictScalars (integralOperationsProjection l L X n)).obj N)
    (hab : ∀ (U : Y.ProEt) (x : M.val.obj (op U)),
      a.val.app (op ((Scheme.proEtaleBaseChange f).obj U))
          (integralOperationsPullbackGenerator l L f n _ U
            (unrestrictedIntegralTensorSection l L Y n
              ((integralOrdinaryScalar l E L ι Y).obj M) (op U) 1
              (integralOrdinaryTensorSection l E L ι Y M (op U) 1 x))) =
      b.val.app (op ((Scheme.proEtaleBaseChange f).obj U))
          (integralOperationsPullbackGenerator l L f n _ U
            (unrestrictedIntegralTensorSection l L Y n
              ((integralOrdinaryScalar l E L ι Y).obj M) (op U) 1
              (integralOrdinaryTensorSection l E L ι Y M (op U) 1 x)))) : a = b := by
  let π := integralOperationsProjection l L X n
  let V := (integralOperationsLevelPullback l L f n).obj
    ((unrestrictedIntegralReductionFunctor l L Y n).obj
      ((integralOrdinaryScalar l E L ι Y).obj M))
  let : Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) π.hom :=
    completedProjection_locallySurjective l L X n
  let lift := SheafOfModules.IntegralScalarProof.liftMap π π (𝟙 _) (Category.comp_id π) V N
  apply liftMap_injective π π (𝟙 _) (Category.comp_id π) V N
  apply ((integralOperationsPullbackAdjunction l L f n).homEquiv _ _).injective
  apply ((quotientAdjunction l L Y n).homEquiv _ _).injective
  apply ((scalarAdjunction l E L ι Y).homEquiv _ _).injective
  ext U x
  simp only [scalarTranspose_apply, quotientTranspose_apply]
  change a.val.app _ _ = b.val.app _ _
  exact hab U.unop x

/-- Nested tensor-unit pullback generators determine the strict tower comparison.
Source: Stacks 03D3, 06YY, 07A4; the generator comparison in step 2 of
stage3-pur-scalar-pullback-left-roos.
(blueprint: lem-pur-scalar-pullback-quotient-ext).

Proof: compare q inverse followed by q' with the identity, degreewise and at each
level n. By the inverse-image adjunction it suffices to compare maps on the pullback
unit sections. Ordinary scalar extension and finite quotient extension are generated
locally by pure tensors; their balancing relations reduce these sections to scalar
multiples of the nested unit sections in the hypothesis. Completed-to-finite scalar
projection is locally surjective, so a completed-linear map of these finite modules
is already finite-linear. The two maps therefore coincide on every section after
sheafification. Equality at each degree gives chain-map equality; equality at all
levels gives equality of natural transformations, and then of isomorphisms. All
quotient transitions are retained. Zero complexes, empty schemes, n=0 and ramified
coefficient embeddings require no extra hypothesis. -/
theorem scalarPullbackQuotient_ext {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex.{u, u} l E Y).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules.{u, u} l E Y) ℤ)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E Y n).obj P.obj)
    (q :
    (((coefficientSequenceRestriction.{u, u} l L X).mapHomologicalComplex (.up ℤ)).obj
      ((((integralComparisonSequencePullback.{u, u} l L f).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel.{u, u} l E L ι Y).E.mapHomologicalComplex
          (.up ℤ)).obj C)))).asFunctor ≅
      (integralOperationsPullbackTowerFunctor.{u, u} l L f).obj
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P.obj))
    (q' :
    (((coefficientSequenceRestriction.{u, u} l L X).mapHomologicalComplex (.up ℤ)).obj
      ((((integralComparisonSequencePullback.{u, u} l L f).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel.{u, u} l E L ι Y).E.mapHomologicalComplex
          (.up ℤ)).obj C)))).asFunctor ≅
      (integralOperationsPullbackTowerFunctor.{u, u} l L f).obj
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P.obj))
    (hq : ScalarPullbackQuotientFormula l E L ι f P C κ q)
    (hq' : ScalarPullbackQuotientFormula l E L ι f P C κ q') : q = q' := by
  have he : q.inv ≫ q'.hom = 𝟙 _ := by
    apply NatTrans.ext
    funext n
    apply HomologicalComplex.hom_ext
    intro i
    apply pulledScalarGenerators_ext l E L ι f n.unop (P.obj.X i)
    intro U x
    let s := integralComparisonRestrictedSection l L X
      ((integralComparisonSequencePullback l L f).obj
        ((integralComparisonSequenceScalarModel l E L ι Y).E.obj (C.X i))) n.unop
      (op ((Scheme.proEtaleBaseChange f).obj U))
      (integralComparisonSequenceGenerator l L f
        ((integralComparisonSequenceScalarModel l E L ι Y).E.obj (C.X i)) n.unop U
        (integralComparisonSequenceTensorSection l E L ι Y (C.X i) (op (n.unop, U)) 1
          (integralComparisonSequenceSection l E Y (C.X i) n.unop (op U)
            (((κ n.unop).inv.f i).val.app (op U)
              (unrestrictedIntegralTensorSection l E Y n.unop (P.obj.X i) (op U) 1 x)))))
    let v := integralOperationsPullbackGenerator l L f n.unop _ U
      (unrestrictedIntegralTensorSection l L Y n.unop
        ((integralOrdinaryScalar l E L ι Y).obj (P.obj.X i)) (op U) 1
        (integralOrdinaryTensorSection l E L ι Y (P.obj.X i) (op U) 1 x))
    have hi : ((q.inv.app n).f i).val.app _ v = s := by
      have h := congrArg (fun k ↦ ((k.app n).f i).val.app
        (op ((Scheme.proEtaleBaseChange f).obj U)) s) q.hom_inv_id
      change ((q.inv.app n).f i).val.app _ (((q.hom.app n).f i).val.app _ s) = s at h
      have hqv : ((q.hom.app n).f i).val.app _ s = v := hq n.unop i U x
      rw [hqv] at h
      exact h
    change ((q'.hom.app n).f i).val.app _ (((q.inv.app n).f i).val.app _ v) = v
    rw [hi]
    exact hq' n.unop i U x
  apply Iso.ext
  have h := congrArg (q.hom ≫ ·) he
  simpa only [← Category.assoc, q.hom_inv_id, Category.id_comp, Category.comp_id] using h.symm

end WeilConjectures.ScalarExtensionTower
