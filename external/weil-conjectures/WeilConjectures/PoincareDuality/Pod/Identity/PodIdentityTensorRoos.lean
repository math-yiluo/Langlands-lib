/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletedTensorReindex.PodCompletionTensorModels
import WeilConjectures.PoincareDuality.Pod.Identity.PodIdentityTensorTower
import WeilConjectures.PoincareDuality.Pod.Identity.PodIdentityRoosMap

/-! # Compatibility of normalized ordinary reindexing

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 03EL, 07A4 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.integralCompletedTensor WeilConjectures.sfIntegralConstructible
  WeilConjectures.podReindexCalculus WeilConjectures.coefficientSequenceRestriction

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] integralOperationsTensorTowerFunctor integralOperationsRoos
attribute [local implicit_reducible] integralOperationsTensorComplexFunctor

/-- The strict tensor-tower identity determines the identity on its whole Roos complex.
Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5
(blueprint: lem-pod-identity-tensor-roos).

Proof: the strict tensor-tower equation and functoriality identify the tower-map
part of the composite. Apply the proved generic Roos identity, using the two
coordinate formulas of the completion datum. This identifies the entire cochain
map, including its shifted coordinate. -/
theorem podIdentityTensorRoos
    (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
    (D : PodCompletionReindex l E (𝟙 W))
    (hg : PodCompletionReindex.QuotientGenerators l E (𝟙 W) D)
    (T : PodCompletedTensorReindex l E (𝟙 W) D)
    (ht : PodCompletedTensorReindex.Generators l E (𝟙 W) D T)
    (hf : PodCompletionReindex.RoosFst l E (𝟙 W) D)
    (hs : PodCompletionReindex.RoosSnd l E (𝟙 W) D)
    (a : isoReductionIntegralInverse l E (𝟙 W) ≅ 𝟭 _)
    (ha : ∀ (M : scalarReductionSource l E W) (U : W.ProEt)
      (x : M.val.obj (op ((proEtaleIsoPostcompose (𝟙 W)).obj U))),
      (a.hom.app M).val.app (op U) x =
        M.val.map ((MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ W
          (𝟙 W) rfl).hom.app U).op x)
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory) :
    let α := NatIso.mapHomologicalComplex a (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso _ (.up ℤ)
    (D.roos ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj))).hom ≫
      integralOperationsRoosFunctor.map (T.tower P Q).hom ≫
      (integralOperationsTensorComplexFunctor l E W).map
        (Prod.mkHom (α.hom.app P.obj) (α.hom.app Q.obj)) =
      α.hom.app ((integralOperationsTensorComplexFunctor l E W).obj (P.obj, Q.obj)) := by
  dsimp only
  have htower := podIdentityTensorTower l E W D hg T ht a ha P Q
  change (D.roos ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj))).hom ≫
    integralOperationsRoosFunctor.map (T.tower P Q).hom ≫
    integralOperationsRoosFunctor.map ((integralOperationsTensorTowerFunctor l E W).map
      (Prod.mkHom
        ((NatIso.mapHomologicalComplex a (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.app P.obj)
        ((NatIso.mapHomologicalComplex a (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.app Q.obj))) = _
  rw [← integralOperationsRoosFunctor.map_comp]
  have he := congrArg (fun v ↦ integralOperationsRoosFunctor.map v) htower
  rw [he]
  exact podIdentityRoosMap (isoReductionIntegralInverse l E (𝟙 W)) a
    ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj))
    (D.roos ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj))).hom (hf _) (hs _)

end WeilConjectures
