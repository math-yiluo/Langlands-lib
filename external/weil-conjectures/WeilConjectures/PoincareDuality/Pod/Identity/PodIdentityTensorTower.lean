/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletedTensorReindex.PodCompletionTensorModels
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTensorLevelReduction
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTensorLevelTower
import WeilConjectures.PoincareDuality.Pod.Identity.PodIdentityTensorUnitSections
import WeilConjectures.PoincareDuality.Pod.Identity.PodIdentityTensorTowerInverseGenerators

/-! # Compatibility of normalized ordinary reindexing

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 03EL, 07A4 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
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

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] integralOperationsRoos
attribute [local implicit_reducible] integralOperationsTensorTowerFunctor
  integralOperationsTensorLevel integralOperationsTensorComposite podGoodReindex
  SheafOfModules.restrictScalars Functor.map₂HomologicalComplex
  Functor.ofOpSequence Functor.ofSequence
attribute [local implicit_reducible] isoSectionwiseModuleInverseImage
  SheafOfModules.pushforward PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀ PresheafOfModules.pushforward₀Obj
  PresheafOfModules.restrictScalars PresheafOfModules.restrictScalarsObj
  ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'

attribute [local irreducible] integralOperationsTotalTensorSection
  unrestrictedIntegralTensorSection

-- Comparing sheafified total-tensor generators requires substantial instance elaboration.
/-- Identity relabelling agrees with the strict completed-tensor construction.
Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 07A4 and 0941 (blueprint: lem-pod-identity-tensor-tower).

Proof: the quotient-generator equation identifies the identity quotient comparison
with scalar reduction of the ordinary identity relabelling. Apply Generators to
all homogeneous pure tensors. These generate the direct-sum total tensor before
sheafification, so the tower map followed by the tensor of the two ordinary
relabellings equals the ordinary identity on each strict quotient. The equations
retain every transition. Equality of these whole strict tower maps follows from
extensionality in the quotient index and degree. No Roos realization, localization,
finite derived evaluation faithfulness or choice of resolutions is used. -/
theorem podIdentityTensorTower
    (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
    (D : PodCompletionReindex l E (𝟙 W))
    (hD : PodCompletionReindex.QuotientGenerators l E (𝟙 W) D)
    (T : PodCompletedTensorReindex l E (𝟙 W) D)
    (hT : PodCompletedTensorReindex.Generators l E (𝟙 W) D T)
    (a : isoReductionIntegralInverse l E (𝟙 W) ≅ 𝟭 _)
    (ha : ∀ (M : scalarReductionSource l E W) (U : W.ProEt)
      (x : M.val.obj (op ((proEtaleIsoPostcompose (𝟙 W)).obj U))),
      (a.hom.app M).val.app (op U) x =
        M.val.map ((MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ W
          (𝟙 W) rfl).hom.app U).op x)
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory) :
    let α := NatIso.mapHomologicalComplex a (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso _ (.up ℤ)
    (T.tower P Q).hom ≫ (integralOperationsTensorTowerFunctor l E W).map
        (Prod.mkHom (α.hom.app P.obj) (α.hom.app Q.obj)) =
      (isoWhiskerLeft ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj)) α ≪≫
        ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj)).rightUnitor).hom :=
  by
  let α := NatIso.mapHomologicalComplex a (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ (.up ℤ)
  have hα (K : CochainComplex (scalarReductionSource l E W) ℤ) (i : ℤ) :
      (α.hom.app K).f i = a.hom.app (K.X i) := by
    change a.hom.app (K.X i) ≫ 𝟙 _ = _
    exact Category.comp_id _
  have hτ (n : ℕᵒᵖ) :
      ((isoWhiskerLeft ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj))
          α ≪≫ ((integralOperationsTensorTowerFunctor l E W).obj
            (P.obj, Q.obj)).rightUnitor).hom.app n) =
        α.hom.app ((integralOperationsTensorLevel l E W n.unop).obj (P.obj, Q.obj)) := by
    simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
      whiskerLeft_app, rightUnitor_hom_app]
    exact Category.comp_id _
  have hmap (n : ℕᵒᵖ) :
      ((integralOperationsTensorTowerFunctor l E W).map
        (Prod.mkHom (α.hom.app P.obj) (α.hom.app Q.obj))).app n =
      (integralOperationsTensorLevel l E W n.unop).map
        (Prod.mkHom (α.hom.app P.obj) (α.hom.app Q.obj)) := rfl
  let P' := ((podGoodReindex l E (𝟙 W) D).obj P).obj
  let Q' := ((podGoodReindex l E (𝟙 W) D).obj Q).obj
  dsimp only
  apply (cancel_epi (T.tower P Q).inv).mp
  rw [Iso.inv_hom_id_assoc]
  apply NatTrans.ext
  funext n
  simp only [NatTrans.comp_app]
  refine (hmap n).trans ?_
  refine Eq.trans ?_
    (congrArg (fun f ↦ (T.tower P Q).inv.app n ≫ f) (hτ n)).symm
  apply HomologicalComplex.hom_ext
  intro k
  rw [HomologicalComplex.comp_f, hα]
  apply finite_tensor_ext l E W n.unop P' Q' k _ _ _
  intro p q hpq U x y
  subst k
  simp only [eqToHom_refl, SheafOfModules.id_val, PresheafOfModules.id_app,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply,
    ModuleCat.id_apply]
  rw [podIdentityTensorTowerInverseGenerators l E W D hD T hT P Q
    n.unop p q U x y]
  refine (finite_tensor_map_section l E W n.unop
    (α.hom.app P.obj) (α.hom.app Q.obj) p q U
    (unrestrictedIntegralTensorSection l E W n.unop _ U 1 x)
    (unrestrictedIntegralTensorSection l E W n.unop _ U 1 y)).trans ?_
  refine (congrArg₂ (fun s t ↦ integralOperationsTotalTensorSection l E W n.unop
    P.obj Q.obj p q U s t)
    (finite_reduction_map_section l E W n.unop ((α.hom.app P.obj).f p) U x)
    (finite_reduction_map_section l E W n.unop ((α.hom.app Q.obj).f q) U y)).trans ?_
  refine (congrArg₂ (fun s t ↦ integralOperationsTotalTensorSection l E W n.unop
    P.obj Q.obj p q U
    (unrestrictedIntegralTensorSection l E W n.unop (P.obj.X p) U 1 s)
    (unrestrictedIntegralTensorSection l E W n.unop (Q.obj.X q) U 1 t))
    ((congrArg (fun g : P'.X p ⟶ P.obj.X p ↦ g.val.app U x) (hα P.obj p)).trans
      (ha (P.obj.X p) U.unop x))
    ((congrArg (fun g : Q'.X q ⟶ Q.obj.X q ↦ g.val.app U y) (hα Q.obj q)).trans
      (ha (Q.obj.X q) U.unop y))).trans ?_
  exact (podIdentityTensorUnitSections l E W n.unop P.obj Q.obj p q U.unop a ha x y).symm

end WeilConjectures
