/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorConstruction
import WeilConjectures.SmoothPurity.Coefficient.CoefficientTotalTensorMapGenerators
import WeilConjectures.SmoothPurity.ProEtale.ProEtaleTotalTensorPullbackGenerators

/-! # The explicit intrinsic total pullback tensor isomorphism

Source: Stacks Tags 03EL, 06YY and 07A4.
(blueprint: lem-pur-finite-pullback-tensor-chain-generators).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open MonoidalCategory TensorProduct
namespace WeilConjectures
attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  Functor.mapDerivedCategory finitePullbackTensorConstruction
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] SheafOfModules.monoidalCategory
  proEtaleTensorPullbackTotalIso CategoryTheory.Functor.mapBifunctorHomologicalComplex
  HomologicalComplex₂.total
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
attribute [local instance] sfIntrinsicPullback_additive
  pullbackTensorCoefficientFinite
  SheafOfModules.monoidalCategory

/-- The signed-total ordinary comparison conjugated by the prescribed finite realization.
Source: Stacks 03EL and 07A4
(blueprint: lem-pur-finite-pullback-tensor-chain-generators). -/
@[irreducible] def finitePullbackTensorChainIso {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P Q : CochainComplex (normalizedDVRModules l E Y n) ℤ) :
    ((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex
      (.up ℤ)).obj
        ((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology Y)
          (integralCoefficientCommRingSheaf l E Y n)).obj (P, Q)) ≅
      (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n)).obj
          (((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex
            (.up ℤ)).obj P,
           ((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex
            (.up ℤ)).obj Q) := by
  letI : (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).Additive :=
    sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
  let e := NatIso.mapHomologicalComplex (pullbackTensorFiniteRealization l E f n) (.up ℤ)
  exact (e.app ((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology Y)
      (integralCoefficientCommRingSheaf l E Y n)).obj (P, Q))).symm ≪≫
    (proEtaleTensorPullbackTotalIso f
      (integralCoefficientCommRingSheaf l E Y n)
      (integralCoefficientCommRingSheaf l E X n)
      (pullbackTensorCoefficientIso l E f n) P Q).symm ≪≫
    (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
      (integralCoefficientCommRingSheaf l E X n)).mapIso
        (Iso.prod (e.app P) (e.app Q))

/-- The explicit chain comparison preserves intrinsic inverse-image unit generators.
Source: Stacks 03EL and 07A4
(blueprint: lem-pur-finite-pullback-tensor-chain-generators).
Proof: move the source unit through the inverse unit-normalized realization. The
ordinary signed-total comparison sends that ordinary unit generator to the tensor
of the two ordinary units. The total tensor map applies the realization in each
factor, and its two unit equations give the two intrinsic unit sections. -/
theorem finitePullbackTensorChain_generators {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P Q : CochainComplex (normalizedDVRModules l E Y n) ℤ) :
    ∀ (p q i : ℤ) (hpq : p + q = i) (U : Y.ProEt)
    (x : (P.X p).val.obj (op U)) (y : (Q.X q).val.obj (op U)),
    ((finitePullbackTensorChainIso l E f n P Q).hom.f i).val.app (op ((proEtaleBaseChange f).obj U))
      (((sfIntrinsicConstantModuleAdjunction f
        (finiteCoefficientRing l E (n + 1))).unit.app
          (((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology Y)
            (integralCoefficientCommRingSheaf l E Y n)).obj (P, Q)).X i)).val.app (op U)
        (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y)
          (integralCoefficientCommRingSheaf l E Y n) P Q p q i hpq (op U) x y)) =
    coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
      (integralCoefficientCommRingSheaf l E X n)
      (((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex
        (.up ℤ)).obj P)
      (((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex
        (.up ℤ)).obj Q) p q i hpq
      (op ((proEtaleBaseChange f).obj U))
      (((sfIntrinsicConstantModuleAdjunction f
        (finiteCoefficientRing l E (n + 1))).unit.app (P.X p)).val.app (op U) x)
      (((sfIntrinsicConstantModuleAdjunction f
        (finiteCoefficientRing l E (n + 1))).unit.app (Q.X q)).val.app (op U) y) := by
  let R := integralCoefficientCommRingSheaf l E Y n
  let S := integralCoefficientCommRingSheaf l E X n
  let c := pullbackTensorCoefficientIso l E f n
  let L := proEtaleRingModulePullback f R S c
  let F := sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f
  let e := pullbackTensorFiniteRealization l E f n
  let : F.Additive := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients S
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients S
  let eC := NatIso.mapHomologicalComplex e (.up ℤ)
  let FP := (F.mapHomologicalComplex (.up ℤ)).obj P
  let FQ := (F.mapHomologicalComplex (.up ℤ)).obj Q
  let LP := (L.mapHomologicalComplex (.up ℤ)).obj P
  let LQ := (L.mapHomologicalComplex (.up ℤ)).obj Q
  let T := coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X) S
  have hu (M : normalizedDVRModules l E Y n) (U : Y.ProEt)
      (x : M.val.obj (op U)) :
      (e.hom.app M).val.app (op ((proEtaleBaseChange f).obj U))
        (((proEtaleRingModuleAdjunction f R S c).unit.app M).val.app (op U) x) =
      ((sfIntrinsicConstantModuleAdjunction f
        (finiteCoefficientRing l E (n + 1))).unit.app M).val.app (op U) x :=
    (pullbackTensorFiniteRealization_existsUnique l E f n).exists.choose_spec M U x
  have hui (M : normalizedDVRModules l E Y n) (U : Y.ProEt)
      (x : M.val.obj (op U)) :
      (e.inv.app M).val.app (op ((proEtaleBaseChange f).obj U))
        (((sfIntrinsicConstantModuleAdjunction f
          (finiteCoefficientRing l E (n + 1))).unit.app M).val.app (op U) x) =
      ((proEtaleRingModuleAdjunction f R S c).unit.app M).val.app (op U) x := by
    rw [← hu M U x]
    exact congrArg (fun a ↦ a.val.app (op ((proEtaleBaseChange f).obj U))
      (((proEtaleRingModuleAdjunction f R S c).unit.app M).val.app (op U) x))
      (e.hom_inv_id_app M)
  unfold finitePullbackTensorChainIso
  intro p q i hpq U x y
  let V := op ((proEtaleBaseChange f).obj U)
  change ((T.map (Prod.mkHom (eC.hom.app P) (eC.hom.app Q))).f i).val.app V
      (((proEtaleTensorPullbackTotalIso f R S c P Q).inv.f i).val.app V
        ((e.inv.app _).val.app V
          (((sfIntrinsicConstantModuleAdjunction f
            (finiteCoefficientRing l E (n + 1))).unit.app _).val.app (op U)
            (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y) R
              P Q p q i hpq (op U) x y)))) = _
  erw [hui]
  erw [proEtaleTensorPullbackTotal_generators]
  erw [coefficientTotalTensor_map_generator]
  change coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X) S FP FQ p q i hpq V
      ((e.hom.app (P.X p)).val.app V
        (((proEtaleRingModuleAdjunction f R S c).unit.app (P.X p)).val.app (op U) x))
      ((e.hom.app (Q.X q)).val.app V
        (((proEtaleRingModuleAdjunction f R S c).unit.app (Q.X q)).val.app (op U) y)) = _
  erw [hu, hu]

end WeilConjectures
