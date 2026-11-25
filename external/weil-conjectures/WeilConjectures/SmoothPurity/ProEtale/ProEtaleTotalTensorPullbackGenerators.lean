/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackModels

/-! # Homogeneous total-tensor generator calculations

Source: Stacks Tags 03EL and 07A4.
(blueprint: lem-pur-proetale-total-tensor-pullback-generators).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open MonoidalCategory TensorProduct
namespace WeilConjectures
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] SheafOfModules.monoidalCategory
  proEtaleTensorPullbackTotalIso CategoryTheory.Functor.mapBifunctorHomologicalComplex
  HomologicalComplex₂.total
attribute [local instance] SheafOfModules.monoidalCategory

private theorem geometric_total_ι {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (P Q : CochainComplex (proEtaleRingModules Y R) ℤ)
    (p q i : ℤ) (h : p + q = i) :
    (proEtaleRingModulePullback f R S c).map
        (CochainComplex.ιMapBifunctor P Q (proEtaleOrdinaryTensor Y R) p q i h) ≫
      (proEtaleTensorPullbackTotalIso f R S c P Q).inv.f i =
    (proEtaleOrdinaryTensorPullback f R S c (P.X p) (Q.X q)).hom ≫
      CochainComplex.ιMapBifunctor
        (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj P)
        (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj Q)
        (proEtaleOrdinaryTensor X S) p q i h := by
  apply (cancel_mono ((proEtaleTensorPullbackTotalIso f R S c P Q).hom.f i)).1
  simp only [Category.assoc, ← HomologicalComplex.comp_f, Iso.inv_hom_id,
    HomologicalComplex.id_f]
  simp only [proEtaleTensorPullbackTotalIso, asIso_hom, proEtaleTensorPullbackTotal,
    tensorPullbackTotal, tensorPullbackTotalComponent,
    HomologicalComplex.ι_mapBifunctorDesc, Iso.hom_inv_id_assoc]
  simp only [proEtaleOrdinaryTensor]
  erw [Category.comp_id]

private theorem generator_ι {W : Scheme.{u}}
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (P Q : CochainComplex (proEtaleRingModules W R) ℤ)
    (p q i : ℤ) (h : p + q = i) (V : W.ProEtᵒᵖ)
    (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) :
    coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W) R P Q p q i h V x y =
      (CochainComplex.ιMapBifunctor P Q (proEtaleOrdinaryTensor W R) p q i h).val.app V
        (proEtaleTensorPair W R (P.X p) (Q.X q) V x y) := by
  rfl

/-- The inverse signed-total comparison preserves the inverse-image unit generators.
Source: Stacks 03EL and 07A4
(blueprint: lem-pur-proetale-total-tensor-pullback-generators).
Proof: write a homogeneous generator as the ordinary pure tensor followed by the
total-summand inclusion. Naturality of the pullback adjunction unit moves that
inclusion past the unit. The total comparison's defining summand equation reduces
the claim to the ordinary tensor comparison's prescribed pure-unit equation.
Apply that equation and the target summand inclusion. All maps preserve bidegree,
so the signed total differential contributes no extra sign. -/
theorem proEtaleTensorPullbackTotal_generators {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (P Q : CochainComplex (proEtaleRingModules Y R) ℤ)
    (p q i : ℤ) (h : p + q = i) (U : Y.ProEt)
    (x : (P.X p).val.obj (op U)) (y : (Q.X q).val.obj (op U)) :
    ((proEtaleTensorPullbackTotalIso f R S c P Q).inv.f i).val.app
      (op ((proEtaleBaseChange f).obj U))
      (((proEtaleRingModuleAdjunction f R S c).unit.app
        (((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology Y) R).obj (P, Q)).X i)).val.app
          (op U) (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y) R
            P Q p q i h (op U) x y)) =
    coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X) S
      (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj P)
      (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj Q)
      p q i h (op ((proEtaleBaseChange f).obj U))
      (((proEtaleRingModuleAdjunction f R S c).unit.app (P.X p)).val.app (op U) x)
      (((proEtaleRingModuleAdjunction f R S c).unit.app (Q.X q)).val.app (op U) y) := by
  let j := CochainComplex.ιMapBifunctor P Q (proEtaleOrdinaryTensor Y R) p q i h
  let v := proEtaleTensorPair Y R (P.X p) (Q.X q) (op U) x y
  let V := op ((proEtaleBaseChange f).obj U)
  have hn := congrArg (fun a ↦ a.val.app (op U) v)
    ((proEtaleRingModuleAdjunction f R S c).unit.naturality j)
  change ((proEtaleRingModuleAdjunction f R S c).unit.app _).val.app (op U)
      (j.val.app (op U) v) =
    ((proEtaleRingModulePullback f R S c).map j).val.app V
      (((proEtaleRingModuleAdjunction f R S c).unit.app _).val.app (op U) v) at hn
  rw [generator_ι]
  erw [hn]
  have hi := congrArg (fun a ↦ a.val.app V
    (((proEtaleRingModuleAdjunction f R S c).unit.app _).val.app (op U) v))
    (geometric_total_ι f R S c P Q p q i h)
  change ((proEtaleTensorPullbackTotalIso f R S c P Q).inv.f i).val.app V
    (((proEtaleRingModulePullback f R S c).map j).val.app V _) = _ at hi ⊢
  erw [hi]
  change (CochainComplex.ιMapBifunctor
    (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj P)
    (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj Q)
    (proEtaleOrdinaryTensor X S) p q i h).val.app V
    ((proEtaleOrdinaryTensorPullback f R S c (P.X p) (Q.X q)).hom.val.app V
      (((proEtaleRingModuleAdjunction f R S c).unit.app _).val.app (op U) v)) = _
  erw [(proEtaleOrdinaryTensorPullback_existsUnique f R S c).exists.choose_spec.2]
  rfl

end WeilConjectures
