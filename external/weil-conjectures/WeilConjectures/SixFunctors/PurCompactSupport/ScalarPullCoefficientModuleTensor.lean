/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurCompactSupport.ScalarPullCoefficientComplexNormalization
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement

/-! # The ordinary module tensor square for a coefficient change

Source: Stacks Project, Tags 03EL and 07A4.
(blueprint: lem-sf-scalar-pull-coefficient-module-tensor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurCompactSupport
attribute [local irreducible] SheafOfModules.monoidalCategory

attribute [local instance] SheafOfModules.monoidalCategory
attribute [local instance 100000] coefficientSiteSmall coefficientRingSheafify
  coefficientAbSheafify coefficientAbLocallyBijective
attribute [local irreducible] scalarPullModule proEtaleRingModulePullback
  proEtaleOrdinaryTensorPullback scalarOrdinaryTensor reductionChange completedAdicChange
  proEtaleRingModuleAdjunction pbcScalarAdjunction
open MonoidalCategory

private theorem scalar_unit {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S)
    (M : pbcModules W R) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcScalarAdjunction a).unit.app M).val.app U x =
      pbcTensorSection a M U 1 x := by
  unfold pbcScalarAdjunction
  exact (pbcScalarAdjunction_exists a).exists.choose_spec M U x

private theorem scalarPull_unit {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (g : U ⟶ V) (M : pbcModules V (R.ring V))
    (W : V.ProEtᵒᵖ) (x : M.val.obj W) :
    ((scalarPullModule a g).hom.app M).val.app
        (Opposite.op ((proEtaleBaseChange g).obj W.unop))
      (((proEtaleRingModuleAdjunction g (S.ring V) (S.ring U)
        (S.pull g)).unit.app ((pbcExtend (a.map V)).obj M)).val.app W
          (pbcTensorSection (a.map V) M W 1 x)) =
      pbcTensorSection (a.map U) _
        (Opposite.op ((proEtaleBaseChange g).obj W.unop)) 1
          (((proEtaleRingModuleAdjunction g (R.ring V) (R.ring U)
            (R.pull g)).unit.app M).val.app W x) := by
  let d := proEtaleRingRestrictionDirectImage g
    (R.ring V) (S.ring V) (R.ring U) (S.ring U)
    (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)
  let ad := ((proEtaleRingModuleAdjunction g (R.ring V) (R.ring U)
    (R.pull g)).comp (pbcScalarAdjunction (a.map U))).ofNatIsoRight d.symm
  let bd := (pbcScalarAdjunction (a.map V)).comp
    (proEtaleRingModuleAdjunction g (S.ring V) (S.ring U) (S.pull g))
  have hh := Adjunction.homEquiv_leftAdjointUniq_hom_app bd ad M
  have he : (bd.leftAdjointUniq ad).hom.app M = (scalarPullModule a g).hom.app M := by
    unfold scalarPullModule
    exact (Adjunction.leftAdjointUniq_inv_app ad bd M).symm
  rw [he] at hh
  have hz := congrArg (fun f ↦ f.val.app W x) hh
  have hd (N : pbcModules U (S.ring U)) (w : V.ProEtᵒᵖ)
      (n : N.val.obj ((proEtaleBaseChange g).op.obj w)) :
      (d.hom.app N).val.app w n = n := by
    dsimp only [d, proEtaleRingRestrictionDirectImage]
    exact (Classical.choose_spec (proEtaleRingRestrictionDirectImage_existsUnique g
      (R.ring V) (S.ring V) (R.ring U) (S.ring U)
      (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g))).1 N w n
  have hi (N : pbcModules U (S.ring U)) (w : V.ProEtᵒᵖ)
      (n : N.val.obj ((proEtaleBaseChange g).op.obj w)) :
      (d.inv.app N).val.app w n = n := by
    have h := congrArg (fun f ↦ f.val.app w n) (d.inv_hom_id_app N)
    change (d.hom.app N).val.app w ((d.inv.app N).val.app w n) = n at h
    rw [hd] at h
    exact h
  change (((pbcScalarAdjunction (a.map V)).homEquiv _ _
    ((proEtaleRingModuleAdjunction g (S.ring V) (S.ring U) (S.pull g)).homEquiv _ _
      ((scalarPullModule a g).hom.app M))).val.app W x) = _ at hz
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit] at hz
  change ((scalarPullModule a g).hom.app M).val.app _
    (((proEtaleRingModuleAdjunction g (S.ring V) (S.ring U) (S.pull g)).unit.app
      ((pbcExtend (a.map V)).obj M)).val.app W
        (((pbcScalarAdjunction (a.map V)).unit.app M).val.app W x)) = _ at hz
  rw [scalar_unit] at hz
  change _ = (d.inv.app _).val.app W
    (((proEtaleRingModuleAdjunction g (R.ring V) (R.ring U) (R.pull g)).unit.app M
      ≫ (proEtaleRingModuleDirectImage g (R.ring V) (R.ring U) (R.pull g)).map
        ((pbcScalarAdjunction (a.map U)).unit.app _)).val.app W x) at hz
  rw [hi] at hz
  change _ = ((pbcScalarAdjunction (a.map U)).unit.app _).val.app _
    (((proEtaleRingModuleAdjunction g (R.ring V) (R.ring U)
      (R.pull g)).unit.app M).val.app W x) at hz
  rw [scalar_unit] at hz
  exact hz

private theorem tensorPair_map (W : Scheme.{u})
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    {M M' N N' : pbcModules W R} (f : M ⟶ M') (h : N ⟶ N')
    (Z : W.ProEtᵒᵖ) (x : M.val.obj Z) (y : N.val.obj Z) :
    (f ⊗ₘ h).val.app Z (proEtaleTensorPair W R M N Z x y) =
      proEtaleTensorPair W R M' N' Z (f.val.app Z x) (h.val.app Z y) := by
  exact SheafOfModules.ScalarHomOrdinary.pure_map.{u + 1, u, u + 1} R f h Z x y

private theorem scalar_tensor_unit {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S)
    (M N : pbcModules W R) (Z : W.ProEtᵒᵖ) (x : M.val.obj Z) (y : N.val.obj Z) :
    (scalarOrdinaryTensor a M N).hom.val.app Z
      (pbcTensorSection a _ Z 1 (proEtaleTensorPair W R M N Z x y)) =
      proEtaleTensorPair W S _ _ Z
        (pbcTensorSection a M Z 1 x) (pbcTensorSection a N Z 1 y) := by
  unfold scalarOrdinaryTensor
  exact (scalarOrdinaryTensor_existsUnique a).exists.choose_spec M N Z 1 x y

private theorem scalar_map_unit {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S)
    {M N : pbcModules W R} (f : M ⟶ N) (Z : W.ProEtᵒᵖ) (x : M.val.obj Z) :
    ((pbcExtend a).map f).val.app Z (pbcTensorSection a M Z 1 x) =
      pbcTensorSection a N Z 1 (f.val.app Z x) := by
  have h := congrArg (fun f ↦ f.val.app Z x) ((pbcScalarAdjunction a).unit.naturality f)
  change ((pbcScalarAdjunction a).unit.app N).val.app Z (f.val.app Z x) =
    ((pbcExtend a).map f).val.app Z
      (((pbcScalarAdjunction a).unit.app M).val.app Z x) at h
  rw [scalar_unit, scalar_unit] at h
  exact h.symm

private theorem geometric_map_unit {U V : Scheme.{u}} (g : U ⟶ V)
    (R : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S)
    {M N : pbcModules V R} (f : M ⟶ N) (Z : V.ProEtᵒᵖ) (x : M.val.obj Z) :
    ((proEtaleRingModulePullback g R S c).map f).val.app
        (Opposite.op ((proEtaleBaseChange g).obj Z.unop))
      (((proEtaleRingModuleAdjunction g R S c).unit.app M).val.app Z x) =
      ((proEtaleRingModuleAdjunction g R S c).unit.app N).val.app Z (f.val.app Z x) := by
  have h := congrArg (fun f ↦ f.val.app Z x)
    ((proEtaleRingModuleAdjunction g R S c).unit.naturality f)
  exact h.symm

private theorem geometric_tensor_unit {U V : Scheme.{u}} (g : U ⟶ V)
    (R : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S)
    (M N : pbcModules V R) (Z : V.ProEtᵒᵖ) (x : M.val.obj Z) (y : N.val.obj Z) :
    (proEtaleOrdinaryTensorPullback g R S c M N).hom.val.app
        (Opposite.op ((proEtaleBaseChange g).obj Z.unop))
      (((proEtaleRingModuleAdjunction g R S c).unit.app (M ⊗ N)).val.app Z
        (proEtaleTensorPair V R M N Z x y)) =
      proEtaleTensorPair U S _ _ (Opposite.op ((proEtaleBaseChange g).obj Z.unop))
        (((proEtaleRingModuleAdjunction g R S c).unit.app M).val.app Z x)
        (((proEtaleRingModuleAdjunction g R S c).unit.app N).val.app Z y) := by
  unfold proEtaleOrdinaryTensorPullback
  exact (proEtaleOrdinaryTensorPullback_existsUnique g R S c).exists.choose_spec.2
    M N Z.unop x y

/-- Scalar extension and geometric pullback respect the normalized ordinary tensor maps.

Source: Stacks 03EL, the tensor universal property under the module adjunctions.
(blueprint: lem-sf-scalar-pull-coefficient-module-tensor).

Proof: the unit identity for uniqueness of left adjoints shows that the comparison
carries the successive scalar and geometric units to the units in the other order.
Transpose both tensor routes through the geometric and scalar adjunctions and test
on sheaf tensor generators. Naturality of the geometric unit moves the scalar tensor
comparison through it. The two normalized tensor formulas split the generator into
the two successive units. Applying the comparison separately to these factors gives
the units in the other order. On the other route, first apply the comparison to the
whole tensor, use naturality of the target scalar unit, and apply the geometric and
scalar tensor formulas. The two expressions are identical. Tensor sheafification
extensionality and injectivity of the adjunction bijections finish. The argument
uses no flatness and also applies to zero coefficient rings and zero modules. -/
theorem scalarPull_coefficient_module_tensor {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (g : U ⟶ V) (M N : pbcModules V (R.ring V)) :
    let F := proEtaleRingModulePullback g (R.ring V) (R.ring U) (R.pull g)
    let G := pbcExtend (a.map V)
    let H := pbcExtend (a.map U)
    let K := proEtaleRingModulePullback g (S.ring V) (S.ring U) (S.pull g)
    K.map (scalarOrdinaryTensor (a.map V) M N).hom ≫
      (proEtaleOrdinaryTensorPullback g (S.ring V) (S.ring U) (S.pull g)
        (G.obj M) (G.obj N)).hom ≫
      ((scalarPullModule a g).hom.app M ⊗ₘ (scalarPullModule a g).hom.app N) =
    (scalarPullModule a g).hom.app (M ⊗ N) ≫
      H.map (proEtaleOrdinaryTensorPullback g (R.ring V) (R.ring U) (R.pull g) M N).hom ≫
      (scalarOrdinaryTensor (a.map U) (F.obj M) (F.obj N)).hom := by
  let F := proEtaleRingModulePullback g (R.ring V) (R.ring U) (R.pull g)
  let G := pbcExtend (a.map V)
  let H := pbcExtend (a.map U)
  let K := proEtaleRingModulePullback g (S.ring V) (S.ring U) (S.pull g)
  let c := scalarPullModule a g
  let μR := proEtaleOrdinaryTensorPullback g (R.ring V) (R.ring U) (R.pull g)
  let μS := proEtaleOrdinaryTensorPullback g (S.ring V) (S.ring U) (S.pull g)
  let adj := proEtaleRingModuleAdjunction g (S.ring V) (S.ring U) (S.pull g)
  apply (adj.homEquiv _ _).injective
  apply ((pbcScalarAdjunction (a.map V)).homEquiv _ _).injective
  apply SheafOfModules.ScalarHomOrdinary.pure_hom_ext.{u + 1, u, u + 1} (R.ring V) M N
  intro Z x y
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change (c.hom.app M ⊗ₘ c.hom.app N).val.app _
    ((μS (G.obj M) (G.obj N)).hom.val.app _
      ((K.map (scalarOrdinaryTensor (a.map V) M N).hom).val.app _
        ((adj.unit.app (G.obj (M ⊗ N))).val.app Z
          (((pbcScalarAdjunction (a.map V)).unit.app (M ⊗ N)).val.app Z
            (proEtaleTensorPair V (R.ring V) M N Z x y))))) =
    (scalarOrdinaryTensor (a.map U) (F.obj M) (F.obj N)).hom.val.app _
      ((H.map (μR M N).hom).val.app _
        ((c.hom.app (M ⊗ N)).val.app _
          ((adj.unit.app (G.obj (M ⊗ N))).val.app Z
            (((pbcScalarAdjunction (a.map V)).unit.app (M ⊗ N)).val.app Z
              (proEtaleTensorPair V (R.ring V) M N Z x y)))))
  erw [scalar_unit]
  erw [geometric_map_unit]
  erw [scalar_tensor_unit]
  erw [geometric_tensor_unit]
  erw [tensorPair_map, scalarPull_unit, scalarPull_unit, scalarPull_unit,
    scalar_map_unit]
  erw [geometric_tensor_unit]
  erw [scalar_tensor_unit]
  rfl

end WeilConjectures.PurCompactSupport
