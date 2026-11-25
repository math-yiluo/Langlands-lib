/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurCompactSupport.ScalarPullCoefficientComplexNormalization
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorCoefficientResolutionSquare
import WeilConjectures.SixFunctors.PurCompactSupport.ScalarPullCoefficientModuleTensor

/-! # Ordinary total tensor and the coefficient square

Source: Stacks Project, Tags 03EL and 07A4.
(blueprint: lem-sf-scalar-pull-coefficient-total-tensor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurCompactSupport
attribute [local irreducible] scalarPullComplex scalarTensorTotal proEtaleTensorPullbackTotalIso
  SheafOfModules.monoidalCategory CategoryTheory.Functor.mapBifunctorHomologicalComplex
  HomologicalComplex₂.total CategoryTheory.Functor.mapDerivedCategory
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex

attribute [local instance] SheafOfModules.monoidalCategory
attribute [local instance 100000] coefficientSiteSmall coefficientRingSheafify
  coefficientAbSheafify coefficientAbLocallyBijective
attribute [local irreducible] scalarPullModule proEtaleRingModulePullback
  proEtaleOrdinaryTensorPullback scalarOrdinaryTensor reductionChange completedAdicChange
  proEtaleRingModuleAdjunction pbcScalarAdjunction
open MonoidalCategory

private theorem total_tensor_exists {D : Type*} [Category D] [Preadditive D]
    [MonoidalCategory D] [MonoidalPreadditive D] [CategoryTheory.Limits.HasCoproducts.{0} D]
    (P Q : CochainComplex D ℤ) :
    HomologicalComplex.HasMapBifunctor P Q (curriedTensor D) (.up ℤ) := by
  infer_instance

attribute [local instance 100000] total_tensor_exists

private theorem scalar_total_ι {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S)
    (P Q : CochainComplex (pbcModules W R) ℤ) (p q n : ℤ) (h : p + q = n) :
    (pbcExtend a).map
        (CochainComplex.ιMapBifunctor P Q (proEtaleOrdinaryTensor W R) p q n h) ≫
      (@inv _ _ _ _ (scalarTensorTotal a P Q) (scalarTensorTotal_isIso a P Q)).f n =
    (scalarOrdinaryTensor a (P.X p) (Q.X q)).hom ≫
      CochainComplex.ιMapBifunctor
        (((pbcExtend a).mapHomologicalComplex (.up ℤ)).obj P)
        (((pbcExtend a).mapHomologicalComplex (.up ℤ)).obj Q)
        (proEtaleOrdinaryTensor W S) p q n h := by
  let e := @asIso _ _ _ _ (scalarTensorTotal a P Q) (scalarTensorTotal_isIso a P Q)
  change _ ≫ e.inv.f n = _
  apply (cancel_mono (e.hom.f n)).1
  simp only [Category.assoc, ← HomologicalComplex.comp_f, Iso.inv_hom_id,
    HomologicalComplex.id_f, Category.comp_id]
  change _ = _ ≫ _ ≫ (scalarTensorTotal a P Q).f n
  simp only [scalarTensorTotal, tensorPullbackTotal, tensorPullbackTotalComponent,
    HomologicalComplex.ι_mapBifunctorDesc, Iso.hom_inv_id_assoc]

private theorem geometric_total_ι {U V : Scheme.{u}} (g : U ⟶ V)
    (R : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S)
    (P Q : CochainComplex (pbcModules V R) ℤ) (p q n : ℤ) (h : p + q = n) :
    (proEtaleRingModulePullback g R S c).map
        (CochainComplex.ιMapBifunctor P Q (proEtaleOrdinaryTensor V R) p q n h) ≫
      (proEtaleTensorPullbackTotalIso g R S c P Q).inv.f n =
    (proEtaleOrdinaryTensorPullback g R S c (P.X p) (Q.X q)).hom ≫
      CochainComplex.ιMapBifunctor
        (((proEtaleRingModulePullback g R S c).mapHomologicalComplex (.up ℤ)).obj P)
        (((proEtaleRingModulePullback g R S c).mapHomologicalComplex (.up ℤ)).obj Q)
        (proEtaleOrdinaryTensor U S) p q n h := by
  apply (cancel_mono ((proEtaleTensorPullbackTotalIso g R S c P Q).hom.f n)).1
  simp only [Category.assoc, ← HomologicalComplex.comp_f, Iso.inv_hom_id,
    HomologicalComplex.id_f]
  simp only [proEtaleTensorPullbackTotalIso, asIso_hom, proEtaleTensorPullbackTotal,
    tensorPullbackTotal, tensorPullbackTotalComponent,
    HomologicalComplex.ι_mapBifunctorDesc, Iso.hom_inv_id_assoc]
  simp only [proEtaleOrdinaryTensor]
  erw [Category.comp_id]

private theorem scalarPullComplex_f {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (g : U ⟶ V)
    (P : CochainComplex (pbcModules V (R.ring V)) ℤ) (n : ℤ) :
    ((scalarPullComplex a g).hom.app P).f n = (scalarPullModule a g).hom.app (P.X n) := by
  simp only [scalarPullComplex, Iso.trans_hom, NatTrans.comp_app,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f, NatIso.mapHomologicalComplex_hom_app_f,
    Iso.symm_hom, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  change 𝟙 _ ≫ (scalarPullModule a g).hom.app (P.X n) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

private theorem total_map_ι {W : Scheme.{u}}
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    {P Q P' Q' : CochainComplex (pbcModules W R) ℤ} (a : P ⟶ P') (b : Q ⟶ Q')
    (p q n : ℤ) (h : p + q = n) :
    CochainComplex.ιMapBifunctor P Q (proEtaleOrdinaryTensor W R) p q n h ≫
      ((proEtaleResolutionTotal W R).map (Prod.mkHom a b)).f n =
    (a.f p ⊗ₘ b.f q) ≫
      CochainComplex.ιMapBifunctor P' Q' (proEtaleOrdinaryTensor W R) p q n h := by
  simp only [proEtaleResolutionTotal, Functor.uncurry_obj_map,
    Functor.map₂HomologicalComplex, HomologicalComplex.comp_f,
    HomologicalComplex.ι_mapBifunctorMap_assoc, HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.id_f, proEtaleOrdinaryTensor, curriedTensor_map_app,
    curriedTensor_obj_map, tensorHom_def, Category.assoc]
  simp only [whiskerLeft_id, id_whiskerRight]
  erw [Category.id_comp, Category.id_comp]

/-- The ordinary coefficient square respects signed total tensor.
There are no derived tensor models, localizations or derived adjunctions in this statement.

Source: Stacks 03EL and 07A4, the pure-tensor calculation before passage to derived categories
(blueprint: lem-sf-scalar-pull-coefficient-total-tensor).

Proof: first compare the ordinary module maps. The transpose of scalarPullModule
under the composite adjunction is identity on the underlying direct-image sections.
Consequently it sends an iterated unit tensor to the corresponding iterated unit
tensor. ScalarOrdinaryTensor and proEtaleOrdinaryTensorPullback split an inserted
tensor into its two factors. On pure tensors the two routes insert the same units
and multiply the same coefficients. Linearity and balancing extend this equality
to scalar tensors, and the sheafification universal property extends it to module
sheaves. Invert the four ordinary tensor comparisons to obtain the inverse square.
In degree n of the direct-sum total, precompose with every (p,q) summand, p+q=n.
The defining summand formula for tensorPullbackTotal reduces each equality to that
inverse module square. The coefficient comparison is natural for the summand
inclusion. Coproduct extensionality proves the degree-n equality; cochain
extensionality proves the displayed identity. All maps preserve both degrees,
so there is no permutation and no extra sign. Identity coefficient maps, zero
rings, zero complexes and nonflat coefficient changes obey the same calculation. -/
theorem scalarPull_coefficient_total_tensor
    {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (g : U ⟶ V)
    (P Q : CochainComplex (pbcModules V (R.ring V)) ℤ) :
    ((proEtaleRingModulePullback g (S.ring V) (S.ring U)
        (S.pull g)).mapHomologicalComplex (.up ℤ)).map
      (@inv.{u + 1, u + 2} _ _ _ _ (scalarTensorTotal (a.map V) P Q)
        (scalarTensorTotal_isIso (a.map V) P Q)) ≫
      (proEtaleTensorPullbackTotalIso g (S.ring V) (S.ring U) (S.pull g)
        (((pbcExtend (a.map V)).mapHomologicalComplex (.up ℤ)).obj P)
        (((pbcExtend (a.map V)).mapHomologicalComplex (.up ℤ)).obj Q)).inv ≫
      (proEtaleResolutionTotal U (S.ring U)).map
          (Prod.mkHom ((scalarPullComplex a g).hom.app P)
            ((scalarPullComplex a g).hom.app Q)) =
    (scalarPullComplex a g).hom.app
        ((proEtaleResolutionTotal V (R.ring V)).obj (P, Q)) ≫
      ((pbcExtend (a.map U)).mapHomologicalComplex (.up ℤ)).map
        ((proEtaleTensorPullbackTotalIso g (R.ring V) (R.ring U) (R.pull g) P Q).inv) ≫
      @inv.{u + 1, u + 2} _ _ _ _
        (scalarTensorTotal (a.map U)
          (((proEtaleRingModulePullback g (R.ring V) (R.ring U)
            (R.pull g)).mapHomologicalComplex (.up ℤ)).obj P)
          (((proEtaleRingModulePullback g (R.ring V) (R.ring U)
            (R.pull g)).mapHomologicalComplex (.up ℤ)).obj Q))
        (scalarTensorTotal_isIso (a.map U) _ _) := by
  let F := proEtaleRingModulePullback g (R.ring V) (R.ring U) (R.pull g)
  let G := pbcExtend (a.map V)
  let H := pbcExtend (a.map U)
  let K := proEtaleRingModulePullback g (S.ring V) (S.ring U) (S.pull g)
  let c := scalarPullModule a g
  let := (pbcScalarAdjunction (a.map V)).isLeftAdjoint
  let := (proEtaleRingModuleAdjunction g (S.ring V) (S.ring U)
    (S.pull g)).isLeftAdjoint
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map (G ⋙ K)
  intro p q hpq
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    scalarPullComplex_f, Functor.comp_map]
  let i := CochainComplex.ιMapBifunctor P Q (proEtaleOrdinaryTensor V (R.ring V))
    p q n hpq
  let j := CochainComplex.ιMapBifunctor
    ((H.mapHomologicalComplex (.up ℤ)).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj P))
    ((H.mapHomologicalComplex (.up ℤ)).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj Q))
    (proEtaleOrdinaryTensor U (S.ring U)) p q n hpq
  change K.map (G.map i) ≫ K.map _ ≫ _ ≫ _ =
    K.map (G.map i) ≫ c.hom.app _ ≫ H.map _ ≫ _
  rw [← K.map_comp_assoc, scalar_total_ι, K.map_comp]
  simp only [Category.assoc]
  have ht := geometric_total_ι g (S.ring V) (S.ring U) (S.pull g)
    ((G.mapHomologicalComplex (.up ℤ)).obj P)
    ((G.mapHomologicalComplex (.up ℤ)).obj Q) p q n hpq
  rw [reassoc_of% ht, total_map_ι]
  simp only [scalarPullComplex_f]
  erw [c.hom.naturality_assoc i]
  change _ = c.hom.app (P.X p ⊗ Q.X q) ≫ H.map (F.map i) ≫ H.map _ ≫ _
  rw [← H.map_comp_assoc, geometric_total_ι, H.map_comp]
  simp only [Category.assoc]
  rw [scalar_total_ι]
  exact congrArg (fun z ↦ z ≫ j) (scalarPull_coefficient_module_tensor a g (P.X p) (Q.X q))

end WeilConjectures.PurCompactSupport
