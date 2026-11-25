/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FinitePullbackTensorRep.FinitePullbackTensorRepresentativeData
import WeilConjectures.AlgebraicGeometry.Finite.FiniteIntrinsicPullbackUnitComposition
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackModels
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
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
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits

/-! # Composition of the ordinary signed tensor comparison

Source: Stacks 03EL, 07A4 and 00YV.
(blueprint: lem-pur-finite-pullback-tensor-chain-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.ProEt
  CategoryTheory.MorphismProperty
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
private def baseComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    proEtaleBaseChange (f ≫ g) ≅ proEtaleBaseChange g ⋙ proEtaleBaseChange f := by
  exact MorphismProperty.Over.pullbackComp f g

attribute [local implicit_reducible] proEtaleConstantModuleDirectImage
  proEtaleRingModuleDirectImage SheafOfModules.pushforward
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'

namespace WeilConjectures.FinitePullbackTensorRep
attribute [local irreducible] Scheme.residueField finiteIntrinsicClosed
  finiteIntrinsicTensorModels finitePullbackTensorConstruction
attribute [local implicit_reducible] integralCoefficientSheaf
  integralCoefficientCommRingSheaf finiteIntrinsicDerivedTensor
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private abbrev unit {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : normalizedDVRModules l E Y n) (U : Y.ProEt)
    (m : M.val.obj (Opposite.op U)) :=
  ((proEtaleRingModuleAdjunction f (integralCoefficientCommRingSheaf l E Y n)
    (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n)).unit.app
      M).val.app (Opposite.op U) m

private abbrev iunit {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : normalizedDVRModules l E Y n) (U : Y.ProEt)
    (m : M.val.obj (Opposite.op U)) :=
  ((sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1))).unit.app
    M).val.app (Opposite.op U) m

private theorem realization_unit {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : normalizedDVRModules l E Y n) (U : Y.ProEt)
    (m : M.val.obj (Opposite.op U)) :
    ((pullbackTensorFiniteRealization l E f n).hom.app M).val.app
        (Opposite.op ((proEtaleBaseChange f).obj U)) (unit l E f n M U m) =
      iunit l E f n M U m :=
  (pullbackTensorFiniteRealization_existsUnique l E f n).exists.choose_spec M U m

private theorem realization_inv_unit {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : normalizedDVRModules l E Y n) (U : Y.ProEt)
    (m : M.val.obj (Opposite.op U)) :
    ((pullbackTensorFiniteRealization l E f n).inv.app M).val.app
        (Opposite.op ((proEtaleBaseChange f).obj U)) (iunit l E f n M U m) =
      unit l E f n M U m := by
  rw [← realization_unit l E f n M U m]
  exact congrArg (fun t ↦ t.val.app
    (Opposite.op ((proEtaleBaseChange f).obj U)) (unit l E f n M U m))
    ((pullbackTensorFiniteRealization l E f n).hom_inv_id_app M)

private theorem unit_naturality {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    {M N : normalizedDVRModules l E Y n} (a : M ⟶ N) (U : Y.ProEt)
    (m : M.val.obj (Opposite.op U)) :
    ((ordinary l E f n).map a).val.app
        (Opposite.op ((proEtaleBaseChange f).obj U)) (unit l E f n M U m) =
      unit l E f n N U (a.val.app (Opposite.op U) m) := by
  exact (congrArg (fun t ↦ t.val.app (Opposite.op U) m)
    ((proEtaleRingModuleAdjunction f (integralCoefficientCommRingSheaf l E Y n)
      (integralCoefficientCommRingSheaf l E X n)
      (pullbackTensorCoefficientIso l E f n)).unit.naturality a)).symm

private theorem iunit_naturality {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    {M N : normalizedDVRModules l E Y n} (a : M ⟶ N) (U : Y.ProEt)
    (m : M.val.obj (Opposite.op U)) :
    ((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).map a).val.app
        (Opposite.op ((proEtaleBaseChange f).obj U)) (iunit l E f n M U m) =
      iunit l E f n N U (a.val.app (Opposite.op U) m) := by
  exact (congrArg (fun t ↦ t.val.app (Opposite.op U) m)
    ((sfIntrinsicConstantModuleAdjunction f
      (finiteCoefficientRing l E (n + 1))).unit.naturality a)).symm

private theorem moduleComp_unit {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Z ⟶ X)
    (n : ℕ) (M : normalizedDVRModules l E Y n) (U : Y.ProEt)
    (m : M.val.obj (Opposite.op U)) :
    ((moduleComp l E f h n).hom.app M).val.app
        (Opposite.op ((proEtaleBaseChange (h ≫ f)).obj U))
        (unit l E (h ≫ f) n M U m) =
      ((ordinary l E h n).obj ((ordinary l E f n).obj M)).val.map
        ((baseComp h f).hom.app U).op
        (unit l E h n ((ordinary l E f n).obj M) ((proEtaleBaseChange f).obj U)
          (unit l E f n M U m)) := by
  have hc := finiteIntrinsicPullback_unit_comp (finiteCoefficientRing l E (n + 1)) f h M U m
  change ((sfIntrinsicPullbackComp (finiteCoefficientRing l E (n + 1)) h f).hom.app
    M).val.app (Opposite.op ((proEtaleBaseChange (h ≫ f)).obj U))
        (iunit l E (h ≫ f) n M U m) =
      ((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) h).obj
        ((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).obj M)).val.map
          ((baseComp h f).hom.app U).op
          (iunit l E h n
            ((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).obj M)
            ((proEtaleBaseChange f).obj U) (iunit l E f n M U m)) at hc
  change ((pullbackTensorFiniteRealization l E h n).inv.app
      ((ordinary l E f n).obj M)).val.app _
      (((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) h).map
        ((pullbackTensorFiniteRealization l E f n).inv.app M)).val.app _
        (((sfIntrinsicPullbackComp (finiteCoefficientRing l E (n + 1)) h f).hom.app M).val.app _
          (((pullbackTensorFiniteRealization l E (h ≫ f) n).hom.app M).val.app _
            (unit l E (h ≫ f) n M U m)))) = _
  erw [realization_unit l E (h ≫ f) n M U m, hc]
  rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply]
  apply congrArg (fun x ↦
    ((ordinary l E h n).obj ((ordinary l E f n).obj M)).val.map
      ((baseComp h f).hom.app U).op x)
  change ((pullbackTensorFiniteRealization l E h n).inv.app
      ((ordinary l E f n).obj M)).val.app
        (Opposite.op ((proEtaleBaseChange h).obj ((proEtaleBaseChange f).obj U)))
        (((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) h).map
          ((pullbackTensorFiniteRealization l E f n).inv.app M)).val.app
            (Opposite.op ((proEtaleBaseChange h).obj ((proEtaleBaseChange f).obj U)))
            (iunit l E h n ((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).obj M)
              ((proEtaleBaseChange f).obj U) (iunit l E f n M U m))) = _
  rw [iunit_naturality l E h n, realization_inv_unit l E f n,
    realization_inv_unit l E h n]

private abbrev mu {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M N : normalizedDVRModules l E Y n) :=
  proEtaleOrdinaryTensorPullback f (integralCoefficientCommRingSheaf l E Y n)
    (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n) M N

private theorem mu_unit {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M N : normalizedDVRModules l E Y n) (U : Y.ProEt)
    (m : M.val.obj (Opposite.op U)) (t : N.val.obj (Opposite.op U)) :
    (mu l E f n M N).hom.val.app (Opposite.op ((proEtaleBaseChange f).obj U))
        (unit l E f n
          (((proEtaleOrdinaryTensor Y (integralCoefficientCommRingSheaf l E Y n)).obj M).obj N) U
          (proEtaleTensorPair Y (integralCoefficientCommRingSheaf l E Y n) M N
            (Opposite.op U) m t)) =
      proEtaleTensorPair X (integralCoefficientCommRingSheaf l E X n)
        ((ordinary l E f n).obj M) ((ordinary l E f n).obj N)
        (Opposite.op ((proEtaleBaseChange f).obj U))
        (unit l E f n M U m) (unit l E f n N U t) :=
  (proEtaleOrdinaryTensorPullback_existsUnique f
    (integralCoefficientCommRingSheaf l E Y n) (integralCoefficientCommRingSheaf l E X n)
    (pullbackTensorCoefficientIso l E f n)).exists.choose_spec.2 M N U m t

attribute [local irreducible] moduleComp proEtaleOrdinaryTensorPullback
  SheafOfModules.monoidalCategory

private theorem pair_map (W : Scheme.{u}) (n : ℕ)
    {M M' N N' : normalizedDVRModules l E W n} (a : M ⟶ M') (b : N ⟶ N')
    (V : W.ProEtᵒᵖ) (m : M.val.obj V) (t : N.val.obj V) :
    ((SheafOfModules.monoidalCategory (integralCoefficientCommRingSheaf l E W n)).tensorHom
      a b).val.app V
        (proEtaleTensorPair W (integralCoefficientCommRingSheaf l E W n) M N V m t) =
      proEtaleTensorPair W (integralCoefficientCommRingSheaf l E W n) M' N' V
        (a.val.app V m) (b.val.app V t) := by
  exact SheafOfModules.ScalarHomOrdinary.pure_map
    (integralCoefficientCommRingSheaf l E W n) a b V m t

private theorem module_composition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Z ⟶ X)
    (n : ℕ) (M N : normalizedDVRModules l E Y n) :
    (mu l E (h ≫ f) n M N).hom ≫
        (SheafOfModules.monoidalCategory (integralCoefficientCommRingSheaf l E Z n)).tensorHom
          ((moduleComp l E f h n).hom.app M) ((moduleComp l E f h n).hom.app N) =
      (moduleComp l E f h n).hom.app
        (((proEtaleOrdinaryTensor Y (integralCoefficientCommRingSheaf l E Y n)).obj M).obj N) ≫
        (ordinary l E h n).map (mu l E f n M N).hom ≫
          (mu l E h n ((ordinary l E f n).obj M) ((ordinary l E f n).obj N)).hom := by
  apply ((proEtaleRingModuleAdjunction (h ≫ f)
    (integralCoefficientCommRingSheaf l E Y n) (integralCoefficientCommRingSheaf l E Z n)
    (pullbackTensorCoefficientIso l E (h ≫ f) n)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply modelTensor_hom_ext Y (integralCoefficientCommRingSheaf l E Y n)
  intro U m t
  change
    ((SheafOfModules.monoidalCategory (integralCoefficientCommRingSheaf l E Z n)).tensorHom
      ((moduleComp l E f h n).hom.app M) ((moduleComp l E f h n).hom.app N)).val.app _
      ((mu l E (h ≫ f) n M N).hom.val.app _
        (unit l E (h ≫ f) n _ U.unop
          (proEtaleTensorPair Y (integralCoefficientCommRingSheaf l E Y n) M N U m t))) =
    (mu l E h n ((ordinary l E f n).obj M) ((ordinary l E f n).obj N)).hom.val.app _
      (((ordinary l E h n).map (mu l E f n M N).hom).val.app _
        (((moduleComp l E f h n).hom.app _).val.app _
          (unit l E (h ≫ f) n _ U.unop
            (proEtaleTensorPair Y (integralCoefficientCommRingSheaf l E Y n) M N U m t))))
  simp only [Functor.op_obj, Opposite.op_unop]
  rw [mu_unit l E (h ≫ f) n M N U.unop m t]
  rw [pair_map]
  rw [moduleComp_unit, moduleComp_unit, moduleComp_unit]
  rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply]
  simp only [Functor.comp_obj]
  rw [unit_naturality, mu_unit, mu_unit]
  exact (modelTensorPair_restriction Z (integralCoefficientCommRingSheaf l E Z n)
    ((ordinary l E h n).obj ((ordinary l E f n).obj M))
    ((ordinary l E h n).obj ((ordinary l E f n).obj N))
    ((baseComp h f).hom.app U.unop).op _ _).symm

private theorem module_composition_inv {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Z ⟶ X)
    (n : ℕ) (M N : normalizedDVRModules l E Y n) :
    (SheafOfModules.monoidalCategory (integralCoefficientCommRingSheaf l E Z n)).tensorHom
        ((moduleComp l E f h n).hom.app M) ((moduleComp l E f h n).hom.app N) ≫
        (mu l E h n ((ordinary l E f n).obj M) ((ordinary l E f n).obj N)).inv ≫
        (ordinary l E h n).map (mu l E f n M N).inv =
      (mu l E (h ≫ f) n M N).inv ≫ (moduleComp l E f h n).hom.app
        (((proEtaleOrdinaryTensor Y (integralCoefficientCommRingSheaf l E Y n)).obj M).obj N) :=
    by
  apply (cancel_epi (mu l E (h ≫ f) n M N).hom).1
  rw [← Category.assoc, ← Category.assoc, module_composition]
  simp only [Category.assoc, Iso.hom_inv_id,
    Iso.hom_inv_id_assoc, ← Functor.map_comp, Category.comp_id]
  rw [(ordinary l E h n).map_id]
  simpa only [Functor.comp_obj] using Category.comp_id ((moduleComp l E f h n).hom.app
    (((proEtaleOrdinaryTensor Y (integralCoefficientCommRingSheaf l E Y n)).obj M).obj N))

attribute [local instance] modules_abelian ordinary_additive
attribute [local implicit_reducible] modules_abelian
attribute [local semireducible] pull
attribute [local implicit_reducible] pull Functor.map₂HomologicalComplex

private theorem complexComp_f {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Z ⟶ X)
    (n : ℕ) (P : CochainComplex (normalizedDVRModules l E Y n) ℤ) (i : ℤ) :
    ((complexComp l E f h n).hom.app P).f i =
      (moduleComp l E f h n).hom.app (P.X i) := by
  simp only [complexComp, id_eq, Iso.symm_hom,
    Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.symm_inv]

private instance tensor_additive (W : Scheme.{u}) (n : ℕ) :
    (proEtaleOrdinaryTensor W (integralCoefficientCommRingSheaf l E W n)).Additive := by
  let := SheafOfModules.monoidalCategory (integralCoefficientCommRingSheaf l E W n)
  let := proEtaleTensorPreadditive W (integralCoefficientCommRingSheaf l E W n)
  exact inferInstance

private instance tensor_obj_additive (W : Scheme.{u}) (n : ℕ)
    (M : normalizedDVRModules l E W n) :
    ((proEtaleOrdinaryTensor W (integralCoefficientCommRingSheaf l E W n)).obj M).Additive := by
  let := SheafOfModules.monoidalCategory (integralCoefficientCommRingSheaf l E W n)
  let := proEtaleTensorPreadditive W (integralCoefficientCommRingSheaf l E W n)
  exact inferInstance

attribute [local instance high] tensor_additive tensor_obj_additive

private instance tensor_zero (W : Scheme.{u}) (n : ℕ) :
    (proEtaleOrdinaryTensor W
      (integralCoefficientCommRingSheaf l E W n)).PreservesZeroMorphisms := by
  exact Functor.preservesZeroMorphisms_of_additive _

private instance tensor_obj_zero (W : Scheme.{u}) (n : ℕ)
    (M : normalizedDVRModules l E W n) :
    ((proEtaleOrdinaryTensor W
      (integralCoefficientCommRingSheaf l E W n)).obj M).PreservesZeroMorphisms := by
  exact Functor.preservesZeroMorphisms_of_additive _

attribute [local instance high] tensor_zero tensor_obj_zero

private abbrev mapTotal (W : Scheme.{u}) (n : ℕ)
    {P P' Q Q' : CochainComplex (normalizedDVRModules l E W n) ℤ}
    (a : P ⟶ P') (b : Q ⟶ Q') :=
  @HomologicalComplex.mapBifunctorMap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a b
    (proEtaleOrdinaryTensor W (integralCoefficientCommRingSheaf l E W n))
    (tensor_zero l E W n) (tensor_obj_zero l E W n) (.up ℤ) _ _ _ _

private theorem totalTensor_map (W : Scheme.{u}) (n : ℕ)
    {P P' Q Q' : CochainComplex (normalizedDVRModules l E W n) ℤ}
    (a : P ⟶ P') (b : Q ⟶ Q') :
    (totalTensor l E W n).map (Prod.mkHom a b) = mapTotal l E W n a b := by
  change mapTotal l E W n a (𝟙 Q) ≫ mapTotal l E W n (𝟙 P') b = _
  simp only [mapTotal, HomologicalComplex.mapBifunctorMap,
    ← HomologicalComplex₂.total.map_comp]
  let T := (proEtaleOrdinaryTensor W
    (integralCoefficientCommRingSheaf l E W n)).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)
  have h₁ := congrArg (fun t ↦ t.app Q) (T.map_id P')
  have h₂ := (T.obj P').map_id Q
  rw [h₁, h₂]
  rfl

@[irreducible] private def kappa {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P Q : CochainComplex (normalizedDVRModules l E Y n) ℤ) :
    tensor l E X n ((pull l E f n).obj P) ((pull l E f n).obj Q) ≅
      (pull l E f n).obj (tensor l E Y n P Q) :=
  proEtaleTensorPullbackTotalIso f (integralCoefficientCommRingSheaf l E Y n)
    (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n) P Q

attribute [local instance] modules_abelian ordinary_additive
attribute [local implicit_reducible] totalTensor

private theorem comparison_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P Q : CochainComplex (normalizedDVRModules l E Y n) ℤ) :
    comparison l E f n P Q = (kappa l E f n P Q).inv := by
  unfold comparison kappa
  rfl

private def inclusion (W : Scheme.{u}) (n : ℕ)
    (P Q : CochainComplex (normalizedDVRModules l E W n) ℤ) (i j k : ℤ)
    (hij : ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) (i, j) = k) :
    ((proEtaleOrdinaryTensor W (integralCoefficientCommRingSheaf l E W n)).obj
      (P.X i)).obj (Q.X j) ⟶ (tensor l E W n P Q).X k :=
  @HomologicalComplex.ιMapBifunctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ P Q
    (proEtaleOrdinaryTensor W (integralCoefficientCommRingSheaf l E W n))
    (tensor_zero l E W n) (tensor_obj_zero l E W n) (.up ℤ) _ _ _ i j k hij

private theorem inclusion_mapTotal (W : Scheme.{u}) (n : ℕ)
    {P P' Q Q' : CochainComplex (normalizedDVRModules l E W n) ℤ}
    (a : P ⟶ P') (b : Q ⟶ Q') (i j k : ℤ)
    (hij : ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) (i, j) = k) :
    inclusion l E W n P Q i j k hij ≫ (mapTotal l E W n a b).f k =
      (SheafOfModules.monoidalCategory (integralCoefficientCommRingSheaf l E W n)).tensorHom
        (a.f i) (b.f j) ≫ inclusion l E W n P' Q' i j k hij := by
  let := SheafOfModules.monoidalCategory (integralCoefficientCommRingSheaf l E W n)
  simp only [inclusion, mapTotal, HomologicalComplex.ι_mapBifunctorMap,
    MonoidalCategory.tensorHom_def, Category.assoc]
  rfl

@[reassoc] private theorem inclusion_kappa {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P Q : CochainComplex (normalizedDVRModules l E Y n) ℤ) (i j k : ℤ)
    (hij : ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) (i, j) = k) :
    inclusion l E X n ((pull l E f n).obj P) ((pull l E f n).obj Q) i j k hij ≫
        (kappa l E f n P Q).hom.f k =
      (mu l E f n (P.X i) (Q.X j)).inv ≫
        (ordinary l E f n).map (inclusion l E Y n P Q i j k hij) := by
  simp only [inclusion, kappa, proEtaleTensorPullbackTotalIso, asIso_hom,
    proEtaleTensorPullbackTotal, tensorPullbackTotal, tensorPullbackTotalComponent,
    pull, Functor.mapHomologicalComplex_obj_X, HomologicalComplex.ι_mapBifunctorDesc]

private theorem total_composition_inv {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Z ⟶ X)
    (n : ℕ) (P Q : CochainComplex (normalizedDVRModules l E Y n) ℤ) :
    (totalTensor l E Z n).map (Prod.mkHom
        ((complexComp l E f h n).hom.app P) ((complexComp l E f h n).hom.app Q)) ≫
        (kappa l E h n ((pull l E f n).obj P) ((pull l E f n).obj Q)).hom ≫
        (pull l E h n).map (kappa l E f n P Q).hom =
      (kappa l E (h ≫ f) n P Q).hom ≫
        (complexComp l E f h n).hom.app (tensor l E Y n P Q) := by
  rw [totalTensor_map]
  apply HomologicalComplex.Hom.ext
  funext k
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  simp only [HomologicalComplex.comp_f]
  change inclusion l E Z n ((pull l E (h ≫ f) n).obj P)
      ((pull l E (h ≫ f) n).obj Q) i j k hij ≫ _ =
    inclusion l E Z n ((pull l E (h ≫ f) n).obj P)
      ((pull l E (h ≫ f) n).obj Q) i j k hij ≫ _
  rw [← Category.assoc, inclusion_mapTotal, Category.assoc]
  simp only [Functor.comp_obj]
  rw [inclusion_kappa_assoc, inclusion_kappa_assoc]
  simp only [complexComp_f, pull, Functor.mapHomologicalComplex_map_f,
    Functor.mapHomologicalComplex_obj_X]
  rw [← (ordinary l E h n).map_comp]
  erw [inclusion_kappa l E f n P Q i j k hij]
  rw [(ordinary l E h n).map_comp]
  have hm := congrArg (fun t ↦ t ≫
    (ordinary l E h n).map ((ordinary l E f n).map (inclusion l E Y n P Q i j k hij)))
    (module_composition_inv l E f h n (P.X i) (Q.X j))
  have hn := congrArg (fun t ↦ (mu l E (h ≫ f) n (P.X i) (Q.X j)).inv ≫ t)
    ((moduleComp l E f h n).hom.naturality
      (inclusion l E Y n P Q i j k hij)).symm
  calc
    _ = (mu l E (h ≫ f) n (P.X i) (Q.X j)).inv ≫
        (moduleComp l E f h n).hom.app
          (((proEtaleOrdinaryTensor Y (integralCoefficientCommRingSheaf l E Y n)).obj
            (P.X i)).obj (Q.X j)) ≫
        (ordinary l E h n).map ((ordinary l E f n).map (inclusion l E Y n P Q i j k hij)) := by
      simpa only [Category.assoc] using hm
    _ = _ := by simpa only [Category.assoc, Functor.comp_map] using hn

/-- The ordinary total comparison respects the unit-normalized pullback compositor.
Source: Stacks, Modules on Sites 03EL, Sites 00YV, and Cohomology on Sites 07A4
(blueprint: lem-pur-finite-pullback-tensor-chain-composition).

Proof: first work with two sheaves of modules. The defining unit-section formula
for proEtaleOrdinaryTensorPullback sends the unit of a pure tensor to the tensor
of its two units. The realization maps in moduleComp preserve precisely these
adjunction-unit sections. The fixed-scalar compositor is the comparison of the
composite adjunctions, and inserts their composite unit. Consequently both routes
send a unit section of m tensor n to the tensor of the two iterated unit sections,
with the same fibre-product identification of test objects. Apply the adjunction
hom-equivalence to the two candidate maps out of composite pullback. Maps from
the sheaf tensor are determined by pure tensors: the tensor universal property
proves this before sheafification, and the sheafification adjunction proves it
afterwards. Thus the two module maps agree. Invert this square. For complexes,
precompose in degree k with each source direct-sum injection indexed by i+j=k.
The total comparison acts on that summand by the inverse ordinary module
comparison followed by the pullback of its inclusion. The termwise compositor
is moduleComp in each degree. The inverse module square and naturality of
moduleComp on the inclusion identify both summand maps. Coproduct and complex
morphism extensionality prove the inverse total square; cancellation of the
three total comparison isomorphisms gives the stated equation. The existing
chain maps already respect the signed differentials.
No flatness, boundedness or derived localization is used. -/
theorem chain_composition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Z ⟶ X) (n : ℕ)
    (P Q : CochainComplex (normalizedDVRModules l E Y n) ℤ) :
    comparison l E (h ≫ f) n P Q ≫
      (totalTensor l E Z n).map (Prod.mkHom
        ((complexComp l E f h n).hom.app P) ((complexComp l E f h n).hom.app Q)) =
    (complexComp l E f h n).hom.app (tensor l E Y n P Q) ≫
      (pull l E h n).map (comparison l E f n P Q) ≫
      comparison l E h n ((pull l E f n).obj P) ((pull l E f n).obj Q) := by
  simp only [comparison_eq]
  apply (cancel_epi (kappa l E (h ≫ f) n P Q).hom).1
  apply (cancel_mono
    (kappa l E h n ((pull l E f n).obj P) ((pull l E f n).obj Q)).hom).1
  apply (cancel_mono ((pull l E h n).map (kappa l E f n P Q).hom)).1
  simp only [Category.assoc, Iso.hom_inv_id_assoc,
    ← Functor.map_comp, Iso.inv_hom_id, Category.comp_id]
  rw [(pull l E h n).map_id]
  have hid := congrArg (fun t ↦ (kappa l E (h ≫ f) n P Q).hom ≫ t)
    (Category.comp_id ((complexComp l E f h n).hom.app (tensor l E Y n P Q)))
  exact (total_composition_inv l E f h n P Q).trans
    (by simpa only [Functor.comp_obj] using hid.symm)

end WeilConjectures.FinitePullbackTensorRep
