/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FinitePullbackTensorRep.FinitePullbackTensorRepresentativeData

/-! # The derived factorization identity for finite realization

Source: Stacks Tags 03EL, 06YY and 07A4.
(blueprint: lem-pur-finite-pullback-tensor-realization-factors).
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

attribute [local instance] FinitePullbackTensorRep.modules_abelian
  FinitePullbackTensorRep.modules_derived FinitePullbackTensorRep.ordinary_additive
  FinitePullbackTensorRep.ordinary_limits FinitePullbackTensorRep.ordinary_colimits
attribute [local implicit_reducible] FinitePullbackTensorRep.modules_abelian
  FinitePullbackTensorRep.modules_derived
attribute [local semireducible] FinitePullbackTensorRep.pull
attribute [local implicit_reducible] FinitePullbackTensorRep.pull
  coefficientFiniteInternalHom
attribute [local implicit_reducible] finiteIntrinsicDerivedTensor coefficientTotalTensor
  FinitePullbackTensorRep.totalTensor

/-- The intrinsic derived factor is the ordinary factor followed by the localized
finite realization. Source: Stacks 07A4
(blueprint: lem-pur-finite-pullback-tensor-realization-factors).
Proof: expand the definition of the ordinary-coordinate factor. Compatibility of
derived natural isomorphisms with their localization factors identifies the
ordinary factor followed by the localized realization with the derived realization
followed by the intrinsic factor. Cancel the inverse derived realization. -/
theorem finitePullbackTensor_realization_factors {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P : CochainComplex (normalizedDVRModules l E Y n) ℤ) :
    letI : (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).Additive :=
      sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
    (FinitePullbackTensorRep.factors l E f n).hom.app P ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (pullbackTensorFiniteRealization l E f n)
          (.up ℤ)).hom.app P) =
    (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).mapDerivedCategoryFactors.hom.app
      P := by
  let : (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).Additive :=
    sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
  let := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f
  let := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f
  have h := Functor.mapDerivedCategoryNatIso_fac (pullbackTensorFiniteRealization l E f n) P
  unfold FinitePullbackTensorRep.factors FinitePullbackTensorRep.realization
  change ((Functor.mapDerivedCategoryNatIso (pullbackTensorFiniteRealization l E f n)).inv.app
      (DerivedCategory.Q.obj P) ≫
    (FinitePullbackTensorRep.ordinaryFactors l E f n).hom.app P) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (pullbackTensorFiniteRealization l E f n).hom
          (.up ℤ)).app P) = _
  rw [Category.assoc]
  erw [← h]
  exact Iso.inv_hom_id_app_assoc _ _ _

end WeilConjectures
