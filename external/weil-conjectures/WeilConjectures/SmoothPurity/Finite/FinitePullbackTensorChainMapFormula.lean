/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorChainGenerators
public import WeilConjectures.SmoothPurity.FinitePullbackTensorRep.FinitePullbackTensorRepresentativeData

/-! # The chain map of the intrinsic tensor comparison

Source: Stacks Tags 03EL, 06YY and 07A4.
(blueprint: lem-pur-finite-pullback-tensor-chain-map-formula).
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

/-- The underlying map of the explicit intrinsic chain isomorphism.
Source: Stacks 03EL and 07A4
(blueprint: lem-pur-finite-pullback-tensor-chain-map-formula).
Proof: the isomorphism is defined as the inverse realization on the total tensor,
the inverse ordinary total comparison, and the tensor of the two realizations.
Taking its hom gives precisely this threefold composite. -/
theorem finitePullbackTensorChainIso_hom {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P Q : CochainComplex (normalizedDVRModules l E Y n) ℤ) :
    letI : (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).Additive :=
      sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
    let e := NatIso.mapHomologicalComplex (pullbackTensorFiniteRealization l E f n) (.up ℤ)
    (finitePullbackTensorChainIso l E f n P Q).hom =
      e.inv.app ((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology Y)
        (integralCoefficientCommRingSheaf l E Y n)).obj (P, Q)) ≫
      FinitePullbackTensorRep.comparison l E f n P Q ≫
      (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n)).map
          (Prod.mkHom (e.hom.app P) (e.hom.app Q)) := by
  unfold finitePullbackTensorChainIso FinitePullbackTensorRep.comparison
  rfl

end WeilConjectures
