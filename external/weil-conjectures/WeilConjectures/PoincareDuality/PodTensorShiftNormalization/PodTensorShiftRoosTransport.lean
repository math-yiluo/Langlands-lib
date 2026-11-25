/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexShifts

import WeilConjectures.PoincareDuality.PodTensorShiftNormalization.PodTensorShiftNaturality

/-! # Proved calculations for tensor-shift path normalization

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 011G, 07A4, 0941
(blueprint: lem-pod-tensor-shift-roos-transport-t5).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
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
  WeilConjectures.podReindexCalculus

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodTensorShiftNormalization

attribute [local irreducible] integralOperationsTensorTowerFunctor
attribute [local implicit_reducible] podOrdinaryReindex podShiftTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section Presentations
variable {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]

attribute [local irreducible] integralOperationsRoos

-- Share the normalized categorical expressions without unfolding coefficient constructions.
/-- Transport a source signed Roos shift through reindexing and a tower morphism.
Use comparison naturality and CommShift, RoosNaturality, RoosShift, and signed-shift naturality.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 011G, 07A4, 0941
(blueprint: lem-pod-tensor-shift-roos-transport-t5). -/
theorem roos_path_shift
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    {C C' : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E Y) ℤ}
    {B : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E X) ℤ}
    (r : ℤ) (s : C' ⟶ podShiftTower C r)
    (t : (podReindexTower l E g).obj C ⟶ B) :
    letI : (isoReductionIntegralInverse l E g).Additive :=
      isoSectionwiseModuleInverseImage_additive.{u, u} g (isoReductionCompletedMap l E g).hom
    letI : PreservesFiniteLimits (isoReductionIntegralInverse l E g) :=
      isoSectionwiseModuleInverseImage_limits.{u, u} g (isoReductionCompletedMap l E g).hom
    letI : PreservesFiniteColimits (isoReductionIntegralInverse l E g) :=
      isoSectionwiseModuleInverseImage_colimits.{u, u} g (isoReductionCompletedMap l E g).hom
    let F := podOrdinaryReindex l E g
    let φ := (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors
    F.map (DerivedCategory.Q.map (integralOperationsRoosMap s)) ≫
      F.map (DerivedCategory.Q.map (D.shiftSource.comparison C r).hom) ≫
      F.map ((DerivedCategory.Q.commShiftIso r).hom.app _) ≫
      (F.commShiftIso r).hom.app _ ≫
      (φ.hom.app (integralOperationsRoos C))⟦r⟧' ≫
      (DerivedCategory.Q.map (D.roos C).hom)⟦r⟧' ≫
      (DerivedCategory.Q.map (integralOperationsRoosMap t))⟦r⟧' =
    φ.hom.app _ ≫ DerivedCategory.Q.map (D.roos C').hom ≫
      DerivedCategory.Q.map (integralOperationsRoosMap
        ((podReindexTower l E g).map s ≫ (podTowerShift l E g C r).hom ≫
          whiskerRight t (shiftFunctor _ r))) ≫
      DerivedCategory.Q.map (D.shiftTarget.comparison B r).hom ≫
      (DerivedCategory.Q.commShiftIso r).hom.app _ := by
  dsimp only [podOrdinaryReindex, isoReductionIntegralComplex, Functor.comp_obj] at *
  let : (isoReductionIntegralInverse l E g).Additive :=
    isoSectionwiseModuleInverseImage_additive.{u, u} g (isoReductionCompletedMap l E g).hom
  let : PreservesFiniteLimits (isoReductionIntegralInverse l E g) :=
    isoSectionwiseModuleInverseImage_limits.{u, u} g (isoReductionCompletedMap l E g).hom
  let : PreservesFiniteColimits (isoReductionIntegralInverse l E g) :=
    isoSectionwiseModuleInverseImage_colimits.{u, u} g (isoReductionCompletedMap l E g).hom
  have hn := hD.2.2.2.2.2.2.2.2.2.2.2.2.1 C' (podShiftTower C r) s
  have hs := hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 C r
  have ht := signed_roos_naturality D.shiftTarget
    hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 t r
  have hc := NatTrans.shift_app_comm
    (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom r
    (integralOperationsRoos C)
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hc
  simp only [integralOperationsRoosMap_comp, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hc]
  rw [(isoReductionIntegralInverse l E g).mapDerivedCategoryFactors_hom_naturality_assoc]
  rw [(isoReductionIntegralInverse l E g).mapDerivedCategoryFactors_hom_naturality_assoc]
  rw [← DerivedCategory.Q.commShiftIso_hom_naturality_assoc]
  have hsq := congrArg DerivedCategory.Q.map hs
  have hnq := congrArg DerivedCategory.Q.map hn
  have htq := congrArg DerivedCategory.Q.map ht
  simp only [Functor.map_comp] at hsq hnq htq
  rw [← reassoc_of% hsq, reassoc_of% hnq]
  rw [← DerivedCategory.Q.commShiftIso_hom_naturality]
  rw [← reassoc_of% htq]

end Presentations
end WeilConjectures.PodTensorShiftNormalization
