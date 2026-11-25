/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletedTensorReindex.PodCompletionTensorModels
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement

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

section RestrictionProof

attribute [local implicit_reducible] integralCoefficientCommRingSheaf integralCoefficientSheaf
  sheafCompose PresheafOfModules.presheaf SheafOfModules.changeOfRingsPresheaf
  completedIntegralCommRingSheafUnrestricted ModuleCat.extendScalars ModuleCat.ExtendScalars.obj'

private theorem reduction_section_restrict (W : Scheme.{u}) (n : ℕ)
    (M : integralTowerModules l E W) {U V : W.ProEtᵒᵖ} (f : U ⟶ V)
    (x : M.val.obj U) :
    ((unrestrictedIntegralReductionFunctor l E W n).obj M).val.map f
        (unrestrictedIntegralTensorSection l E W n M U 1 x) =
      unrestrictedIntegralTensorSection l E W n M V 1 (M.val.map f x) := by
  unfold unrestrictedIntegralTensorSection
  erw [← PresheafOfModules.naturality_apply]
  have h := ConcreteCategory.congr_hom
    ((toSheafify (ProEt.topology W)
      (SheafOfModules.changeOfRingsPresheaf
        (completedIntegralCommRingProjectionUnrestricted l E W n) M).presheaf).naturality f)
    ((1 : (integralCoefficientCommRingSheaf l E W n).obj.obj U)
      ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E W).obj.obj U,
        ((completedIntegralCommRingProjectionUnrestricted l E W n).hom.app U).hom] x)
  simp only [ConcreteCategory.comp_apply] at h
  have ht :
      (SheafOfModules.changeOfRingsPresheaf
        (completedIntegralCommRingProjectionUnrestricted l E W n) M).presheaf.map f
        ((1 : (integralCoefficientCommRingSheaf l E W n).obj.obj U)
          ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E W).obj.obj U,
            ((completedIntegralCommRingProjectionUnrestricted l E W n).hom.app U).hom] x) =
      (integralCoefficientCommRingSheaf l E W n).obj.map f 1
        ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E W).obj.obj V,
          ((completedIntegralCommRingProjectionUnrestricted l E W n).hom.app V).hom]
            M.val.map f x := by
    exact SheafOfModules.UnrestrictedTowerProof.restriction_tmul
      (completedIntegralCommRingProjectionUnrestricted l E W n) M f 1 x
  rw [ht, map_one] at h
  exact congrArg ((eqToHom
    ((scalarReductionExistence l E W n).choose_spec.choose M).symm).val.app V) h.symm

private theorem total_section_restrict (W : Scheme.{u}) (n : ℕ)
    (P Q : CochainComplex (integralTowerModules l E W) ℤ)
    (p q : ℤ) {U V : W.ProEtᵒᵖ} (f : U ⟶ V)
    (x : (((unrestrictedIntegralFiniteComplex l E W n).obj P).X p).val.obj U)
    (y : (((unrestrictedIntegralFiniteComplex l E W n).obj Q).X q).val.obj U) :
    (((integralOperationsTensorLevel l E W n).obj (P, Q)).X (p + q)).val.map f
        (integralOperationsTotalTensorSection l E W n P Q p q U x y) =
      integralOperationsTotalTensorSection l E W n P Q p q V
        ((((unrestrictedIntegralFiniteComplex l E W n).obj P).X p).val.map f x)
        ((((unrestrictedIntegralFiniteComplex l E W n).obj Q).X q).val.map f y) := by
  unfold integralOperationsTotalTensorSection integralOperationsTensorSection
  erw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply]
  have h := ConcreteCategory.congr_hom
    ((toSheafify (ProEt.topology W)
      ((MonoidalCategory.tensorObj
        (((unrestrictedIntegralFiniteComplex l E W n).obj P).X p).val
        (((unrestrictedIntegralFiniteComplex l E W n).obj Q).X q).val).presheaf)).naturality f)
    (x ⊗ₜ[(integralCoefficientCommRingSheaf l E W n).obj.obj U] y)
  simp only [ConcreteCategory.comp_apply] at h
  erw [PresheafOfModules.Monoidal.tensorObj_map_tmul] at h
  exact congrArg _ (congrArg _ h.symm)

end RestrictionProof

attribute [local irreducible] integralOperationsTotalTensorSection
  unrestrictedIntegralTensorSection

private theorem total_unit_restrict (W : Scheme.{u}) (n : ℕ)
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (p q : ℤ)
    {U V : W.ProEtᵒᵖ} (f : U ⟶ V)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    (((integralOperationsTensorLevel l E W n).obj (P, Q)).X (p + q)).val.map f
        (integralOperationsTotalTensorSection l E W n P Q p q U
          (unrestrictedIntegralTensorSection l E W n (P.X p) U 1 x)
          (unrestrictedIntegralTensorSection l E W n (Q.X q) U 1 y)) =
      integralOperationsTotalTensorSection l E W n P Q p q V
        (unrestrictedIntegralTensorSection l E W n (P.X p) V 1 ((P.X p).val.map f x))
        (unrestrictedIntegralTensorSection l E W n (Q.X q) V 1 ((Q.X q).val.map f y)) := by
  exact (total_section_restrict l E W n P Q p q f
    (unrestrictedIntegralTensorSection l E W n (P.X p) U 1 x)
    (unrestrictedIntegralTensorSection l E W n (Q.X q) U 1 y)).trans
    (congrArg₂ (fun s t ↦ integralOperationsTotalTensorSection l E W n P Q p q V s t)
      (reduction_section_restrict l E W n (P.X p) f x)
      (reduction_section_restrict l E W n (Q.X q) f y))

/-- Ordinary identity relabelling preserves total tensors of unit reduction sections.
Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 07A4 and 0941 (blueprint: lem-pod-identity-tensor-unit-sections).

Proof: the given section equation for ordinary identity relabelling is restriction
along Over.mapId. Naturality of the reduction sheafification unit sends 1 tensor x
to 1 tensor the restriction of x, since restriction preserves one. Naturality of
the tensor sheafification unit and of the total-summand injection sends a total
pure tensor to the total tensor of its restrictions. Combining these equations
with the section equation gives the result in every pair of degrees. -/
theorem podIdentityTensorUnitSections (W : Scheme.{u}) (n : ℕ)
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (p q : ℤ) (U : W.ProEt)
    (a : isoReductionIntegralInverse l E (𝟙 W) ≅ 𝟭 _)
    (ha : ∀ (M : scalarReductionSource l E W) (V : W.ProEt)
      (x : M.val.obj (op ((proEtaleIsoPostcompose (𝟙 W)).obj V))),
      (a.hom.app M).val.app (op V) x =
        M.val.map ((MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ W
          (𝟙 W) rfl).hom.app V).op x)
    (x : (P.X p).val.obj (op ((proEtaleIsoPostcompose (𝟙 W)).obj U)))
    (y : (Q.X q).val.obj (op ((proEtaleIsoPostcompose (𝟙 W)).obj U))) :
    (a.hom.app (((integralOperationsTensorLevel l E W n).obj (P, Q)).X (p + q))).val.app
        (op U) (integralOperationsTotalTensorSection l E W n P Q p q
          (op ((proEtaleIsoPostcompose (𝟙 W)).obj U))
          (unrestrictedIntegralTensorSection l E W n (P.X p)
            (op ((proEtaleIsoPostcompose (𝟙 W)).obj U)) 1 x)
          (unrestrictedIntegralTensorSection l E W n (Q.X q)
            (op ((proEtaleIsoPostcompose (𝟙 W)).obj U)) 1 y)) =
      integralOperationsTotalTensorSection l E W n P Q p q (op U)
        (unrestrictedIntegralTensorSection l E W n (P.X p) (op U) 1
          ((P.X p).val.map ((MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ W
            (𝟙 W) rfl).hom.app U).op x))
        (unrestrictedIntegralTensorSection l E W n (Q.X q) (op U) 1
          ((Q.X q).val.map ((MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ W
            (𝟙 W) rfl).hom.app U).op y)) := by
  exact (ha (((integralOperationsTensorLevel l E W n).obj (P, Q)).X (p + q)) U _).trans
    (total_unit_restrict l E W n P Q p q
      ((MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ W (𝟙 W) rfl).hom.app U).op x y)

end WeilConjectures
