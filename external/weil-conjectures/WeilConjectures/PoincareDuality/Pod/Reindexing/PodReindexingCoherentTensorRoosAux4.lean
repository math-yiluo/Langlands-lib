/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingCoherentTensorRoosAux3
public import WeilConjectures.SmoothPurity.ScalarExtensionTower.StrictQuotientTensorGenerator
public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSectionsScalarHomZeroCycleClosed

/-! # Section formulas for the strict tensor tower comparison

The reference strict tower comparison of the coherent system tensor and the finite tensor
tower sends the restricted generator of two unit-inserted reduced sections to the total
tensor of the unit-inserted sections.

Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 03EK, 07A4, 0941
(blueprint: stage3-pod-reindexing-coherent-tensor-roos).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The reduction of a unit-inserted section, read as a section of the coherent reduction.
Source: Stacks 06YY, 0941. -/
abbrev podReducedUnitSection (W : Scheme.{u}) (n : ℕ) (M : integralTowerModules l E W)
    (V : W.ProEt) (x : M.val.obj (op V)) :
    ((pullbackTensorOrdinaryReduction l E W).obj M).val.obj (op (n, V)) :=
  ((pullbackTensorReductionEvaluation l E W n).hom.app M).val.app (op V)
    (unrestrictedIntegralTensorSection l E W n M (op V) 1 x)

/-- Degreewise, the inverse complex-level reduction evaluation is the termwise inverse.
Source: Stacks 0941. -/
theorem podReductionEvaluationComplex_inv_f (W : Scheme.{u}) (n : ℕ)
    (C : CochainComplex (integralTowerModules l E W) ℤ) (k : ℤ) :
    ((pullbackTensorReductionEvaluationComplex l E W n).inv.app C).f k =
      (pullbackTensorReductionEvaluation l E W n).inv.app (C.X k) := by
  simp only [pullbackTensorReductionEvaluationComplex, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_inv_app_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f, Iso.refl_hom, NatTrans.id_app]
  exact Category.id_comp _

/-- The inverse reduction evaluation recovers a unit-inserted section.
Source: Stacks 06YY, 0941. -/
theorem podReducedUnitSection_inv (W : Scheme.{u}) (n : ℕ) (M : integralTowerModules l E W)
    (V : W.ProEt) (x : M.val.obj (op V)) :
    (((pullbackTensorReductionEvaluation l E W n).inv.app M).val.app (op V))
        (coefficientEvaluationSection l E W ((pullbackTensorOrdinaryReduction l E W).obj M) n
          (op V) (podReducedUnitSection l E W n M V x)) =
      unrestrictedIntegralTensorSection l E W n M (op V) 1 x := by
  have he : coefficientEvaluationSection l E W ((pullbackTensorOrdinaryReduction l E W).obj M) n
      (op V) (podReducedUnitSection l E W n M V x) = podReducedUnitSection l E W n M V x := rfl
  rw [he]
  exact congrArg (fun f ↦ f.val.app (op V) (unrestrictedIntegralTensorSection l E W n M (op V) 1 x))
    ((pullbackTensorReductionEvaluation l E W n).hom_inv_id_app M)

/-- The reference strict tensor tower comparison on the restricted generator of two reduced
unit-inserted sections.
Source: Stacks 03EK, 07A4, 0941. -/
theorem pullbackTensorTensorTower_hom_reducedUnit (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) (p q : ℤ) (V : W.ProEt)
    (x : (P.X p).val.obj (op V)) (y : (Q.X q).val.obj (op V)) :
    (((pullbackTensorTensorTower l E W P Q).hom.app (op n)).f (p + q)).val.app (op V)
        (integralComparisonRestrictedSection l E W
          (((coefficientTotalTensor.{u, u + 1, u}
            (coefficientSequenceTopology (ProEt.topology W))
            (coefficientSequenceCommRingSheaf l E W)).obj
            (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P,
              ((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj Q)).X
              (p + q)) n (op V)
          (coefficientTensorGenerator.{u, u + 1, u}
            (coefficientSequenceTopology (ProEt.topology W))
            (coefficientSequenceCommRingSheaf l E W)
            (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P)
            (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj Q)
            p q (p + q) rfl (op (n, V))
            (podReducedUnitSection l E W n (P.X p) V x)
            (podReducedUnitSection l E W n (Q.X q) V y))) =
      integralOperationsTotalTensorSection l E W n P Q p q (op V)
        (unrestrictedIntegralTensorSection l E W n (P.X p) (op V) 1 x)
        (unrestrictedIntegralTensorSection l E W n (Q.X q) (op V) 1 y) := by
  have h := ScalarExtensionTower.strictQuotientTensorGenerator l E W P Q _ _
    (Iso.refl _) (Iso.refl _)
    (fun n ↦ ((pullbackTensorReductionEvaluationComplex l E W n).app P).symm)
    (fun n ↦ ((pullbackTensorReductionEvaluationComplex l E W n).app Q).symm)
    (fun n ↦ by
      ext1
      simp)
    (fun n ↦ by
      ext1
      simp)
  dsimp only at h
  have h' := h n p q (op V) (podReducedUnitSection l E W n (P.X p) V x)
    (podReducedUnitSection l E W n (Q.X q) V y)
  have hrefl : (Iso.refl (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex
      (.up ℤ)).obj P)).symm.prod
      (Iso.refl (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex
        (.up ℤ)).obj Q)).symm = Iso.refl _ := by
    ext <;> rfl
  simp only [hrefl, Functor.mapIso_refl, Iso.refl_trans] at h'
  refine h'.trans ?_
  unfold ScalarExtensionTower.integralTensorGenerator
  simp only [Iso.symm_hom, Iso.app_inv, podReductionEvaluationComplex_inv_f]
  exact congrArg₂ (integralOperationsTotalTensorSection l E W n P Q p q (op V))
    (podReducedUnitSection_inv l E W n (P.X p) V x) (podReducedUnitSection_inv l E W n (Q.X q) V y)

/-- Unit-inserted reduced sections are compatible with an equality of modules.
Source: Stacks 06YY. -/
theorem podReducedUnitSection_eqToHom (W : Scheme.{u}) {M N : scalarReductionSource l E W}
    (h : M = N) (n : ℕ) (U : W.ProEt) (x : M.val.obj (op U)) (y : N.val.obj (op U))
    (hxy : HEq x y) :
    ((pullbackTensorOrdinaryReduction l E W).map (eqToHom h)).val.app (op (n, U))
        (podReducedUnitSection l E W n M U x) = podReducedUnitSection l E W n N U y := by
  subst h
  obtain rfl := eq_of_heq hxy
  simp

set_option quotPrecheck false in
set_option hygiene false in
local notation "R[" W "]" =>
  (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
set_option quotPrecheck false in
set_option hygiene false in
local notation "I[" g "]" =>
  (integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)
set_option quotPrecheck false in
set_option hygiene false in
local notation "F[" g "]" => podReindexingComplexFunctor l E g none

/-- The transported unary chain model sends the restricted inverse-image unit of a reduced
unit-inserted section to the reduced unit-inserted section.
Source: Stacks 03D2, 06YY, 0941. -/
theorem podUnaryTransport_generator {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (β : (I[g]).obj ((R[Y]).obj P) ≅ (R[X]).obj ((F[g]).obj P))
    (hβ : PodReductionRepresentatives.Generators l E g P β) (n : ℕ) (i : ℤ) (U : X.ProEt)
    (x : (P.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    (((β ≪≫ (R[X]).mapIso (podReindexComplexIso l E g P)).hom.f i).val.app (op (n, U)))
        (((integralComparisonSequencePullback l E g).obj
            ((pullbackTensorOrdinaryReduction l E Y).obj (P.X i))).val.map
          (Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U)).op
          (integralComparisonSequenceGenerator.{u, u} l E g
            ((pullbackTensorOrdinaryReduction l E Y).obj (P.X i)) n
            ((proEtaleIsoPostcompose g).obj U)
            (podReducedUnitSection l E Y n (P.X i) ((proEtaleIsoPostcompose g).obj U) x))) =
      podReducedUnitSection l E X n (((isoReductionIntegralComplex l E g).obj P).X i) U x := by
  have hb := hβ n i U 1 x
  have h1 : (isoSectionwiseConstantMap.{u, u} g (CommRingCat.of
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).hom.app (op U) 1 =
      (1 : (integralCoefficientCommRingSheaf l E X n).obj.obj (op U)) := map_one _
  erw [h1] at hb
  simp only [Iso.trans_hom, HomologicalComplex.comp_f, Functor.mapIso_hom,
    Functor.mapHomologicalComplex_map_f, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ConcreteCategory.comp_apply]
  erw [hb]
  simp only [podReindexComplexIso, Iso.app_hom, NatIso.mapHomologicalComplex_hom_app_f,
    eqToIso.hom, eqToHom_app]
  exact podReducedUnitSection_eqToHom l E X (M := ((F[g]).obj P).X i)
    (N := ((isoReductionIntegralComplex l E g).obj P).X i) _ n U x x HEq.rfl

end WeilConjectures
