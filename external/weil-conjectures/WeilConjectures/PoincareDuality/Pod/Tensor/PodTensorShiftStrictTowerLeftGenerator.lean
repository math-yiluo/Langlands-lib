/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexShifts
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTensorLevelTower

/-! # Left tensor-shift calculation on generators -/

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
namespace WeilConjectures

attribute [local irreducible] integralOperationsRoos
attribute [local implicit_reducible] integralOperationsTensorTowerFunctor
attribute [local implicit_reducible] integralOperationsTensorOnGood
  integralOperationsTensorComplexFunctor integralOperationsGoodLocalization

attribute [local implicit_reducible] integralOperationsTensorLevel
  integralOperationsTensorComposite SheafOfModules.restrictScalars podGoodReindex
  podShiftTower Functor.ofOpSequence Functor.ofSequence
attribute [local implicit_reducible] Functor.map₂HomologicalComplex
attribute [local implicit_reducible] isoSectionwiseModuleInverseImage
  SheafOfModules.pushforward PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀ PresheafOfModules.pushforward₀Obj
  PresheafOfModules.restrictScalars PresheafOfModules.restrictScalarsObj
  ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem quotient_unit_section
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (hP : integralOperationsGoodComplex l E Y P) (n : ℕ) (i : ℤ) (U : X.ProEt)
    (x : (P.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    (((D.quotient P hP n).hom.f i).val.app (op U))
        (unrestrictedIntegralTensorSection l E Y n (P.X i)
          (op ((proEtaleIsoPostcompose g).obj U)) 1 x) =
      unrestrictedIntegralTensorSection l E X n
        (((isoReductionIntegralComplex l E g).obj P).X i) (op U) 1 x := by
  have h := hD.2.2.2.2.2.2.1 P hP n i U 1 x
  have ho : ((isoSectionwiseConstantMap.{u, u} g (CommRingCat.of
      (ULift.{u+1} (Padic.coefficientExtensionRing l E (n + 1))))).hom.app (op U)) 1 = 1 :=
    (RingCat.Hom.hom _).map_one
  exact h.trans (congrArg (fun c ↦ unrestrictedIntegralTensorSection l E X n
    (((isoReductionIntegralComplex l E g).obj P).X i) (op U) c x) ho)

private theorem index_apply_heq {I : Type a} {A B : I → Type b}
    (f : ∀ i, A i → B i) {i j : I} (h : i = j) {x : A i} {y : A j}
    (hx : HEq x y) : HEq (f i x) (f j y) := by
  subst j
  cases hx
  rfl

private theorem tensor_map_unit_section (W : Scheme.{u}) (n : ℕ)
    {P Q P' Q' : CochainComplex (integralTowerModules l E W) ℤ}
    (a : P ⟶ P') (b : Q ⟶ Q') (p q : ℤ) (U : W.ProEtᵒᵖ)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    (((integralOperationsTensorLevel l E W n).map
        (X := (P, Q)) (Y := (P', Q')) (a, b)).f (p + q)).val.app U
        (integralOperationsTotalTensorSection l E W n P Q p q U
          (unrestrictedIntegralTensorSection l E W n _ U 1 x)
          (unrestrictedIntegralTensorSection l E W n _ U 1 y)) =
      integralOperationsTotalTensorSection l E W n P' Q' p q U
        (unrestrictedIntegralTensorSection l E W n _ U 1 ((a.f p).val.app U x))
        (unrestrictedIntegralTensorSection l E W n _ U 1 ((b.f q).val.app U y)) := by
  rw [finite_tensor_map_section]
  exact congrArg₂ (integralOperationsTotalTensorSection l E W n P' Q' p q U)
    (finite_reduction_map_section l E W n (a.f p) U x)
    (finite_reduction_map_section l E W n (b.f q) U y)

-- The tensor and restricted-scalar section types require substantial elaboration.
/-- The left square agrees on every unit reduction tensor generator.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 011G and 07A4
(blueprint: lem-pod-tensor-shift-strict-tower-left-generator-t6).

The inverse tensor normalization reduces the input to a tensor on Y. Quotient
normalization sends 1 tensor x to 1 tensor x because the coefficient ring map
preserves 1. The Y shift normalization and forward tensor normalization compute
one image. The finite tensor map law, identity components of the termwise shift
comparison, and X shift normalization compute the other. Integer degree transport
identifies the total degrees; in the right slot, additivity transports (-1)^(pr).
Thus the two images agree for every integer shift and every pair of sections. -/
theorem podTensorShift_strictTowerLeftGenerator
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D) (hT : PodCompletedTensorReindex.Laws l E g D T)
    (SY : PodTensorSignedShift l E Y) (SX : PodTensorSignedShift l E X)
    (hSY : SY.Generators l E) (hSX : SX.Generators l E)
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory) (r : ℤ)
    [(isoReductionIntegralInverse l E g).Additive]
    (n : ℕᵒᵖ) (p q : ℤ) (U : X.ProEtᵒᵖ)
    (x : ((((isoReductionIntegralComplex l E g).obj (P.obj⟦r⟧)).X p).val.obj U))
    (y : ((((isoReductionIntegralComplex l E g).obj Q.obj).X q).val.obj U)) :
    let PX := (podGoodReindex l E g D).obj P
    let QX := (podGoodReindex l E g D).obj Q
    let yX := unrestrictedIntegralTensorSection l E X n.unop (QX.obj.X q) U 1 y
    (((T.tower P Q).hom.app n).f ((p+q)+r)).val.app U
      ((((SY.leftTower P Q r).hom.app n).f (p+q)).val.app
        (op ((proEtaleIsoPostcompose g).obj U.unop))
        (((((T.tower ⟨P.obj⟦r⟧, SY.good P r⟩ Q).inv.app n).f (p+q)).val.app U)
          (integralOperationsTotalTensorSection l E X n.unop
            ((isoReductionIntegralComplex l E g).obj (P.obj⟦r⟧)) QX.obj p q U
            (unrestrictedIntegralTensorSection l E X n.unop _ U 1 x) yX))) =
      (((SX.leftTower PX QX r).hom.app n).f (p+q)).val.app U
        ((((integralOperationsTensorLevel l E X n.unop).map
          (X := ((isoReductionIntegralComplex l E g).obj (P.obj⟦r⟧), QX.obj))
          (Y := (PX.obj⟦r⟧, QX.obj))
          ((((isoReductionIntegralComplex l E g).commShiftIso r).hom.app P.obj),
            𝟙 QX.obj)).f (p+q)).val.app U
          (integralOperationsTotalTensorSection l E X n.unop
            ((isoReductionIntegralComplex l E g).obj (P.obj⟦r⟧)) QX.obj p q U
            (unrestrictedIntegralTensorSection l E X n.unop _ U 1 x) yX)) := by
  dsimp only
  let xY := unrestrictedIntegralTensorSection l E Y n.unop (P.obj.X (p+r))
    (op ((proEtaleIsoPostcompose g).obj U.unop)) 1 x
  let yY := unrestrictedIntegralTensorSection l E Y n.unop (Q.obj.X q)
    (op ((proEtaleIsoPostcompose g).obj U.unop)) 1 y
  have hinv := hT.2.1 ⟨P.obj⟦r⟧, SY.good P r⟩ Q n.unop p q U.unop xY yY
  have hx := quotient_unit_section l E g D hD (P.obj⟦r⟧) (SY.good P r)
    n.unop p U.unop x
  have hy := quotient_unit_section l E g D hD Q.obj Q.property n.unop q U.unop y
  dsimp only [xY, yY] at hinv
  simp only [CochainComplex.shiftFunctor_obj_X'] at hx
  rw [hx, hy] at hinv
  let PX := (podGoodReindex l E g D).obj P
  let QX := (podGoodReindex l E g D).obj Q
  let xX := unrestrictedIntegralTensorSection l E X n.unop (PX.obj.X (p+r)) U 1 x
  let yX := unrestrictedIntegralTensorSection l E X n.unop (QX.obj.X q) U 1 y
  have hsY := hSY.1 P Q n.unop p q r
    (op ((proEtaleIsoPostcompose g).obj U.unop)) xY yY
  have ht := hT.1 P Q n.unop (p+r) q U.unop xY yY
  dsimp only [xY, yY] at ht
  have hx0 := quotient_unit_section l E g D hD P.obj P.property
    n.unop (p+r) U.unop x
  have hy0 := quotient_unit_section l E g D hD Q.obj Q.property n.unop q U.unop y
  rw [hx0, hy0] at ht
  have hsX := hSX.1 PX QX n.unop p q r U xX yX
  have ha := tensor_map_unit_section l E X n.unop
    (((isoReductionIntegralComplex l E g).commShiftIso r).hom.app P.obj)
    (𝟙 QX.obj) p q U x y
  simp only [Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
    HomologicalComplex.id_f, SheafOfModules.id_val, PresheafOfModules.id_app,
    ConcreteCategory.id_apply] at ha
  have hidx : (p+q)+r = (p+r)+q := by omega
  have hL := (index_apply_heq
    (fun j ↦ ⇑((((T.tower P Q).hom.app n).f j).val.app U)) hidx hsY).trans (heq_of_eq ht)
  have hR := hsX
  exact (congrArg (fun z ↦
    (((T.tower P Q).hom.app n).f ((p+q)+r)).val.app U
      ((((SY.leftTower P Q r).hom.app n).f (p+q)).val.app
        (op ((proEtaleIsoPostcompose g).obj U.unop)) z)) hinv).trans
    ((eq_of_heq (hL.trans hR.symm)).trans
      (congrArg (fun z ↦ (((SX.leftTower PX QX r).hom.app n).f
        (p+q)).val.app U z) ha).symm)

end WeilConjectures
