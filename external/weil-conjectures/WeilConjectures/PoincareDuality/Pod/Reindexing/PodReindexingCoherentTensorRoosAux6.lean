/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingCoherentTensorRoosAux5
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTensorLevelReduction

/-! # The strict tower equation of the coherent tensor comparison

The tower map induced by the chain-level model of the coherent system tensor comparison is
the prescribed strict tensor tower comparison: both are fixed on the total tensors of
unit-inserted original sections.

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
set_option quotPrecheck false in
set_option hygiene false in
local notation "S[" W "]" => coefficientTotalTensor.{u, u + 1, u}
  (coefficientSequenceTopology (ProEt.topology W)) (coefficientSequenceCommRingSheaf l E W)

/-- A composite of four maps of towers of complexes of sheaves of modules, on sections.
Source: composition of natural transformations. -/
theorem towerSheafHom_comp₄_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat} {D : Type*} [Category D]
    {T₀ T₁ T₂ T₃ T₄ : D ⥤ CochainComplex (SheafOfModules R) ℤ}
    (a : T₀ ⟶ T₁) (b : T₁ ⟶ T₂) (c : T₂ ⟶ T₃) (d : T₃ ⟶ T₄) (n : D) (k : ℤ) (U : Cᵒᵖ)
    (z : ((T₀.obj n).X k).val.obj U) :
    (((a ≫ b ≫ c ≫ d).app n).f k).val.app U z =
      ((d.app n).f k).val.app U (((c.app n).f k).val.app U
        (((b.app n).f k).val.app U (((a.app n).f k).val.app U z))) :=
  rfl

/-- The inverse of an isomorphism of towers of complexes of sheaves of modules, on sections.
Source: composition of natural transformations. -/
theorem towerSheafIso_inv_hom_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat} {D : Type*} [Category D]
    {T₀ T₁ : D ⥤ CochainComplex (SheafOfModules R) ℤ} (e : T₀ ≅ T₁) (n : D) (k : ℤ)
    (U : Cᵒᵖ) (z : ((T₀.obj n).X k).val.obj U) :
    ((e.inv.app n).f k).val.app U (((e.hom.app n).f k).val.app U z) = z := by
  have h := congrArg (fun f ↦ ((f.app n).f k).val.app U z) e.hom_inv_id
  exact h

/-- The tower map induced by the chain-level model of the system tensor comparison sends the
total tensor of two unit-inserted original sections to the same total tensor after reindexing.
Source: Stacks 03EK, 07A4, 0941. -/
theorem podCoherentTower_unitTensor {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (A : PodCompletionReindex l E g)
    (hA : PodCompletionReindex.RestrictedGenerators l E g A)
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (βP : (I[g]).obj ((R[Y]).obj P.obj) ≅ (R[X]).obj ((F[g]).obj P.obj))
    (βQ : (I[g]).obj ((R[Y]).obj Q.obj) ≅ (R[X]).obj ((F[g]).obj Q.obj))
    (hβP : PodReductionRepresentatives.Generators l E g P.obj βP)
    (hβQ : PodReductionRepresentatives.Generators l E g Q.obj βQ)
    (n : ℕ) (p q : ℤ) (U : X.ProEt)
    (x : (P.obj.X p).val.obj (op ((proEtaleIsoPostcompose g).obj U)))
    (y : (Q.obj.X q).val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    ((((podReindexTower l E g).map (pullbackTensorTensorTower l E Y P.obj Q.obj).inv ≫
        (A.restricted ((S[Y]).obj ((R[Y]).obj P.obj, (R[Y]).obj Q.obj))).hom ≫
        HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
          (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).map
            ((PodReductionRepresentatives.systemChain l E g).hom.app
              ((R[Y]).obj P.obj, (R[Y]).obj Q.obj) ≫
              (S[X]).map (Prod.mkHom (βP ≪≫ (R[X]).mapIso (podReindexComplexIso l E g P.obj)).hom
                (βQ ≪≫ (R[X]).mapIso (podReindexComplexIso l E g Q.obj)).hom))) ≫
        (pullbackTensorTensorTower l E X ((podGoodReindex l E g A).obj P).obj
          ((podGoodReindex l E g A).obj Q).obj).hom).app (op n)).f (p + q)).val.app (op U)
        (integralOperationsTotalTensorSection l E Y n P.obj Q.obj p q
          (op ((proEtaleIsoPostcompose g).obj U))
          (unrestrictedIntegralTensorSection l E Y n (P.obj.X p)
            (op ((proEtaleIsoPostcompose g).obj U)) 1 x)
          (unrestrictedIntegralTensorSection l E Y n (Q.obj.X q)
            (op ((proEtaleIsoPostcompose g).obj U)) 1 y)) =
      integralOperationsTotalTensorSection l E X n ((podGoodReindex l E g A).obj P).obj
        ((podGoodReindex l E g A).obj Q).obj p q (op U)
        (unrestrictedIntegralTensorSection l E X n (((podGoodReindex l E g A).obj P).obj.X p)
          (op U) 1 x)
        (unrestrictedIntegralTensorSection l E X n (((podGoodReindex l E g A).obj Q).obj.X q)
          (op U) 1 y) := by
  have hY := pullbackTensorTensorTower_hom_reducedUnit l E Y P.obj Q.obj n p q
    ((proEtaleIsoPostcompose g).obj U) x y
  have hs₁ := (congrArg (fun z ↦ (((pullbackTensorTensorTower l E Y P.obj Q.obj).inv.app (op n)).f
    (p + q)).val.app (op ((proEtaleIsoPostcompose g).obj U)) z) hY).symm.trans
    (towerSheafIso_inv_hom_apply (pullbackTensorTensorTower l E Y P.obj Q.obj) (op n) (p + q)
      (op ((proEtaleIsoPostcompose g).obj U)) _)
  let f := (PodReductionRepresentatives.systemChain l E g).hom.app
    ((R[Y]).obj P.obj, (R[Y]).obj Q.obj) ≫
    (S[X]).map (Prod.mkHom (βP ≪≫ (R[X]).mapIso (podReindexComplexIso l E g P.obj)).hom
      (βQ ≪≫ (R[X]).mapIso (podReindexComplexIso l E g Q.obj)).hom)
  let b := (((A.restricted ((S[Y]).obj ((R[Y]).obj P.obj, (R[Y]).obj Q.obj))).hom.app
    (op n)).f (p + q)).val.app (op U)
  let c := (((coefficientSequenceRestriction l E X).map (f.f (p + q))).app
    (op n)).val.app (op U)
  let d := (((pullbackTensorTensorTower l E X ((podGoodReindex l E g A).obj P).obj
    ((podGoodReindex l E g A).obj Q).obj).hom.app (op n)).f (p + q)).val.app (op U)
  refine (towerSheafHom_comp₄_apply _ _ _ _ _ _ _ _).trans ?_
  -- Transport the section identities through the remaining maps without searching the composite.
  refine (congrArg (fun z ↦ d (c (b z))) hs₁).trans ?_
  refine (congrArg (fun z ↦ d (c z))
    (hA ((S[Y]).obj ((R[Y]).obj P.obj, (R[Y]).obj Q.obj)) n (p + q) U _)).trans ?_
  refine (congrArg (fun z ↦ d z)
    (coefficientSequenceRestriction_map_restrictedSection' l E (f.f (p + q)) n (op U) _)).trans ?_
  have hc := podChainModel_generator l E g P.obj Q.obj βP βQ hβP hβQ n p q U x y
  refine (congrArg (fun z ↦ d (integralComparisonRestrictedSection l E X
    (((S[X]).obj ((R[X]).obj ((podGoodReindex l E g A).obj P).obj,
      (R[X]).obj ((podGoodReindex l E g A).obj Q).obj)).X (p + q)) n (op U) z)) hc).trans ?_
  exact pullbackTensorTensorTower_hom_reducedUnit l E X ((podGoodReindex l E g A).obj P).obj
    ((podGoodReindex l E g A).obj Q).obj n p q U x y

/-- A composite of two maps of towers of complexes of sheaves of modules, on sections.
Source: composition of natural transformations. -/
theorem towerSheafHom_comp_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat} {D : Type*} [Category D]
    {T₀ T₁ T₂ : D ⥤ CochainComplex (SheafOfModules R) ℤ}
    (a : T₀ ⟶ T₁) (b : T₁ ⟶ T₂) (n : D) (k : ℤ) (U : Cᵒᵖ)
    (z : ((T₀.obj n).X k).val.obj U) :
    (((a ≫ b).app n).f k).val.app U z = ((b.app n).f k).val.app U (((a.app n).f k).val.app U z) :=
  rfl

/-- The tower map induced by the chain-level model of the coherent system tensor comparison is
the prescribed strict tensor tower comparison.
Source: Stacks 03EK, 07A4, 0941 (blueprint: stage3-pod-reindexing-coherent-tensor-roos). -/
theorem podCoherentTower_eq {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g A)
    (hA : PodCompletionReindex.Laws l E g A)
    (hGen : PodCompletedTensorReindex.Generators l E g A T)
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (βP : (I[g]).obj ((R[Y]).obj P.obj) ≅ (R[X]).obj ((F[g]).obj P.obj))
    (βQ : (I[g]).obj ((R[Y]).obj Q.obj) ≅ (R[X]).obj ((F[g]).obj Q.obj))
    (hβP : PodReductionRepresentatives.Generators l E g P.obj βP)
    (hβQ : PodReductionRepresentatives.Generators l E g Q.obj βQ) :
    (podReindexTower l E g).map (pullbackTensorTensorTower l E Y P.obj Q.obj).inv ≫
        (A.restricted ((S[Y]).obj ((R[Y]).obj P.obj, (R[Y]).obj Q.obj))).hom ≫
        HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
          (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).map
            ((PodReductionRepresentatives.systemChain l E g).hom.app
              ((R[Y]).obj P.obj, (R[Y]).obj Q.obj) ≫
              (S[X]).map (Prod.mkHom (βP ≪≫ (R[X]).mapIso (podReindexComplexIso l E g P.obj)).hom
                (βQ ≪≫ (R[X]).mapIso (podReindexComplexIso l E g Q.obj)).hom))) ≫
        (pullbackTensorTensorTower l E X ((podGoodReindex l E g A).obj P).obj
          ((podGoodReindex l E g A).obj Q).obj).hom = (T.tower P Q).hom := by
  have hquot : PodCompletionReindex.QuotientGenerators l E g A := hA.2.2.2.2.2.2.1
  have hres : PodCompletionReindex.RestrictedGenerators l E g A :=
    hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hu (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (n : ℕ) (p : ℤ) (U : X.ProEt)
      (x : (P.obj.X p).val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
      (((A.quotient P.obj P.property n).hom.f p).val.app (op U))
          (unrestrictedIntegralTensorSection l E Y n (P.obj.X p)
            (op ((proEtaleIsoPostcompose g).obj U)) 1 x) =
        unrestrictedIntegralTensorSection l E X n
          ((((podGoodReindex l E g A).obj P).obj).X p) (op U) 1 x := by
    have h := hquot P.obj P.property n p U 1 x
    have h1 : (isoSectionwiseConstantMap.{u, u} g (CommRingCat.of
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).hom.app (op U) 1 =
        (1 : (integralCoefficientCommRingSheaf l E X n).obj.obj (op U)) := map_one _
    erw [h1] at h
    exact h
  rw [← cancel_epi (T.tower P Q).inv, Iso.inv_hom_id]
  apply NatTrans.ext
  funext n
  apply HomologicalComplex.hom_ext
  intro k
  apply finite_tensor_ext l E X n.unop
    (((podGoodReindex l E g A).obj P).obj) (((podGoodReindex l E g A).obj Q).obj) k
  intro p q hpq U x y
  subst k
  with_unfolding_all simp only [eqToHom_refl, SheafOfModules.id_val, PresheafOfModules.id_app]
  let x' : (P.obj.X p).val.obj (op ((proEtaleIsoPostcompose g).obj U.unop)) := x
  let y' : (Q.obj.X q).val.obj (op ((proEtaleIsoPostcompose g).obj U.unop)) := y
  have hτ := hGen P Q n.unop p q U.unop
    (unrestrictedIntegralTensorSection l E Y n.unop (P.obj.X p)
      (op ((proEtaleIsoPostcompose g).obj U.unop)) 1 x')
    (unrestrictedIntegralTensorSection l E Y n.unop (Q.obj.X q)
      (op ((proEtaleIsoPostcompose g).obj U.unop)) 1 y')
  erw [hu P n.unop p U.unop x', hu Q n.unop q U.unop y'] at hτ
  have hinv := (congrArg (fun z ↦ ((((T.tower P Q).inv.app (op n.unop)).f (p + q)).val.app
    (op U.unop)) z) hτ).symm.trans (towerSheafIso_inv_hom_apply (T.tower P Q) (op n.unop) (p + q)
      (op U.unop) _)
  refine (towerSheafHom_comp_apply _ _ _ _ _ _).trans ?_
  erw [hinv]
  erw [podCoherentTower_unitTensor l E g A hres P Q βP βQ hβP hβQ n.unop p q U.unop x' y']
  rfl

end WeilConjectures
