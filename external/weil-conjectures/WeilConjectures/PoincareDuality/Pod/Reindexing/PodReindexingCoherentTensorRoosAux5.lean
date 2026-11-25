/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingCoherentTensorRoosAux4

/-! # Generator formulas for the chain-level system tensor model

Source: Stacks 03D2, 03EK, 03EL, 07A4 and 0941
(blueprint: stage3-pod-reindexing-coherent-tensor-roos).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local semireducible] pullbackTensorSequenceRingMap

section TotalTensor

open MonoidalCategory

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Total-tensor generators are natural for restriction of sections.
Source: Stacks 03EK and 06YN. -/
theorem coefficientTensorGenerator_val_map
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (A : Sheaf J CommRingCat.{u + 1})
    (P Q : CochainComplex (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) ℤ)
    (p q k : ℤ) (hpq : p + q = k) {U V : Cᵒᵖ} (i : U ⟶ V)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    (((coefficientTotalTensor.{u, u + 1, u} J A).obj (P, Q)).X k).val.map i
        (coefficientTensorGenerator.{u, u + 1, u} J A P Q p q k hpq U x y) =
      coefficientTensorGenerator.{u, u + 1, u} J A P Q p q k hpq V
        ((P.X p).val.map i x) ((Q.X q).val.map i y) := by
  let : EssentiallySmall.{u + 1} C := essentiallySmallSelf.{0, u, u + 1} C
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} A
  let := SheafOfModules.monoidalCategory A
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients.{u + 1, u,
    u + 1} A
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients.{u + 1,
    u, u + 1} A
  let ι := HomologicalComplex.ιMapBifunctor P Q (MonoidalCategory.curriedTensor _)
    (.up ℤ) p q k hpq
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A).obj)
  let z := x ⊗ₜ[A.obj.obj U] y
  have hi := PresheafOfModules.naturality_apply ι.val i
    ((SheafOfModules.tensorObjIsoSheafification (R := A) (P.X p) (Q.X q)).inv.val.app U
      ((adj.unit.app ((P.X p).val ⊗ (Q.X q).val)).app U z))
  have ht := PresheafOfModules.naturality_apply
    (SheafOfModules.tensorObjIsoSheafification (R := A) (P.X p) (Q.X q)).inv.val i
    ((adj.unit.app ((P.X p).val ⊗ (Q.X q).val)).app U z)
  have hu := PresheafOfModules.naturality_apply
    (adj.unit.app ((P.X p).val ⊗ (Q.X q).val)) i z
  dsimp only [Functor.id_obj] at hu
  erw [PresheafOfModules.Monoidal.tensorObj_map_tmul] at hu
  simp only [coefficientTotalTensor, coefficientTensorGenerator]
  with_unfolding_all
    exact (hi.symm.trans (congrArg (ι.val.app V)
      (ht.symm.trans (congrArg
        ((SheafOfModules.tensorObjIsoSheafification (R := A) (P.X p) (Q.X q)).inv.val.app V)
        hu.symm))))

end TotalTensor

-- Elaborating the transported adjunction units on sections is expensive.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The transported system tensor comparison sends the inverse-image unit of a pure tensor to
the tensor of the two inverse-image units.
Source: Stacks 03EL and 07A4. -/
theorem systemChain_unit_generator {X Y : Scheme.{u}} (g : X ⟶ Y)
    (A B : CochainComplex (coefficientSequenceModules l E Y) ℤ) (p q k : ℤ) (hpq : p + q = k)
    (V : ℕ × Y.ProEt) (x : (A.X p).val.obj (op V)) (y : (B.X q).val.obj (op V)) :
    (((PodReductionRepresentatives.systemChain l E g).hom.app (A, B)).f k).val.app
        (op ((pullbackTensorSequenceBase g).obj V))
      (((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E g)).unit.app
          (((coefficientTotalTensor.{u, u + 1, u}
            (coefficientSequenceTopology (ProEt.topology Y))
            (coefficientSequenceCommRingSheaf l E Y)).obj (A, B)).X k)).val.app (op V)
        (coefficientTensorGenerator.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology Y))
          (coefficientSequenceCommRingSheaf l E Y) A B p q k hpq (op V) x y)) =
      coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (ProEt.topology X))
        (coefficientSequenceCommRingSheaf l E X)
        (((integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)).obj A)
        (((integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)).obj B)
        p q k hpq (op ((pullbackTensorSequenceBase g).obj V))
        (((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E g)).unit.app
          (A.X p)).val.app (op V) x)
        (((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E g)).unit.app
          (B.X q)).val.app (op V) y) := by
  have hc := (pullbackTensorSequenceCochain_existsUnique l E g).exists.choose_spec A B p q k hpq
    V x y
  unfold PodReductionRepresentatives.systemChain
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    HomologicalComplex.comp_f]
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply]
  let e := NatIso.mapHomologicalComplex (eqToIso (PodReductionRepresentatives.inverse_eq l E g))
    (.up ℤ)
  have hm := coefficientTotalTensor_map_tensorGenerator.{u, u + 1, u}
    (coefficientSequenceTopology (ProEt.topology X)) (coefficientSequenceCommRingSheaf l E X)
    (e.hom.app A) (e.hom.app B) p q k hpq (op ((pullbackTensorSequenceBase g).obj V))
    (((pullbackTensorSequenceAdjunction l E g).unit.app (A.X p)).val.app (op V) x)
    (((pullbackTensorSequenceAdjunction l E g).unit.app (B.X q)).val.app (op V) y)
  exact (congrArg (fun z ↦ (((coefficientTotalTensor.{u, u + 1, u}
    (coefficientSequenceTopology (ProEt.topology X)) (coefficientSequenceCommRingSheaf l E X)).map
      ((NatIso.prod e e).hom.app (A, B))).f k).val.app
        (op ((pullbackTensorSequenceBase g).obj V)) z) hc).trans hm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction to the tower acts on restricted sections as the original map.
Source: Stacks 0941. -/
theorem coefficientSequenceRestriction_map_restrictedSection {W : Scheme.{u}}
    {M N : coefficientSequenceModules l E W} (f : M ⟶ N)
    (n : ℕ) (U : W.ProEtᵒᵖ) (x : M.val.obj (op (n, U.unop))) :
    ((((coefficientSequenceRestriction l E W).map f).app (op n)).val.app U)
        (integralComparisonRestrictedSection l E W M n U x) =
      integralComparisonRestrictedSection l E W N n U (f.val.app (op (n, U.unop)) x) := by
  have h : HEq
      (fun y ↦ ((((coefficientSequenceRestriction l E W).map f).app (op n)).val.app U) y)
      (fun y ↦ f.val.app (op (n, U.unop)) y) := by
    simpa only [coefficientSequenceRestriction] using
      (coefficientSequenceRestriction_exists l E W).exists.choose_spec.2.2 f n U
  have hx : HEq (integralComparisonRestrictedSection l E W M n U x) x := cast_heq _ x
  have hy : HEq
      (integralComparisonRestrictedSection l E W N n U (f.val.app (op (n, U.unop)) x))
      (f.val.app (op (n, U.unop)) x) := cast_heq _ _
  have hh : HEq
      (((((coefficientSequenceRestriction l E W).map f).app (op n)).val.app U)
        (integralComparisonRestrictedSection l E W M n U x))
      (f.val.app (op (n, U.unop)) x) :=
    dcongr_heq hx (fun _ _ _ ↦ integralComparisonRestrictedSectionType l E W N n U)
      (fun _ _ ↦ h)
  exact eq_of_heq (hh.trans hy.symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- `coefficientSequenceRestriction_map_restrictedSection`, with the concrete-category
application of the original map.
Source: Stacks 0941. -/
theorem coefficientSequenceRestriction_map_restrictedSection' {W : Scheme.{u}}
    {M N : coefficientSequenceModules l E W} (f : M ⟶ N)
    (n : ℕ) (U : W.ProEtᵒᵖ) (x : M.val.obj (op (n, U.unop))) :
    ((((coefficientSequenceRestriction l E W).map f).app (op n)).val.app U)
        (integralComparisonRestrictedSection l E W M n U x) =
      integralComparisonRestrictedSection l E W N n U
        ((ConcreteCategory.hom (f.val.app (op (n, U.unop)))) x) :=
  coefficientSequenceRestriction_map_restrictedSection l E f n U x

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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The chain-level model of the system tensor comparison sends the restricted inverse-image
unit of a tensor of two reduced unit-inserted sections to the tensor of the reindexed reduced
unit-inserted sections.
Source: Stacks 03D2, 03EL, 07A4, 0941. -/
theorem podChainModel_generator {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (P Q : CochainComplex (scalarReductionSource l E Y) ℤ)
    (βP : (I[g]).obj ((R[Y]).obj P) ≅ (R[X]).obj ((F[g]).obj P))
    (βQ : (I[g]).obj ((R[Y]).obj Q) ≅ (R[X]).obj ((F[g]).obj Q))
    (hβP : PodReductionRepresentatives.Generators l E g P βP)
    (hβQ : PodReductionRepresentatives.Generators l E g Q βQ)
    (n : ℕ) (p q : ℤ) (U : X.ProEt)
    (x : (P.X p).val.obj (op ((proEtaleIsoPostcompose g).obj U)))
    (y : (Q.X q).val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    ((((PodReductionRepresentatives.systemChain l E g).hom.app ((R[Y]).obj P, (R[Y]).obj Q) ≫
        (S[X]).map (Prod.mkHom (βP ≪≫ (R[X]).mapIso (podReindexComplexIso l E g P)).hom
          (βQ ≪≫ (R[X]).mapIso (podReindexComplexIso l E g Q)).hom)).f (p + q)).val.app
        (op (n, U)))
      (((integralComparisonSequencePullback l E g).obj
          (((S[Y]).obj ((R[Y]).obj P, (R[Y]).obj Q)).X (p + q))).val.map
        (Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U)).op
        (integralComparisonSequenceGenerator.{u, u} l E g
          (((S[Y]).obj ((R[Y]).obj P, (R[Y]).obj Q)).X (p + q)) n
          ((proEtaleIsoPostcompose g).obj U)
          (coefficientTensorGenerator.{u, u + 1, u}
            (coefficientSequenceTopology (ProEt.topology Y))
            (coefficientSequenceCommRingSheaf l E Y) ((R[Y]).obj P) ((R[Y]).obj Q)
            p q (p + q) rfl (op (n, (proEtaleIsoPostcompose g).obj U))
            (podReducedUnitSection l E Y n (P.X p) ((proEtaleIsoPostcompose g).obj U) x)
            (podReducedUnitSection l E Y n (Q.X q) ((proEtaleIsoPostcompose g).obj U) y)))) =
      coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (ProEt.topology X))
        (coefficientSequenceCommRingSheaf l E X)
        ((R[X]).obj ((isoReductionIntegralComplex l E g).obj P))
        ((R[X]).obj ((isoReductionIntegralComplex l E g).obj Q))
        p q (p + q) rfl (op (n, U))
        (podReducedUnitSection l E X n (((isoReductionIntegralComplex l E g).obj P).X p) U x)
        (podReducedUnitSection l E X n (((isoReductionIntegralComplex l E g).obj Q).X q) U y) := by
  rw [HomologicalComplex.comp_f]
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply]
  erw [PresheafOfModules.naturality_apply
    ((((PodReductionRepresentatives.systemChain l E g).hom.app
      ((R[Y]).obj P, (R[Y]).obj Q)).f (p + q)).val)
    (Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U)).op]
  have hc := systemChain_unit_generator l E g ((R[Y]).obj P) ((R[Y]).obj Q) p q (p + q) rfl
    (n, (proEtaleIsoPostcompose g).obj U)
    (podReducedUnitSection l E Y n (P.X p) ((proEtaleIsoPostcompose g).obj U) x)
    (podReducedUnitSection l E Y n (Q.X q) ((proEtaleIsoPostcompose g).obj U) y)
  refine (congrArg (fun z ↦ (((S[X]).map (Prod.mkHom
      (βP ≪≫ (R[X]).mapIso (podReindexComplexIso l E g P)).hom
      (βQ ≪≫ (R[X]).mapIso (podReindexComplexIso l E g Q)).hom)).f (p + q)).val.app (op (n, U))
      ((((S[X]).obj ((I[g]).obj ((R[Y]).obj P), (I[g]).obj ((R[Y]).obj Q))).X (p + q)).val.map
        (Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U)).op z)) hc).trans ?_
  refine (congrArg (fun z ↦ (((S[X]).map (Prod.mkHom
      (βP ≪≫ (R[X]).mapIso (podReindexComplexIso l E g P)).hom
      (βQ ≪≫ (R[X]).mapIso (podReindexComplexIso l E g Q)).hom)).f (p + q)).val.app (op (n, U)) z)
    (coefficientTensorGenerator_val_map (coefficientSequenceTopology (ProEt.topology X))
      (coefficientSequenceCommRingSheaf l E X) ((I[g]).obj ((R[Y]).obj P))
      ((I[g]).obj ((R[Y]).obj Q)) p q (p + q) rfl
      (Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U)).op _ _)).trans ?_
  refine (coefficientTotalTensor_map_tensorGenerator.{u, u + 1, u}
    (coefficientSequenceTopology (ProEt.topology X)) (coefficientSequenceCommRingSheaf l E X)
    _ _ p q (p + q) rfl (op (n, U)) _ _).trans ?_
  exact congrArg₂ (coefficientTensorGenerator.{u, u + 1, u}
    (coefficientSequenceTopology (ProEt.topology X)) (coefficientSequenceCommRingSheaf l E X)
    ((R[X]).obj ((isoReductionIntegralComplex l E g).obj P))
    ((R[X]).obj ((isoReductionIntegralComplex l E g).obj Q)) p q (p + q) rfl (op (n, U)))
    (podUnaryTransport_generator l E g P βP hβP n p U x)
    (podUnaryTransport_generator l E g Q βQ hβQ n q U y)

end WeilConjectures
