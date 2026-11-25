/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingCoherentTensorRoosAux2
public import WeilConjectures.PoincareDuality.PodReductionRepresentatives.PodReindexingReductionTensorData
import all WeilConjectures.PoincareDuality.Pod.Reduction.PodReductionDescentSystem
import all WeilConjectures.PoincareDuality.Pod.Reduction.PodReductionRepresentativeModels

/-! # The chain-level model of the coherent system tensor comparison

The unary reduction models of the two good representatives identify the coherent system
tensor comparison, followed by the reduction comparisons, with the localization of an actual
chain map: the transported system cochain tensor comparison followed by the two unary chain
models.

Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 03EL, 07A4, 0941
(blueprint: stage3-pod-reindexing-coherent-tensor-roos).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local instance 1000000] SheafOfModules.instAbelian

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The coefficient identification of the Hom resolution model is the completed reduction
coefficient map.
Source: Stacks 03CO; uniqueness of maps into an inverse limit. -/
theorem podReindexingCoefficient_none_eq {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
        (podReindexingCoefficient l E g none) = isoReductionCompletedMap l E g := by
  have hπ (W : Scheme.{u}) (n : ℕ) :
      (sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (completedIntegralCommRingProjectionUnrestricted.{u, u} l E W n) =
          limit.π (integralCoefficientSheafSystem l E W) (op n) := by rfl
  have hc := (podReindexingCoefficient_existsUnique l E g).exists.choose_spec
  apply (isoReductionCompletedMap_existsUnique l E g).unique
  · intro n
    have hn := congrArg
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map) (hc.2 n)
    have hm : (sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        ((isoSectionwiseInverseImage g CommRingCat.{u + 1}).map
          (completedIntegralCommRingProjectionUnrestricted l E Y n)) =
        (isoSectionwiseInverseImage g RingCat.{u + 1}).map
          ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (completedIntegralCommRingProjectionUnrestricted l E Y n)) := rfl
    simpa only [Functor.map_comp, hm, hπ, hc.1 n, podReindexingCoefficient,
      Functor.mapIso_hom] using hn
  · exact (isoReductionCompletedMap_existsUnique l E g).exists.choose_spec

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The module reindexing functor of the Hom resolution model is the ordinary one.
Source: Stacks 03CO. -/
theorem podReindexingFunctor_none_eq {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    podReindexingFunctor l E g none = isoReductionIntegralInverse l E g := by
  exact congrArg (fun c : (isoSectionwiseInverseImage g RingCat.{u + 1}).obj
      ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (podReindexingRing l E Y none)) ≅
      (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (podReindexingRing l E X none) ↦
      isoSectionwiseModuleInverseImage.{u, u} g c.hom) (podReindexingCoefficient_none_eq l E g)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The derived reindexing functor of the Hom resolution model is the ordinary one.
Source: Stacks 03CO, 05RU. -/
theorem podReindexingDerivedFunctor_none_eq {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    podReindexingDerivedFunctor l E g none = podOrdinaryReindex l E g := by
  exact congrArg (fun c : (isoSectionwiseInverseImage g RingCat.{u + 1}).obj
      (completedIntegralCoefficientSheafUnrestricted l E Y) ≅
        completedIntegralCoefficientSheafUnrestricted l E X ↦
      (isoSectionwiseModuleInverseImage g c.hom).mapDerivedCategory)
    (podReindexingCoefficient_none_eq l E g)

/-- The module reindexing functor of the Hom resolution model is exact.
Source: Stacks 03CO. -/
theorem podReindexingFunctor_none_exact {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (podReindexingFunctor l E g none).Additive ∧
      PreservesFiniteLimits (podReindexingFunctor l E g none) ∧
      PreservesFiniteColimits (podReindexingFunctor l E g none) := by
  let c := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
      (podReindexingCoefficient l E g none)
  exact @isoSectionwiseModuleInverseImage_exact.{u, u} X Y g inferInstance _ _ c.hom
    c.isIso_hom

/-- A localization factor transported along an equality of exact functors.
Source: Stacks 05RU. -/
theorem reductionFactorOfIso_mapDerivedCategory {C₁ C₂ : Type*} {_ : Category C₁}
    {_ : Abelian C₁} {_ : HasDerivedCategory C₁} {_ : Category C₂} {_ : Abelian C₂}
    {_ : HasDerivedCategory C₂}
    (F₁ F₂ : C₁ ⥤ C₂) [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    (G : DerivedCategory C₁ ⥤ DerivedCategory C₂)
    (hF : F₁ = F₂) (h : F₁.mapDerivedCategory = G) (hG : G = F₂.mapDerivedCategory)
    (K : CochainComplex C₁ ℤ) :
    (reductionFactorOfIso DerivedCategory.Q DerivedCategory.Q (F₁.mapHomologicalComplex (.up ℤ))
        F₁.mapDerivedCategory G (eqToIso h) F₁.mapDerivedCategoryFactors).hom.app K ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (eqToIso hF) (.up ℤ)).hom.app K) =
      eqToHom (by rw [hG]) ≫ F₂.mapDerivedCategoryFactors.hom.app K := by
  subst hF hG
  have : (NatIso.mapHomologicalComplex (Iso.refl F₁) (.up ℤ)).hom.app K = 𝟙 _ := by
    ext i
    simp
  simp [reductionFactorOfIso_hom, this]

/-- Equal exact functors have equal localization factors, after the equality transports.
Source: Stacks 05RU. -/
theorem Functor.mapDerivedCategoryFactors_congr {C₁ C₂ : Type*} [Category C₁] [Abelian C₁]
    [HasDerivedCategory C₁] [Category C₂] [Abelian C₂] [HasDerivedCategory C₂]
    (F G : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (hFG : F = G) (h : F.mapDerivedCategory = G.mapDerivedCategory)
    (K : CochainComplex C₁ ℤ) :
    (eqToIso h).inv.app (DerivedCategory.Q.obj K) ≫ F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (eqToIso hFG) (.up ℤ)).hom.app K) =
      G.mapDerivedCategoryFactors.hom.app K := by
  subst hFG
  have : (NatIso.mapHomologicalComplex (Iso.refl F) (.up ℤ)).hom.app K = 𝟙 _ := by
    ext i
    simp
  simp [this]

/-- The transported system localization factor is the localization factor of system
inverse image.
Source: Stacks 05RU, 0941. -/
theorem systemFactor_hom_app_eq {X Y : Scheme.{u}} (g : X ⟶ Y)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
    (PodReductionRepresentatives.systemFactor l E g).hom.app C =
      (integralComparisonSequencePullback l E g).mapDerivedCategoryFactors.hom.app C := by
  rw [PodReductionRepresentatives.systemFactor, reductionSystemFactorOfIso_hom]
  exact Functor.mapDerivedCategoryFactors_congr _ _ (PodReductionRepresentatives.inverse_eq l E g)
    (PodReductionRepresentatives.derived_eq l E g) _

/-- The categorical pasting behind the chain-level model of the system tensor comparison.
Source: naturality of the system tensor comparison. -/
theorem systemTensorChain_paste {DY DX : Type*} [Category* DY] [Category* DX]
    (G : DY ⥤ DX) (TY : DY × DY ⥤ DY) (TX : DX × DX ⥤ DX)
    (w : TY ⋙ G ≅ G.prod G ⋙ TX)
    {RP₀ RQ₀ QRP QRQ QS : DY} {ZP ZQ IP IQ QIS QSI QSX : DX}
    (rP : RP₀ ≅ QRP) (rQ : RQ₀ ≅ QRQ) (sY : QS ≅ TY.obj (QRP, QRQ))
    (uP : G.obj RP₀ ⟶ ZP) (uQ : G.obj RQ₀ ⟶ ZQ) (sX : QSX ≅ TX.obj (ZP, ZQ))
    (fP : G.obj QRP ⟶ IP) (fQ : G.obj QRQ ⟶ IQ) (bP : IP ⟶ ZP) (bQ : IQ ⟶ ZQ)
    (fS : G.obj QS ⟶ QIS) (chain : QIS ⟶ QSI) (sI : QSI ≅ TX.obj (IP, IQ))
    (sβ : QSI ⟶ QSX) (qσ : QIS ⟶ QSX)
    (huP : uP = G.map rP.hom ≫ fP ≫ bP) (huQ : uQ = G.map rQ.hom ≫ fQ ≫ bQ)
    (hmodel : G.map sY.hom ≫ w.hom.app (QRP, QRQ) ≫ TX.map (Prod.mkHom fP fQ) =
      fS ≫ chain ≫ sI.hom)
    (hnat : sβ ≫ sX.hom = sI.hom ≫ TX.map (Prod.mkHom bP bQ))
    (hqσ : qσ = chain ≫ sβ) :
    G.map (sY.hom ≫ TY.map (Prod.mkHom rP.inv rQ.inv)) ≫ w.hom.app (RP₀, RQ₀) ≫
        TX.map (Prod.mkHom uP uQ) ≫ sX.inv = fS ≫ qσ := by
  have hw := w.hom.naturality (Prod.mkHom rP.inv rQ.inv)
  dsimp only [Functor.comp_map, Functor.prod_map] at hw
  subst huP huQ hqσ
  rw [G.map_comp, Category.assoc, reassoc_of% hw, ← TX.map_comp_assoc]
  have hp : (Prod.mkHom (G.map rP.inv) (G.map rQ.inv) ≫
      Prod.mkHom (G.map rP.hom ≫ fP ≫ bP) (G.map rQ.hom ≫ fQ ≫ bQ) : (_ : DX × DX) ⟶ _) =
      Prod.mkHom fP fQ ≫ Prod.mkHom bP bQ := by
    ext
    · simp [← G.map_comp_assoc]
    · simp [← G.map_comp_assoc]
  rw [hp, TX.map_comp, Category.assoc, reassoc_of% hmodel, ← reassoc_of% hnat, Iso.hom_inv_id,
    Category.comp_id]

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
local notation "S[" W "]" => coefficientTotalTensor.{u, u + 1, u}
  (coefficientSequenceTopology (ProEt.topology W)) (coefficientSequenceCommRingSheaf l E W)

/-- The coherent system tensor comparison, followed by the two reduction comparisons, is the
localization of the transported system cochain tensor comparison followed by two unary chain
models, provided these models localize the unary reduction comparisons.
Source: Stacks 03EL, 07A4, 0941 (blueprint: stage3-pod-reindexing-coherent-tensor-roos). -/
theorem podReindexing_systemTensor_chainModel
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (A : PodCompletionReindex l E g)
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (βP : (I[g]).obj ((R[Y]).obj P.obj) ≅ (R[X]).obj ((podGoodReindex l E g A).obj P).obj)
    (βQ : (I[g]).obj ((R[Y]).obj Q.obj) ≅ (R[X]).obj ((podGoodReindex l E g A).obj Q).obj)
    (hP :
      letI : (isoReductionIntegralInverse l E g).Additive :=
        isoSectionwiseModuleInverseImage_additive.{u, u} g (isoReductionCompletedMap l E g).hom
      letI : PreservesFiniteLimits (isoReductionIntegralInverse l E g) :=
        isoSectionwiseModuleInverseImage_limits.{u, u} g (isoReductionCompletedMap l E g).hom
      letI : PreservesFiniteColimits (isoReductionIntegralInverse l E g) :=
        isoSectionwiseModuleInverseImage_colimits.{u, u} g (isoReductionCompletedMap l E g).hom
      A.reduction.hom.app (DerivedCategory.Q.obj P.obj) ≫
          (podReindexCalculus l E X).reduction.map
            ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app P.obj) ≫
          (pullbackTensorReductionModel l E X).hom.app ((podGoodReindex l E g A).obj P) =
        (integralComparisonDerivedSequencePullback l E g).map
            ((pullbackTensorReductionModel l E Y).hom.app P) ≫
          (PodReductionRepresentatives.systemFactor l E g).hom.app ((R[Y]).obj P.obj) ≫
          DerivedCategory.Q.map βP.hom)
    (hQ :
      letI : (isoReductionIntegralInverse l E g).Additive :=
        isoSectionwiseModuleInverseImage_additive.{u, u} g (isoReductionCompletedMap l E g).hom
      letI : PreservesFiniteLimits (isoReductionIntegralInverse l E g) :=
        isoSectionwiseModuleInverseImage_limits.{u, u} g (isoReductionCompletedMap l E g).hom
      letI : PreservesFiniteColimits (isoReductionIntegralInverse l E g) :=
        isoSectionwiseModuleInverseImage_colimits.{u, u} g (isoReductionCompletedMap l E g).hom
      A.reduction.hom.app (DerivedCategory.Q.obj Q.obj) ≫
          (podReindexCalculus l E X).reduction.map
            ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app Q.obj) ≫
          (pullbackTensorReductionModel l E X).hom.app ((podGoodReindex l E g A).obj Q) =
        (integralComparisonDerivedSequencePullback l E g).map
            ((pullbackTensorReductionModel l E Y).hom.app Q) ≫
          (PodReductionRepresentatives.systemFactor l E g).hom.app ((R[Y]).obj Q.obj) ≫
          DerivedCategory.Q.map βQ.hom) :
    letI : (isoReductionIntegralInverse l E g).Additive :=
      isoSectionwiseModuleInverseImage_additive.{u, u} g (isoReductionCompletedMap l E g).hom
    letI : PreservesFiniteLimits (isoReductionIntegralInverse l E g) :=
      isoSectionwiseModuleInverseImage_limits.{u, u} g (isoReductionCompletedMap l E g).hom
    letI : PreservesFiniteColimits (isoReductionIntegralInverse l E g) :=
      isoSectionwiseModuleInverseImage_colimits.{u, u} g (isoReductionCompletedMap l E g).hom
    (integralComparisonDerivedSequencePullback l E g).map
        ((pullbackTensorSystemModel l E Y _ _
          (pullbackTensorReductionGood l E Y P) (pullbackTensorReductionGood l E Y Q)).hom ≫
        (podReindexCalculus l E Y).systemClosed.tensor.map
          (Prod.mkHom ((pullbackTensorReductionModel l E Y).inv.app P)
            ((pullbackTensorReductionModel l E Y).inv.app Q))) ≫
      (podReindexingSystemTensor l E g).hom.app
        ((podReindexCalculus l E Y).reduction.obj (DerivedCategory.Q.obj P.obj),
          (podReindexCalculus l E Y).reduction.obj (DerivedCategory.Q.obj Q.obj)) ≫
      (podReindexCalculus l E X).systemClosed.tensor.map
        (Prod.mkHom
          (A.reduction.hom.app (DerivedCategory.Q.obj P.obj) ≫
            (podReindexCalculus l E X).reduction.map
              ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app P.obj) ≫
            (pullbackTensorReductionModel l E X).hom.app ((podGoodReindex l E g A).obj P))
          (A.reduction.hom.app (DerivedCategory.Q.obj Q.obj) ≫
            (podReindexCalculus l E X).reduction.map
              ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app Q.obj) ≫
            (pullbackTensorReductionModel l E X).hom.app ((podGoodReindex l E g A).obj Q))) ≫
      (pullbackTensorSystemModel l E X _ _
        (pullbackTensorReductionGood l E X ((podGoodReindex l E g A).obj P))
        (pullbackTensorReductionGood l E X ((podGoodReindex l E g A).obj Q))).inv =
    (integralComparisonSequencePullback l E g).mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map ((PodReductionRepresentatives.systemChain l E g).hom.app
        ((R[Y]).obj P.obj, (R[Y]).obj Q.obj) ≫ (S[X]).map (Prod.mkHom βP.hom βQ.hom)) := by
  let : (isoReductionIntegralInverse l E g).Additive :=
    isoSectionwiseModuleInverseImage_additive.{u, u} g (isoReductionCompletedMap l E g).hom
  let : PreservesFiniteLimits (isoReductionIntegralInverse l E g) :=
    isoSectionwiseModuleInverseImage_limits.{u, u} g (isoReductionCompletedMap l E g).hom
  let : PreservesFiniteColimits (isoReductionIntegralInverse l E g) :=
    isoSectionwiseModuleInverseImage_colimits.{u, u} g (isoReductionCompletedMap l E g).hom
  have hgP := pullbackTensorReductionGood l E Y P
  have hgQ := pullbackTensorReductionGood l E Y Q
  have hIP := sequence_good l E g _ hgP
  have hIQ := sequence_good l E g _ hgQ
  have hmodel := system_model l E g _ _ hgP hgQ hIP hIQ
  have hnat := system_naturality l E X _ _ _ _ hIP hIQ
    (pullbackTensorReductionGood l E X ((podGoodReindex l E g A).obj P))
    (pullbackTensorReductionGood l E X ((podGoodReindex l E g A).obj Q)) βP.hom βQ.hom
  rw [← systemFactor_hom_app_eq]
  refine systemTensorChain_paste (integralComparisonDerivedSequencePullback l E g)
    (podReindexCalculus l E Y).systemClosed.tensor (podReindexCalculus l E X).systemClosed.tensor
    (podReindexingSystemTensor l E g) ((pullbackTensorReductionModel l E Y).app P)
    ((pullbackTensorReductionModel l E Y).app Q)
    (pullbackTensorSystemModel l E Y _ _ hgP hgQ)
    (pullbackTensorSystemModel l E X _ _
      (pullbackTensorReductionGood l E X ((podGoodReindex l E g A).obj P))
      (pullbackTensorReductionGood l E X ((podGoodReindex l E g A).obj Q)))
    (RP₀ := (podReindexCalculus l E Y).reduction.obj (DerivedCategory.Q.obj P.obj))
    (RQ₀ := (podReindexCalculus l E Y).reduction.obj (DerivedCategory.Q.obj Q.obj))
    (QRP := DerivedCategory.Q.obj ((R[Y]).obj P.obj))
    (QRQ := DerivedCategory.Q.obj ((R[Y]).obj Q.obj))
    (uP := A.reduction.hom.app (DerivedCategory.Q.obj P.obj) ≫
          (podReindexCalculus l E X).reduction.map
            ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app P.obj) ≫
          (pullbackTensorReductionModel l E X).hom.app ((podGoodReindex l E g A).obj P))
    (uQ := A.reduction.hom.app (DerivedCategory.Q.obj Q.obj) ≫
          (podReindexCalculus l E X).reduction.map
            ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app Q.obj) ≫
          (pullbackTensorReductionModel l E X).hom.app ((podGoodReindex l E g A).obj Q))
    (fP := (PodReductionRepresentatives.systemFactor l E g).hom.app ((R[Y]).obj P.obj))
    (fQ := (PodReductionRepresentatives.systemFactor l E g).hom.app ((R[Y]).obj Q.obj))
    (bP := DerivedCategory.Q.map βP.hom) (bQ := DerivedCategory.Q.map βQ.hom)
    (fS := (PodReductionRepresentatives.systemFactor l E g).hom.app
      ((S[Y]).obj ((R[Y]).obj P.obj, (R[Y]).obj Q.obj)))
    (chain := DerivedCategory.Q.map ((PodReductionRepresentatives.systemChain l E g).hom.app
      ((R[Y]).obj P.obj, (R[Y]).obj Q.obj)))
    (sI := pullbackTensorSystemModel l E X _ _ hIP hIQ)
    (sβ := DerivedCategory.Q.map ((S[X]).map (Prod.mkHom βP.hom βQ.hom)))
    (huP := hP) (huQ := hQ) (hmodel := hmodel) (hnat := hnat)
    (hqσ := Functor.map_comp _ _ _)

/-- The identification of the reindexed complex of the Hom resolution model with the
ordinary reindexed complex.
Source: Stacks 03CO. -/
def podReindexComplexIso {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    (podReindexingComplexFunctor l E g none).obj P ≅ (isoReductionIntegralComplex l E g).obj P :=
  letI : (podReindexingFunctor l E g none).Additive := (podReindexingFunctor_none_exact l E g).1
  letI : (isoReductionIntegralInverse l E g).Additive :=
    isoSectionwiseModuleInverseImage_additive.{u, u} g (isoReductionCompletedMap l E g).hom
  (NatIso.mapHomologicalComplex (eqToIso (podReindexingFunctor_none_eq l E g)) (.up ℤ)).app P

set_option quotPrecheck false in
set_option hygiene false in
local notation "F[" g "]" => podReindexingComplexFunctor l E g none

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The unary reduction model of a good representative, transported to the ordinary
reindexed complex, localizes the reduction comparison followed by the ordinary localization
factor.
Source: Stacks 05RU, 0941 (blueprint: stage3-pod-reindexing-coherent-tensor-roos). -/
theorem podReductionUnary_transport {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (A : PodCompletionReindex l E g)
    (h : podReindexingDerivedFunctor l E g none = podOrdinaryReindex l E g)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (hFP : integralOperationsGoodComplex l E X ((F[g]).obj P.obj))
    (β : (I[g]).obj ((R[Y]).obj P.obj) ≅ (R[X]).obj ((F[g]).obj P.obj))
    (hU : (integralComparisonDerivedSequencePullback l E g).map
          ((pullbackTensorReductionModel l E Y).hom.app P) ≫
        (PodReductionRepresentatives.systemFactor l E g).hom.app
          ((R[Y]).obj P.obj) ≫ (PodReductionRepresentatives.systemQ l E X).map β.hom =
      A.reduction.hom.app ((podReindexingQ l E Y none).obj P.obj) ≫
        (podReindexCalculus l E X).reduction.map
          ((PodReductionRepresentatives.factor l E g h).hom.app P.obj) ≫
        (pullbackTensorReductionModel l E X).hom.app ⟨(F[g]).obj P.obj, hFP⟩) :
    letI : (isoReductionIntegralInverse l E g).Additive :=
      isoSectionwiseModuleInverseImage_additive.{u, u} g (isoReductionCompletedMap l E g).hom
    letI : PreservesFiniteLimits (isoReductionIntegralInverse l E g) :=
      isoSectionwiseModuleInverseImage_limits.{u, u} g (isoReductionCompletedMap l E g).hom
    letI : PreservesFiniteColimits (isoReductionIntegralInverse l E g) :=
      isoSectionwiseModuleInverseImage_colimits.{u, u} g (isoReductionCompletedMap l E g).hom
    A.reduction.hom.app (DerivedCategory.Q.obj P.obj) ≫
        (podReindexCalculus l E X).reduction.map
          ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app P.obj) ≫
        (pullbackTensorReductionModel l E X).hom.app ((podGoodReindex l E g A).obj P) =
      (integralComparisonDerivedSequencePullback l E g).map
          ((pullbackTensorReductionModel l E Y).hom.app P) ≫
        (PodReductionRepresentatives.systemFactor l E g).hom.app ((R[Y]).obj P.obj) ≫
        DerivedCategory.Q.map
          (β ≪≫ (R[X]).mapIso (podReindexComplexIso l E g P.obj)).hom := by
  let : (podReindexingFunctor l E g none).Additive := (podReindexingFunctor_none_exact l E g).1
  let : PreservesFiniteLimits (podReindexingFunctor l E g none) :=
    (podReindexingFunctor_none_exact l E g).2.1
  let : PreservesFiniteColimits (podReindexingFunctor l E g none) :=
    (podReindexingFunctor_none_exact l E g).2.2
  let : (isoReductionIntegralInverse l E g).Additive :=
    isoSectionwiseModuleInverseImage_additive.{u, u} g (isoReductionCompletedMap l E g).hom
  let : PreservesFiniteLimits (isoReductionIntegralInverse l E g) :=
    isoSectionwiseModuleInverseImage_limits.{u, u} g (isoReductionCompletedMap l E g).hom
  let : PreservesFiniteColimits (isoReductionIntegralInverse l E g) :=
    isoSectionwiseModuleInverseImage_colimits.{u, u} g (isoReductionCompletedMap l E g).hom
  have hfac := reductionFactorOfIso_mapDerivedCategory (podReindexingFunctor l E g none)
    (isoReductionIntegralInverse l E g) (podOrdinaryReindex l E g)
    (podReindexingFunctor_none_eq l E g) h rfl P.obj
  have hfac2 : (PodReductionRepresentatives.factor l E g h).hom.app P.obj ≫ _ = _ := hfac
  simp only [eqToHom_refl, Category.id_comp] at hfac2
  have hr := (pullbackTensorReductionModel l E X).hom.naturality
    (X := ⟨(F[g]).obj P.obj, hFP⟩) (Y := (podGoodReindex l E g A).obj P)
    (ObjectProperty.homMk (podReindexComplexIso l E g P.obj).hom)
  dsimp only [Functor.comp_map, ObjectProperty.homMk_hom] at hr
  rw [← hfac2, Functor.map_comp, Category.assoc]
  erw [hr]
  rw [← reassoc_of% hU, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp]
  rfl

end WeilConjectures
