/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReductionRepresentatives.PodReductionReindexUnaryModelAux
import WeilConjectures.PoincareDuality.Pod.Reindex.PodReindexReductionQuotientNormalization
import all WeilConjectures.SmoothPurity.Supporting.CoherentReferenceQuotientComparison

/-! # Transport lemmas for the unary reduction/reindexing model

Equal exact functors have the same localization factors up to the equality
transports, and the coefficient-normalized reindexing functor is the ordinary
relabelling functor.

Source: blueprint dual-Tate compatibility Steps 2 and 4; Stacks 05RU and 03CO.
(blueprint: lem-pod-reduction-reindex-unary-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodReductionRepresentatives

/-- Equal exact functors have equal localization factors, after the equality transports.
Source: Stacks 05RU. -/
theorem mapDerivedCategoryFactors_congr {C₁ C₂ : Type*} {_ : Category C₁} {_ : Abelian C₁}
    {_ : HasDerivedCategory C₁} {_ : Category C₂} {_ : Abelian C₂} {_ : HasDerivedCategory C₂}
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

/-- Transporting an exact functor's localization factor gives the factor of the equal functor.
Source: Stacks 05RU. -/
private theorem reductionSystemFactorOfIso_mapDerived
    {C₁ C₂ : Type*} {_ : Category C₁} {_ : Abelian C₁} {_ : HasDerivedCategory C₁}
    {_ : Category C₂} {_ : Abelian C₂} {_ : HasDerivedCategory C₂}
    (F G : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (hFG : F = G) (h : F.mapDerivedCategory = G.mapDerivedCategory)
    (K : CochainComplex C₁ ℤ) :
    (reductionSystemFactorOfIso DerivedCategory.Q DerivedCategory.Q
      (F.mapHomologicalComplex (.up ℤ)) (G.mapHomologicalComplex (.up ℤ))
      F.mapDerivedCategory G.mapDerivedCategory
      (NatIso.mapHomologicalComplex (eqToIso hFG) (.up ℤ)) (eqToIso h)
      F.mapDerivedCategoryFactors).hom.app K = G.mapDerivedCategoryFactors.hom.app K := by
  rw [reductionSystemFactorOfIso_hom]
  exact mapDerivedCategoryFactors_congr F G hFG h K


/-- The localization factor transported along an equality of derived functors.
Source: Stacks 05RU. -/
theorem reductionFactorOfIso_mapDerived {C₁ C₂ : Type*} {_ : Category C₁} {_ : Abelian C₁}
    {_ : HasDerivedCategory C₁} {_ : Category C₂} {_ : Abelian C₂} {_ : HasDerivedCategory C₂}
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

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The projection-normalized completed coefficient comparison is the ordinary one.
Source: Stacks 03CO. -/
theorem podReindexingCoefficient_eq {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
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
    change _ ≫ limit.π (integralCoefficientSheafSystem l E X) (op n) = _
    have hm : (sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        ((isoSectionwiseInverseImage g CommRingCat.{u + 1}).map
          (completedIntegralCommRingProjectionUnrestricted l E Y n)) =
        (isoSectionwiseInverseImage g RingCat.{u + 1}).map
          ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (completedIntegralCommRingProjectionUnrestricted l E Y n)) := rfl
    simp only [Functor.map_comp, hm, hπ, hc.1 n] at hn
    exact hn
  · exact (isoReductionCompletedMap_existsUnique l E g).exists.choose_spec

/-- The coefficient-normalized reindexing functor is the ordinary relabelling functor.
Source: Stacks 03CO and 03D6. -/
theorem podReindexingFunctor_eq {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    podReindexingFunctor l E g none = isoReductionIntegralInverse l E g := by
  simp only [podReindexingFunctor, isoReductionIntegralInverse, podReindexingCoefficient_eq]


/-- Generator formulas are compatible with an equality of modules.
Source: Stacks 06YY. -/
theorem reductionEvaluation_eqToHom (W : Scheme.{u}) {M N : scalarReductionSource l E W}
    (h : M = N) (n : ℕ) (U : W.ProEt)
    (c : (integralCoefficientCommRingSheaf l E W n).obj.obj (op U))
    (x : M.val.obj (op U)) (y : N.val.obj (op U)) (hxy : HEq x y) :
    ((pullbackTensorOrdinaryReduction l E W).map (eqToHom h)).val.app (op (n, U))
        (((pullbackTensorReductionEvaluation l E W n).hom.app M).val.app (op U)
          (unrestrictedTowerTensorSection l E W n M (op U) c x)) =
      ((pullbackTensorReductionEvaluation l E W n).hom.app N).val.app (op U)
        (unrestrictedTowerTensorSection l E W n N (op U) c y) := by
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

-- The representative assembles several large localized and sectionwise comparisons.
/-- The whole-system reduction mate has an ordinary quotient representative.
Source: blueprint dual-Tate compatibility Steps 1, 2 and 4; Stacks 03EL, 07A6, 0941.
(blueprint: lem-pod-reduction-reindex-unary-model). -/
theorem unary_model_core {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : PodCompletionReindex l E g) (hA : PodCompletionReindex.Laws l E g A)
    (h : podReindexingDerivedFunctor l E g none = podOrdinaryReindex l E g)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    ∃ (hFP : integralOperationsGoodComplex l E X ((F[g]).obj P.obj))
      (β : (I[g]).obj ((R[Y]).obj P.obj) ≅ (R[X]).obj ((F[g]).obj P.obj)),
      Generators l E g P.obj β ∧
      (integralComparisonDerivedSequencePullback l E g).map
          ((pullbackTensorReductionModel l E Y).hom.app P) ≫
        (systemFactor l E g).hom.app
          ((R[Y]).obj P.obj) ≫ (systemQ l E X).map β.hom =
      A.reduction.hom.app ((podReindexingQ l E Y none).obj P.obj) ≫
        (podReindexCalculus l E X).reduction.map ((factor l E g h).hom.app P.obj) ≫
        (pullbackTensorReductionModel l E X).hom.app ⟨(F[g]).obj P.obj, hFP⟩ := by
  let MY := referenceOrdinaryModel l E Y
  let MX := referenceOrdinaryModel l E X
  obtain ⟨b, hb⟩ := reindexNormalized_exists l E g MY MX
  obtain ⟨DY, hDY⟩ := referenceDerivedModel l E Y
  obtain ⟨DX, hDX⟩ := referenceDerivedModel l E X
  have hF := podReindexingFunctor_eq l E g
  let e₀ := NatIso.mapHomologicalComplex (eqToIso hF) (.up ℤ)
  have hFP : integralOperationsGoodComplex l E X ((F[g]).obj P.obj) := by
    have hP : (F[g]).obj P.obj = (isoReductionIntegralComplex l E g).obj P.obj := by
      simp only [podReindexingComplexFunctor, hF]
    rw [hP]
    exact A.good P.obj P.property
  refine ⟨hFP, (NatIso.mapHomologicalComplex b (.up ℤ)).app P.obj ≪≫
    (R[X]).mapIso (e₀.app P.obj).symm, ?_, ?_⟩
  · intro n i U a x
    simp only [Iso.trans_hom, HomologicalComplex.comp_f, Functor.mapIso_hom, Iso.app_hom,
      Iso.symm_hom, NatIso.mapHomologicalComplex_hom_app_f, SheafOfModules.comp_val,
      PresheafOfModules.comp_app]
    simp only [ConcreteCategory.comp_apply]
    have ht := reindexNormalized_tensor l E g MY MX b hb (P.obj.X i) n U a x
    have ht' := congrArg (fun z ↦
      ((((pullbackTensorOrdinaryReduction l E X).mapHomologicalComplex
        (.up ℤ)).map (e₀.app P.obj).inv).f i).val.app (op (n, U)) z) ht
    refine ht'.trans ?_
    simp only [Functor.mapHomologicalComplex_map_f, Iso.app_inv, e₀,
      NatIso.mapHomologicalComplex_inv_app_f, eqToIso.inv, eqToHom_app]
    exact reductionEvaluation_eqToHom l E X
      (M := (isoReductionIntegralInverse l E g).obj (P.obj.X i))
      (N := ((F[g]).obj P.obj).X i) (Functor.congr_obj hF.symm _) n U _ x x HEq.rfl
  · have hn := podReindexReduction_quotient_normalization l E g A hA MY MX DY DX b hb P
    have hsys : (systemFactor l E g).hom.app ((R[Y]).obj P.obj) =
        (integralComparisonSequencePullback l E g).mapDerivedCategoryFactors.hom.app
          ((R[Y]).obj P.obj) := by
      exact reductionSystemFactorOfIso_mapDerived
        (C₁ := coefficientSequenceModules l E Y) (C₂ := coefficientSequenceModules l E X)
        _ _ (inverse_eq l E g) (derived_eq l E g) _
    have hfac := reductionFactorOfIso_mapDerived (podReindexingFunctor l E g none)
      (isoReductionIntegralInverse l E g) (podOrdinaryReindex l E g) hF h rfl P.obj
    have hfac2 : (factor l E g h).hom.app P.obj ≫ _ = _ := hfac
    simp only [eqToHom_refl, Category.id_comp] at hfac2
    have hfac3 := (Iso.eq_comp_inv
      ((DerivedCategory.Q (C := scalarReductionSource l E X)).mapIso (e₀.app P.obj))).2 hfac2
    have key := congrArg (fun z ↦ A.reduction.hom.app (DerivedCategory.Q.obj P.obj) ≫ z ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex b (.up ℤ)).hom.app P.obj)) hn
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
      Iso.hom_inv_id_app_assoc] at key
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at key
    have hnat := DX.reductionComparison.naturality (e₀.inv.app P.obj)
    rw [hsys]
    rw [← hDY P, ← hDX ⟨(F[g]).obj P.obj, hFP⟩, hfac3, Functor.map_comp, Category.assoc]
    erw [hnat, reassoc_of% key]
    rw [Iso.trans_hom, Functor.map_comp]
    rfl

end WeilConjectures.PodReductionRepresentatives
