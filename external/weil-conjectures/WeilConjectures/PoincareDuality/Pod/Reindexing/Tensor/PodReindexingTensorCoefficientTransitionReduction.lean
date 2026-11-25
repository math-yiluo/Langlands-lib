/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexCoefficientTransition
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.PoincareDuality.Pod.PodOrdinaryQuotientTransitionCube
import WeilConjectures.PoincareDuality.Pod.PodScalarReductionQuotientNormalization
import WeilConjectures.PoincareDuality.Pod.Reindex.PodReindexReductionQuotientNormalization
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitFixedCalculusModels
import all WeilConjectures.TraceFormula.Primitive.PrimitiveQuotientScalarModelExistence

/-! # Reduction square component of the normalized coefficient transition

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL, 06YY, 0941
(blueprint: lem-pod-reindexing-tensor-coefficient-transition-core-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
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

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem derivedSquare_factors
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
    (F₁ : A ⥤ B) (F₂ : B ⥤ D) (G₁ : A ⥤ C) (G₂ : C ⥤ D)
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) (P : CochainComplex A ℤ) :
    F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app P) ≫
        F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) =
      (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj P) ≫
        G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app P) ≫
        G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj P) := by
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso F₁ F₂).inv.app
    (DerivedCategory.Q.obj P))).1
  erw [Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc,
    ← Functor.mapDerivedCategoryNatIso_fac e P]
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors]

private theorem goodRepresentative_exists (W : AlgebraicGeometry.Scheme.{u})
    (K : DerivedCategory (integralTowerModules.{u, u} l E W)) :
    ∃ P : (integralOperationsGoodComplex.{u, u} l E W).FullSubcategory,
      Nonempty (DerivedCategory.Q.obj P.obj ≅ K) := by
  let A : CochainComplex (integralTowerModules.{u, u} l E W) ℤ :=
    DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj A ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let h := CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
    (C := W.ProEt) (J := ProEt.topology W)
    (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E W) A
  let P := h.choose
  let p := h.choose_spec.choose
  let hp := h.choose_spec.choose_spec
  let : QuasiIso p := hp.2.2.1
  exact ⟨⟨P, hp.1, fun i ↦
    (exactFunctor (integralTowerModules.{u, u} l E W)
      (integralTowerModules.{u, u} l E W)).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1}
        (completedIntegralCommRingSheafUnrestricted.{u, u} l E W) (P.X i)).symm
      (hp.2.1 i)⟩,
    ⟨asIso (DerivedCategory.Q.map p) ≪≫ e⟩⟩

private theorem transition_cube_descent
    {R A B C D E₀ E₁ L₀ L₁ : Type*}
    [Category R] [Category A] [Category B] [Category C] [Category D]
    [Category E₀] [Category E₁] [Category L₀] [Category L₁]
    (Q : R ⥤ A) (hQ : ∀ K : A, ∃ P : R, Nonempty (Q.obj P ≅ K))
    (p : A ⥤ B) (aX : B ⥤ D) (aY : A ⥤ C) (pL : C ⥤ D)
    (rE : A ⥤ E₀) (rEX : B ⥤ E₁) (rL : C ⥤ L₀) (rLX : D ⥤ L₁)
    (q : E₀ ⥤ E₁) (qL : L₀ ⥤ L₁) (sX : E₁ ⥤ L₁) (sY : E₀ ⥤ L₀)
    (γX : aX ⋙ rLX ⟶ rEX ⋙ sX) (d : p ⋙ rEX ⟶ rE ⋙ q)
    (τ : q ⋙ sX ⟶ sY ⋙ qL) (δ : p ⋙ aX ⟶ aY ⋙ pL)
    (dL : pL ⋙ rLX ⟶ rL ⋙ qL) (γY : aY ⋙ rL ⟶ rE ⋙ sY)
    (h : ∀ P : R,
      γX.app (p.obj (Q.obj P)) ≫ sX.map (d.app (Q.obj P)) ≫
          τ.app (rE.obj (Q.obj P)) =
        rLX.map (δ.app (Q.obj P)) ≫ dL.app (aY.obj (Q.obj P)) ≫
          qL.map (γY.app (Q.obj P))) :
    ∀ K : A, γX.app (p.obj K) ≫ sX.map (d.app K) ≫ τ.app (rE.obj K) =
      rLX.map (δ.app K) ≫ dL.app (aY.obj K) ≫ qL.map (γY.app K) := by
  let α : p ⋙ aX ⋙ rLX ⟶ rE ⋙ sY ⋙ qL :=
    whiskerLeft p γX ≫ whiskerRight d sX ≫ whiskerLeft rE τ
  let β : p ⋙ aX ⋙ rLX ⟶ rE ⋙ sY ⋙ qL :=
    whiskerRight δ rLX ≫ whiskerLeft aY dL ≫ whiskerRight γY qL
  intro K
  obtain ⟨P, ⟨e⟩⟩ := hQ K
  change α.app K = β.app K
  apply (cancel_epi ((p ⋙ aX ⋙ rLX).map e.hom)).1
  rw [α.naturality, β.naturality]
  exact congrArg (fun z ↦ z ≫ (rE ⋙ sY ⋙ qL).map e.hom) (h P)

/-- Paste the scalar, reindexing, and naturality squares in abstract categories,
so the diagram algebra does not unfold the concrete derived sheaf functors. -/
private theorem reduction_cube_pasting
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (R : A ⥤ D) (S : B ⥤ D) (T : C ⥤ D)
    {A₀ A₁ A₂ A₃ A₄ A₅ : A} {B₀ B₁ B₂ B₃ B₄ B₅ : B}
    {C₀ C₁ C₂ C₃ C₄ C₅ : C} {D₀ D₁ D₂ D₃ D₄ D₅ : D}
    {γX : R.obj A₀ ⟶ S.obj B₀} {d : B₀ ⟶ B₁} {τ : S.obj B₁ ⟶ T.obj C₁}
    {δ : A₀ ⟶ A₃} {dL : R.obj A₃ ⟶ T.obj C₀} {γY : C₀ ⟶ C₁}
    {eY : C₁ ⟶ C₂} {εY : C₂ ⟶ C₃} {qfS : T.obj C₃ ⟶ D₃}
    {eE : B₁ ⟶ B₂} {qf : B₂ ⟶ B₃} {εX : S.obj B₃ ⟶ D₂} {τc : D₂ ⟶ D₃}
    {τ' : S.obj B₂ ⟶ T.obj C₂} {fE : A₀ ⟶ A₁} {fX : A₁ ⟶ A₂}
    {eLX : R.obj A₂ ⟶ D₀} {αX : D₀ ⟶ D₁} {sβ : D₁ ⟶ D₂}
    {f : B₀ ⟶ B₄} {eEX : B₄ ⟶ B₅} {βE : B₅ ⟶ B₃}
    {γX' : R.obj A₁ ⟶ S.obj B₄} {εXR : S.obj B₅ ⟶ D₁}
    {pfY : A₃ ⟶ A₄} {fL : A₄ ⟶ A₅} {dL' : R.obj A₄ ⟶ T.obj C₄}
    {fY : C₀ ⟶ C₄} {eLY : C₄ ⟶ C₅} {αY : C₅ ⟶ C₃}
    {qfL : T.obj C₅ ⟶ D₅} {qα : D₅ ⟶ D₃} {bc : A₂ ⟶ A₅}
    {eLX' : R.obj A₅ ⟶ D₄} {mbc : D₀ ⟶ D₄} {βL : D₄ ⟶ D₅}
    (hscalarX : R.map fX ≫ eLX ≫ αX = γX' ≫ S.map eEX ≫ εXR)
    (hscalarY : fY ≫ eLY ≫ αY = γY ≫ eY ≫ εY)
    (hreindexE : f ≫ eEX ≫ βE = d ≫ eE ≫ qf)
    (hreindexL : R.map fL ≫ eLX' ≫ βL = dL' ≫ T.map eLY ≫ qfL)
    (hnτ : S.map eE ≫ τ' = τ ≫ T.map eY)
    (hτ : S.map qf ≫ εX ≫ τc = τ' ≫ T.map εY ≫ qfS)
    (hnγ : R.map fE ≫ γX' = γX ≫ S.map f)
    (hnε : S.map βE ≫ εX = εXR ≫ sβ)
    (hnb : R.map bc ≫ eLX' = eLX ≫ mbc)
    (hnD : R.map pfY ≫ dL' = dL ≫ T.map fY)
    (hnq : T.map αY ≫ qfS = qfL ≫ qα)
    (hb : fE ≫ fX ≫ bc = δ ≫ pfY ≫ fL)
    (hc : αX ≫ sβ ≫ τc = mbc ≫ βL ≫ qα) :
    γX ≫ S.map d ≫ τ ≫ T.map eY ≫ T.map εY ≫ qfS =
      R.map δ ≫ dL ≫ T.map γY ≫ T.map eY ≫ T.map εY ≫ qfS := by
  have hleft : γX ≫ S.map d ≫ τ ≫ T.map eY ≫ T.map εY ≫ qfS =
      R.map fE ≫ R.map fX ≫ eLX ≫ αX ≫ sβ ≫ τc := by
    calc
      _ = γX ≫ S.map (d ≫ eE ≫ qf) ≫ εX ≫ τc := by
        simp only [Functor.map_comp, Category.assoc]
        rw [← reassoc_of% hnτ, ← hτ]
      _ = γX ≫ S.map (f ≫ eEX ≫ βE) ≫ εX ≫ τc := by rw [← hreindexE]
      _ = R.map fE ≫ γX' ≫ S.map eEX ≫ εXR ≫ sβ ≫ τc := by
        simp only [Functor.map_comp, Category.assoc]
        rw [reassoc_of% hnε, ← reassoc_of% hnγ]
      _ = _ := by rw [← reassoc_of% hscalarX]
  have hright : R.map δ ≫ dL ≫ T.map γY ≫ T.map eY ≫ T.map εY ≫ qfS =
      R.map fE ≫ R.map fX ≫ eLX ≫ mbc ≫ βL ≫ qα := by
    calc
      _ = R.map δ ≫ dL ≫ T.map (fY ≫ eLY ≫ αY) ≫ qfS := by
        rw [hscalarY]
        simp only [Functor.map_comp, Category.assoc]
      _ = R.map δ ≫ R.map pfY ≫ dL' ≫ T.map eLY ≫ qfL ≫ qα := by
        simp only [Functor.map_comp, Category.assoc]
        rw [hnq, ← reassoc_of% hnD]
      _ = R.map δ ≫ R.map pfY ≫ R.map fL ≫ eLX' ≫ βL ≫ qα := by
        rw [← reassoc_of% hreindexL]
      _ = R.map fE ≫ R.map fX ≫ R.map bc ≫ eLX' ≫ βL ≫ qα := by
        simpa only [Functor.map_comp, Category.assoc] using
          congrArg (fun z ↦ R.map z ≫ eLX' ≫ βL ≫ qα) hb.symm
      _ = _ := by rw [reassoc_of% hnb]
  rw [hleft, hright, hc]

private theorem good_reduction
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (hD' : PodCompletionReindex.Laws l L g D')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (hpure : ∀ (M : scalarReductionSource l E Y) (U : X.ProEt)
      (x : M.val.obj (op ((proEtaleIsoPostcompose g).obj U)))
      (a : (completedIntegralCoefficientSheafUnrestricted l L Y).obj.obj
        (op ((proEtaleIsoPostcompose g).obj U))),
      (S.ordinary.hom.app M).val.app (op U)
          (integralOrdinaryTensorSection l E L ι X
            ((isoReductionIntegralInverse l E g).obj M) (op U)
            ((isoReductionCompletedMap l L g).hom.hom.app (op U) a) x) =
        integralOrdinaryTensorSection l E L ι Y M
          (op ((proEtaleIsoPostcompose g).obj U)) a x) :
    ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
      (podScalarReduction l E L ι X D'.targetRoos S.target).app
          ((podOrdinaryReindex l E g).obj (DerivedCategory.Q.obj P.obj)) ≫
        (integralComparisonDerivedSequenceScalar l E L ι X).map
          (D.reduction.inv.app (DerivedCategory.Q.obj P.obj)) ≫
        (integralComparisonSystemScalarPullback l E L ι g).hom.app
          ((podReindexCalculus l E Y).reduction.obj (DerivedCategory.Q.obj P.obj)) =
      (podReindexCalculus l L X).reduction.map
          ((S.derived l E L ι g D D').hom.app (DerivedCategory.Q.obj P.obj)) ≫
        D'.reduction.inv.app
          ((integralOrdinaryDerivedScalar l E L ι Y).obj (DerivedCategory.Q.obj P.obj)) ≫
        (integralComparisonDerivedSequencePullback l L g).map
          ((podScalarReduction l E L ι Y D'.sourceRoos S.source).app
            (DerivedCategory.Q.obj P.obj)) := by
  intro P
  obtain ⟨MEY, ⟨DEY⟩⟩ := CompletionUnit.fixedCalculusModels l E Y (podReindexCalculus l E Y)
  obtain ⟨MEX, ⟨DEX⟩⟩ := CompletionUnit.fixedCalculusModels l E X (podReindexCalculus l E X)
  obtain ⟨MLY, ⟨DLY⟩⟩ := CompletionUnit.fixedCalculusModels l L Y (podReindexCalculus l L Y)
  obtain ⟨MLX, ⟨DLX⟩⟩ := CompletionUnit.fixedCalculusModels l L X (podReindexCalculus l L X)
  obtain ⟨αX, αY, βE, βL, hαX, hαY, hβE, hβL, hcube⟩ :=
    podOrdinaryQuotientTransitionCube l E L ι g MEY MEX MLY MLX S.ordinary hpure
  let PR : (integralOperationsGoodComplex l E X).FullSubcategory :=
    ⟨(isoReductionIntegralComplex l E g).obj P.obj, D.good P.obj P.property⟩
  let PS : (integralOperationsGoodComplex l L Y).FullSubcategory :=
    ⟨_, scalarGood l E L ι Y P⟩
  have hscalarX := podScalarReduction_quotient_normalization l E L ι X
    D'.targetRoos S.target MEX MLX DEX DLX αX hαX PR
  have hscalarY := podScalarReduction_quotient_normalization l E L ι Y
    D'.sourceRoos S.source MEY MLY DEY DLY αY hαY P
  have hreindexE := podReindexReduction_quotient_normalization l E g D hD
    MEY MEX DEY DEX βE hβE P
  have hreindexL := podReindexReduction_quotient_normalization l L g D' hD'
    MLY MLX DLY DLX βL hβL PS
  let r := (podReindexCalculus l L X).reduction
  let qL := integralComparisonDerivedSequencePullback l L g
  let sX := integralComparisonDerivedSequenceScalar l E L ι X
  let sY := integralComparisonDerivedSequenceScalar l E L ι Y
  let γX := podScalarReduction l E L ι X D'.targetRoos S.target
  let τ := (integralComparisonSystemScalarPullback l E L ι g).hom
  let C := (MEY.quotient l E Y).obj P.obj
  have hflat : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E Y) C := by
    apply sequenceKFlat_of_evaluations l E Y
    intro n
    exact SheafOfModules.kFlat_iso_independent (integralCoefficientCommRingSheaf l E Y n)
      ((NatIso.mapHomologicalComplex (MEY.evaluation n) (.up ℤ)).app P.obj).symm
      ((coefficientTensorModelPreservation l E Y).1 P.obj P.property.1 n)
  have hτ := (integralComparisonSystemScalarPullback_existsUnique l E L ι g).exists.choose_spec
    C hflat
  have hnτ := τ.naturality (DEY.reductionComparison.app P.obj)
  have hnγ := γX.naturality
    ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app P.obj)
  have hnε := (integralComparisonSequenceScalarModel l E L ι X).ε.naturality
    ((NatIso.mapHomologicalComplex βE (.up ℤ)).inv.app P.obj)
  have hnb := DLX.reductionComparison.naturality
    ((NatIso.mapHomologicalComplex S.ordinary (.up ℤ)).hom.app P.obj)
  have hnD := D'.reduction.inv.naturality
    ((integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.hom.app P.obj)
  have hnq := (integralComparisonSequencePullback l L g).mapDerivedCategoryFactors.hom.naturality
    ((NatIso.mapHomologicalComplex αY (.up ℤ)).inv.app P.obj)
  have hb := derivedSquare_factors (isoReductionIntegralInverse l E g)
    (integralOrdinaryScalar l E L ι X) (integralOrdinaryScalar l E L ι Y)
    (isoReductionIntegralInverse l L g) S.ordinary P.obj
  have hc := congrArg DerivedCategory.Q.map (hcube P.obj)
  simp only [Functor.comp_map] at hnτ hnγ hnε hnb hnD hnq
  simp only [Functor.map_comp] at hc
  have := DEY.reduction_isIso P.obj P.property.1 P.property.2
  have := (integralComparisonSequenceScalarModel l E L ι Y).computes C hflat
  apply (cancel_mono
    (qL.map (sY.map (DEY.reductionComparison.app P.obj)) ≫
      qL.map ((integralComparisonSequenceScalarModel l E L ι Y).ε.app C) ≫
      (integralComparisonSequencePullback l L g).mapDerivedCategoryFactors.hom.app
        (((integralComparisonSequenceScalarModel l E L ι Y).E.mapHomologicalComplex
          (.up ℤ)).obj C))).1
  simp only [Category.assoc]
  exact reduction_cube_pasting r sX qL hscalarX hscalarY hreindexE hreindexL
    hnτ hτ hnγ hnε hnb hnD hnq hb hc

attribute [local irreducible] podReindexCalculus integralComparisonSequenceScalarModel
attribute [local irreducible] integralComparisonSystemScalarPullback podScalarReduction

/-- The reduction square component of a normalized coefficient transition.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL, 06YY, 0941
(blueprint: lem-pod-reindexing-tensor-coefficient-transition-core-reduction).
Proof: choose a flat-term K-flat representative P of K and its whole-system
coherent quotient presentation. The quotient-generator and quotient-transition
laws for D and D′ identify their finite reindexing maps with the actual maps on
these quotients. The formula hpure identifies the two scalar/reindexing routes on
scalar-unit tensor generators. Balancedness extends this to all tensors, and
sheafification gives equality of the maps of module sheaves. Apply this degreewise
to P, retaining the actual quotient transition maps, to obtain equality of strict
systems. The scalar model normalization identifies its cochain scalar counit with
this same generator map, and its realization with the selected Roos comparison.
Thus applying the whole-system counit to the equality of strict maps gives the
claimed equality on P. The good-complex localization and naturality transport it
along a K-flat resolution to K. Expanding podScalarReduction gives the displayed
order of scalar completion, scalar realization, and counit. No choice of a new
completion reindexing family is made: the quotient and realization laws identify
the maps of the supplied D and D′ themselves.

Edge cases: for identity reindexing or identity scalar extension this is the
corresponding normalized identity square. The generator and localization argument
also applies to zero complexes and to the empty scheme; it uses no nonzero section
or nonempty-site assumption.
-/
theorem podReindexingTensorCoefficientTransition_reduction
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (hpure : ∀ (M : scalarReductionSource l E Y) (U : X.ProEt)
      (x : M.val.obj (op ((proEtaleIsoPostcompose g).obj U)))
      (a : (completedIntegralCoefficientSheafUnrestricted l L Y).obj.obj
        (op ((proEtaleIsoPostcompose g).obj U))),
      (S.ordinary.hom.app M).val.app (op U)
          (integralOrdinaryTensorSection l E L ι X
            ((isoReductionIntegralInverse l E g).obj M) (op U)
            ((isoReductionCompletedMap l L g).hom.hom.app (op U) a) x) =
        integralOrdinaryTensorSection l E L ι Y M
          (op ((proEtaleIsoPostcompose g).obj U)) a x) :
    ∀ K : DerivedCategory (scalarReductionSource l E Y),
      (podScalarReduction l E L ι X D'.targetRoos S.target).app
          ((podOrdinaryReindex l E g).obj K) ≫
        (integralComparisonDerivedSequenceScalar l E L ι X).map
          (D.reduction.inv.app K) ≫
        (integralComparisonSystemScalarPullback l E L ι g).hom.app
          ((podReindexCalculus l E Y).reduction.obj K) =
      (podReindexCalculus l L X).reduction.map
          ((S.derived l E L ι g D D').hom.app K) ≫
        D'.reduction.inv.app
          ((integralOrdinaryDerivedScalar l E L ι Y).obj K) ≫
        (integralComparisonDerivedSequencePullback l L g).map
          ((podScalarReduction l E L ι Y D'.sourceRoos S.source).app K) := by
  have _ := hT
  have _ := hT'
  exact transition_cube_descent (integralOperationsGoodLocalization l E Y)
    (goodRepresentative_exists l E Y)
    (podOrdinaryReindex l E g) (integralOrdinaryDerivedScalar l E L ι X)
    (integralOrdinaryDerivedScalar l E L ι Y) (podOrdinaryReindex l L g)
    (podReindexCalculus l E Y).reduction (podReindexCalculus l E X).reduction
    (podReindexCalculus l L Y).reduction (podReindexCalculus l L X).reduction
    (integralComparisonDerivedSequencePullback l E g)
    (integralComparisonDerivedSequencePullback l L g)
    (integralComparisonDerivedSequenceScalar l E L ι X)
    (integralComparisonDerivedSequenceScalar l E L ι Y)
    (podScalarReduction l E L ι X D'.targetRoos S.target) D.reduction.inv
    (integralComparisonSystemScalarPullback l E L ι g).hom
    (S.derived l E L ι g D D').hom D'.reduction.inv
    (podScalarReduction l E L ι Y D'.sourceRoos S.source)
    (good_reduction l E g D hD L ι D' hD' S hpure)

end WeilConjectures
