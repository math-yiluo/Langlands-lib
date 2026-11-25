/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Comparison.IntegralComparisonSystemData
public import WeilConjectures.TraceFormula.Supporting.QuotientSystemMixedCoherenceData
import WeilConjectures.TraceFormula.Scalar.ScalarModelUnit
import WeilConjectures.TraceFormula.Scalar.ScalarModelAssociativity
import WeilConjectures.TraceFormula.Integral.IntegralScalarOrdinaryModelCoherence

/-! # Multiplication and associativity for scalar realization counits

Source: Stacks 06YY and 0941; the scalar normalization calculation in
lem-trf-normalized-integral-scalar-coherence.
(blueprint: lem-trf-integral-scalar-counit-normalization).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

attribute [local instance 5000] integralTowerHasDerivedCategory
attribute [local irreducible] HasDerivedCategory.standard
  integralOrdinaryScalar completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted

private theorem scalarCounit_unit
    {A B : Type*} [Category A] [Category B]
    {R : A ⥤ B} {L : B ⥤ A} (adj : R ⊣ L)
    {K T : A} {S : B} (b : T ⟶ L.obj S) (e : S ⟶ R.obj K) (u : T ⟶ K)
    (h : b ≫ L.map e = u ≫ adj.unit.app K) :
    R.map b ≫ adj.counit.app S ≫ e = R.map u := by
  have hh := congrArg (fun f ↦ R.map f ≫ adj.counit.app (R.obj K)) h
  have hn : R.map (L.map e) ≫ adj.counit.app (R.obj K) =
      adj.counit.app S ≫ e := adj.counit.naturality e
  simpa only [Functor.map_comp, Category.assoc, hn,
    adj.left_triangle_components, Category.comp_id] using hh

private theorem scalarCounit_comp
    {A B : Type*} [Category A] [Category B]
    {R : A ⥤ B} {L : B ⥤ A} (adj : R ⊣ L)
    {T U : A} {S V : B} (b : T ⟶ L.obj S) (c : U ⟶ L.obj V)
    (f : S ⟶ V) (a : T ⟶ U)
    (h : b ≫ L.map f = a ≫ c) :
    R.map b ≫ adj.counit.app S ≫ f =
      R.map a ≫ R.map c ≫ adj.counit.app V := by
  have hh := congrArg (fun g ↦ R.map g ≫ adj.counit.app V) h
  have hn : R.map (L.map f) ≫ adj.counit.app V =
      adj.counit.app S ≫ f := adj.counit.naturality f
  simpa only [Functor.map_comp, Category.assoc, hn] using hh

/-- The reduction mates of the prescribed scalar realizations respect the published
completed multiplication and associator, before introducing any scheme pullback.
Source: Stacks sites-cohomology.tex, lemma-derived-base-change (06YY) and
lemma-derived-limit-is-ok (0941), and the scalar normalization paragraph of
lem-trf-normalized-integral-scalar-coherence.

Proof: identify finite-free ordinary scalar extension with the universal derived
change-of-rings model by its sheafified pure tensor formula and its universal
K-flat counit. The identification carries multiplication to multiplication and
successive extension to the tensor associator: on sections the two expressions
send s tensor x to sx and t tensor (s tensor x) to t*j(s) tensor x, respectively.
These formulas commute with all restrictions and differentials. Localization on
flat-term K-flat resolutions preserves the equations and determines the derived
comparisons. The completion maps agree since both have the actual quotient
augmentation in the unshifted Roos coordinate and zero shifted coordinate.
Apply scalarModelUnit and scalarModelAssociativity through these identifications.
Cancel the completion isomorphisms at the complete input and its scalar extension.
For the unit, the resulting equation is b times limit(system multiplication)
= completed multiplication times the reconstruction unit. Transpose it under the
actual reduction/limit adjunction; counit naturality and the left triangle give
the first displayed equation. For the tower, move the first realization through
the second counit by naturality. Transpose the associator equation: the composite
mate is c_LM at T_EL(K), followed by S_LM(c_EL), followed by system associativity.
The other mate is reduction of the completed associator. This gives the second
equation. This argument applies to equal fields and identity embeddings, zero
objects, and arbitrary ramification; no finite quotient map is assumed flat.
(blueprint: lem-trf-integral-scalar-counit-normalization). -/
theorem integralScalarCounitNormalization
    (l : ℕ) [Fact l.Prime] (D : IntegralComparisonSystem.{u} l) :
    (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
      (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
      (K : sfIntegralConstructibleCategory l E X),
      (integralComparisonScalarCounit l E E (AlgHom.id ℚ_[l] E) X
        ((D.coefficient E).system X) ((D.coefficient E).system X)
        ((D.coefficient E).roos X) ((D.scalar E E (AlgHom.id ℚ_[l] E)).model X)).app
          K.obj ≫
        (integralComparisonSystemScalarUnit l E X).hom.app
          (((D.coefficient E).system X).reduction.obj K.obj) =
      ((D.coefficient E).system X).reduction.map
        (integralComparisonScalarUnit l E X K).hom) ∧
    (∀ (E L M : Type u) [Field E] [Algebra ℚ_[l] E]
      [FiniteDimensional ℚ_[l] E] [Field L] [Algebra ℚ_[l] L]
      [FiniteDimensional ℚ_[l] L] [Field M] [Algebra ℚ_[l] M]
      [FiniteDimensional ℚ_[l] M] (ι : E →ₐ[ℚ_[l]] L) (j : L →ₐ[ℚ_[l]] M)
      (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
      (K : sfIntegralConstructibleCategory l E X),
      (integralComparisonScalarCounit l L M j X
        ((D.coefficient L).system X) ((D.coefficient M).system X)
        ((D.coefficient M).roos X) ((D.scalar L M j).model X)).app
          ((integralScalarExtension l E L ι X).obj K.obj) ≫
        (integralComparisonDerivedSequenceScalar l L M j X).map
          ((integralComparisonScalarCounit l E L ι X
            ((D.coefficient E).system X) ((D.coefficient L).system X)
            ((D.coefficient L).roos X) ((D.scalar E L ι).model X)).app K.obj) ≫
        (integralComparisonSystemScalarComposition l E L M ι j X).hom.app
          (((D.coefficient E).system X).reduction.obj K.obj) =
      ((D.coefficient M).system X).reduction.map
          (integralComparisonScalarAssociator l E L ι M j X K).hom ≫
        (integralComparisonScalarCounit l E M (j.comp ι) X
          ((D.coefficient E).system X) ((D.coefficient M).system X)
          ((D.coefficient M).roos X) ((D.scalar E M (j.comp ι)).model X)).app K.obj) := by
  constructor
  · intro E _ _ _ X _ K
    obtain ⟨e, hχ, hu⟩ := (integralScalarOrdinaryModelCoherence l).1 E X
    let SE := (D.coefficient E).system X
    let b := (D.scalar E E (AlgHom.id ℚ_[l] E)).model X
    let v := (integralComparisonSystemScalarUnit l E X).hom.app (SE.reduction.obj K.obj)
    have hχK := NatTrans.congr_app hχ K.obj
    have huK := NatTrans.congr_app hu K.obj
    have hraw : (scalarCompletion l E E (AlgHom.id ℚ_[l] E) X).app K.obj ≫
        b.realization.hom.app K.obj ≫ (coefficientSequenceLimit l E X).map v =
      (integralOrdinaryDerivedScalarUnit l E X).hom.app K.obj ≫
        SE.adjunction.unit.app K.obj := by
      calc
        _ = e.hom.app K.obj ≫
            ((completedScalarComparison.{u, u} l E E (AlgHom.id ℚ_[l] E) X).app K.obj ≫
              b.realization.hom.app K.obj ≫ (coefficientSequenceLimit l E X).map v) := by
          rw [← hχK]
          simp only [NatTrans.comp_app, Category.assoc]
        _ = e.hom.app K.obj ≫
            ((CompletedLineTensor.ordinaryUnit l E X).hom.app K.obj ≫
              SE.adjunction.unit.app K.obj) := by
          rw [scalarModelUnit l E X SE ((D.coefficient E).roos X) b K.obj]
        _ = _ := by
          simpa only [NatTrans.comp_app, Category.assoc] using
            congrArg (· ≫ SE.adjunction.unit.app K.obj) huK
    let χ := scalarCompletionIso l E E (AlgHom.id ℚ_[l] E) X K.obj K.property.1
    change χ.hom ≫ b.realization.hom.app K.obj ≫ (coefficientSequenceLimit l E X).map v =
      (integralOrdinaryDerivedScalarUnit l E X).hom.app K.obj ≫
        SE.adjunction.unit.app K.obj at hraw
    have hreal : b.realization.hom.app K.obj ≫ (coefficientSequenceLimit l E X).map v =
        (integralComparisonScalarUnit l E X K).hom ≫ SE.adjunction.unit.app K.obj := by
      apply (cancel_epi χ.hom).mp
      simp only [integralComparisonScalarUnit, Iso.trans_hom, Iso.symm_hom,
        Iso.app_hom, Category.assoc]
      change χ.hom ≫ (b.realization.hom.app K.obj ≫
        (coefficientSequenceLimit l E X).map v) =
        χ.hom ≫ (χ.inv ≫ (integralOrdinaryDerivedScalarUnit l E X).hom.app K.obj ≫
          SE.adjunction.unit.app K.obj)
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hraw
    simpa only [SE, b, v, integralComparisonScalarCounit, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_obj,
      Category.assoc] using scalarCounit_unit SE.adjunction (b.realization.hom.app K.obj) v
        (integralComparisonScalarUnit l E X K).hom hreal
  · intro E L M _ _ _ _ _ _ _ _ _ ι j X _ K
    obtain ⟨eEL, eLM, eEM, hχEL, hχLM, hχEM, ha⟩ :=
      (integralScalarOrdinaryModelCoherence l).2 E L M ι j X
    let SE := (D.coefficient E).system X
    let SL := (D.coefficient L).system X
    let SM := (D.coefficient M).system X
    let bEL := (D.scalar E L ι).model X
    let bLM := (D.scalar L M j).model X
    let bEM := (D.scalar E M (j.comp ι)).model X
    let OEL := integralOrdinaryDerivedScalar l E L ι X
    let OLM := integralOrdinaryDerivedScalar l L M j X
    let CLM := completedDerivedScalarExtension.{u, u} l L M j X
    let TEL := integralScalarExtension l E L ι X
    let TLM := integralScalarExtension l L M j X
    let SLM := integralComparisonDerivedSequenceScalar l L M j X
    let LM := coefficientSequenceLimit l M X
    let v := (integralComparisonSystemScalarComposition l E L M ι j X).hom.app
      (SE.reduction.obj K.obj)
    let cEL := (integralComparisonScalarCounit l E L ι X SE SL
      ((D.coefficient L).roos X) bEL).app K.obj
    let w := TLM.map (bEL.realization.hom.app K.obj) ≫
      bLM.realization.hom.app
        ((coefficientSequenceLimit l L X).obj
          ((integralComparisonDerivedSequenceScalar l E L ι X).obj (SE.reduction.obj K.obj))) ≫
      LM.map (SLM.map (SL.adjunction.counit.app
        ((integralComparisonDerivedSequenceScalar l E L ι X).obj (SE.reduction.obj K.obj)))) ≫
      LM.map v
    have hχ1 := NatTrans.congr_app hχEL K.obj
    have hχ2 := NatTrans.congr_app hχLM (TEL.obj K.obj)
    have hχ3 := NatTrans.congr_app hχEM K.obj
    dsimp only [NatTrans.comp_app] at hχ1 hχ2 hχ3
    have hprefix : eLM.hom.app (OEL.obj K.obj) ≫ CLM.map (eEL.hom.app K.obj) ≫
        CLM.map ((completedScalarComparison.{u, u} l E L ι X).app K.obj) ≫
        (completedScalarComparison.{u, u} l L M j X).app (TEL.obj K.obj) =
      OLM.map ((scalarCompletion l E L ι X).app K.obj) ≫
        (scalarCompletion l L M j X).app (TEL.obj K.obj) := by
      rw [← Functor.map_comp_assoc, hχ1, ← eLM.hom.naturality_assoc]
      erw [hχ2]
    have hassoc : eLM.hom.app (OEL.obj K.obj) ≫ CLM.map (eEL.hom.app K.obj) ≫
        (CompletedLineTensor.associatorData l E X L ι M j).derived.hom.app K.obj =
      (integralOrdinaryDerivedScalarComp l E L ι X M j).hom.app K.obj ≫ eEM.hom.app K.obj := by
      have hh := congrArg (fun z ↦ z.hom.app K.obj) ha
      simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
        Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app] using hh
    have hmodel := scalarModelAssociativity l E L M ι j X SE SL
      ((D.coefficient L).roos X) ((D.coefficient M).roos X) bEL bLM bEM K.obj
    change CLM.map ((completedScalarComparison.{u, u} l E L ι X).app K.obj) ≫
      (completedScalarComparison.{u, u} l L M j X).app (TEL.obj K.obj) ≫ w =
      (CompletedLineTensor.associatorData l E X L ι M j).derived.hom.app K.obj ≫
        (completedScalarComparison.{u, u} l E M (j.comp ι) X).app K.obj ≫
          bEM.realization.hom.app K.obj at hmodel
    have hraw : OLM.map ((scalarCompletion l E L ι X).app K.obj) ≫
        (scalarCompletion l L M j X).app (TEL.obj K.obj) ≫ w =
      (integralOrdinaryDerivedScalarComp l E L ι X M j).hom.app K.obj ≫
        (scalarCompletion l E M (j.comp ι) X).app K.obj ≫ bEM.realization.hom.app K.obj := by
      calc
        _ = (eLM.hom.app (OEL.obj K.obj) ≫ CLM.map (eEL.hom.app K.obj) ≫
            CLM.map ((completedScalarComparison.{u, u} l E L ι X).app K.obj) ≫
            (completedScalarComparison.{u, u} l L M j X).app (TEL.obj K.obj)) ≫ w := by
          rw [hprefix]
          simp only [Category.assoc]
        _ = (eLM.hom.app (OEL.obj K.obj) ≫ CLM.map (eEL.hom.app K.obj)) ≫
            ((CompletedLineTensor.associatorData l E X L ι M j).derived.hom.app K.obj ≫
              (completedScalarComparison.{u, u} l E M (j.comp ι) X).app K.obj ≫
              bEM.realization.hom.app K.obj) := by
          simpa only [w, Category.assoc] using
            congrArg ((eLM.hom.app (OEL.obj K.obj) ≫ CLM.map (eEL.hom.app K.obj)) ≫ ·) hmodel
        _ = _ := by
          simpa only [Category.assoc, reassoc_of% hχ3] using
            congrArg (· ≫ (completedScalarComparison.{u, u} l E M (j.comp ι) X).app K.obj ≫
              bEM.realization.hom.app K.obj) hassoc
    let χEL := scalarCompletionIso l E L ι X K.obj K.property.1
    let χLM := scalarCompletionIso l L M j X (TEL.obj K.obj)
      (((integralComparisonConstructibleScalar l E L ι X).obj K).property.1)
    let χEM := scalarCompletionIso l E M (j.comp ι) X K.obj K.property.1
    change OLM.map χEL.hom ≫ χLM.hom ≫ w =
      (integralOrdinaryDerivedScalarComp l E L ι X M j).hom.app K.obj ≫
        χEM.hom ≫ bEM.realization.hom.app K.obj at hraw
    have hreal0 : w = (integralComparisonScalarAssociator l E L ι M j X K).hom ≫
        bEM.realization.hom.app K.obj := by
      apply (cancel_epi χLM.hom).mp
      apply (cancel_epi (OLM.map χEL.hom)).mp
      simp only [integralComparisonScalarAssociator, Iso.trans_hom, Iso.symm_hom,
        Functor.mapIso_hom, Iso.app_hom, Category.assoc]
      change OLM.map χEL.hom ≫ (χLM.hom ≫ w) =
        OLM.map χEL.hom ≫ (χLM.hom ≫ (χLM.inv ≫ OLM.map χEL.inv ≫
          (integralOrdinaryDerivedScalarComp l E L ι X M j).hom.app K.obj ≫
            χEM.hom ≫ bEM.realization.hom.app K.obj))
      simpa only [Category.assoc, Iso.hom_inv_id_assoc,
        ← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
        Category.id_comp] using hraw
    have hreal : bLM.realization.hom.app (TEL.obj K.obj) ≫
        LM.map (SLM.map cEL ≫ v) =
      (integralComparisonScalarAssociator l E L ι M j X K).hom ≫
        bEM.realization.hom.app K.obj := by
      rw [← hreal0]
      have hn := bLM.realization.hom.naturality (bEL.realization.hom.app K.obj)
      dsimp only [Functor.comp_map] at hn
      simp only [w, cEL, integralComparisonScalarCounit, NatTrans.comp_app,
        Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
      simpa only [TEL, TLM, LM, SLM, SE, SL, Functor.comp_obj,
        integralScalarExtension, integralScalarExtensionOfUniverses, Category.assoc] using congrArg
        (fun f ↦ f ≫ LM.map (SLM.map (SL.adjunction.counit.app
          ((integralComparisonDerivedSequenceScalar l E L ι X).obj
            (SE.reduction.obj K.obj)))) ≫ LM.map v) hn.symm
    simpa only [cEL, SE, SL, SM, bEL, bLM, bEM, TEL, SLM, v,
      integralComparisonScalarCounit, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.comp_obj, Category.assoc] using
      scalarCounit_comp SM.adjunction (bLM.realization.hom.app (TEL.obj K.obj))
        (bEM.realization.hom.app K.obj) (SLM.map cEL ≫ v)
        (integralComparisonScalarAssociator l E L ι M j X K).hom hreal

end WeilConjectures
