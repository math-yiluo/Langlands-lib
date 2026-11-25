/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedOpenTensor.CompletedOpenTensorRepresentativeData
public import WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenSemilinearTensorModel
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import WeilConjectures.SmoothPurity.CompletedOpenTensor.CompletedOpenTensorContext
import WeilConjectures.SmoothPurity.CompletedOpenTensor.OpenTensorOrdinaryDescent
import WeilConjectures.SixFunctors.CanonicalOpenRestriction.OpenRestrictionGoodComplex
import WeilConjectures.SixFunctors.OpenSemilinearTensor.OrdinaryReductionAugmentedComputation
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement

/-! # Compatible representatives for strict open tensors -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.CompletedOpenTensor
open IntegralOpenReduction

attribute [local irreducible] IntegralOnSlice.duality SheafOfModules.monoidalCategory
  HasDerivedCategory.standard

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U V : Scheme.{t}} (j : U ⟶ V) [IsOpenImmersion j]

private theorem computation_hom_unique (W : Scheme.{t})
    (S : CoefficientDerivedSystemCalculus l E W)
    (A : OpenSemilinearTensor.OrdinaryReduction l E W)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E W) P)
    (c d : OpenSemilinearTensor.Computation l E S A P hP) :
    c.iso.hom = d.iso.hom := by
  apply (S.adjunction.homEquiv _ _).injective
  obtain ⟨a, ha, he⟩ := c.augmentation
  obtain ⟨b, hb, hf⟩ := d.augmentation
  have hab : a = b := by
    apply HomologicalComplex.hom_ext
    intro i
    apply NatTrans.ext
    funext n
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact eq_of_heq ((ha i n.unop W x).trans (hb i n.unop W x).symm)
  rw [he, hf, hab]

private theorem strictChain_components (C : Context l E j)
    (P : CochainComplex (scalarReductionSource l E U) ℤ)
    (Q : CochainComplex (scalarReductionSource l E V) ℤ) (n : ℕ) (d : ℤ) :
    (coefficientSequenceEvaluation l E V n).map ((strictChain l E j C P Q).hom.f d) ≫
        (extensionEvaluation l E j C.operations n).hom.app
          (((C.ordinaryU.functor.mapHomologicalComplex (.up ℤ)).obj
            (openComplex l E j C P Q)).X d) ≫
        (finiteExtension l E j C.operations n).map
          ((C.ordinaryU.complexEvaluation l E (openComplex l E j C P Q) n).hom.f d) =
      (C.ordinaryV.complexEvaluation l E (sourceComplex l E j C P Q) n).hom.f d ≫
        (scalarReductionExtension l E V n).map
          ((C.strictOpen.totalComparison.chain P Q).hom.f d) ≫
        (C.coefficients.ordinary n).hom.app ((openComplex l E j C P Q).X d) := by
  change (coefficientSequenceEvaluation l E V n).map
      (C.ordinaryV.functor.map ((C.strictOpen.totalComparison.chain P Q).hom.f d) ≫
        C.strictOpen.ordinary.hom.app ((openComplex l E j C P Q).X d)) ≫
      (extensionEvaluation l E j C.operations n).hom.app
        (C.ordinaryU.functor.obj ((openComplex l E j C P Q).X d)) ≫
      (finiteExtension l E j C.operations n).map
        ((C.ordinaryU.evaluation n).hom.app ((openComplex l E j C P Q).X d)) =
    (C.ordinaryV.evaluation n).hom.app ((sourceComplex l E j C P Q).X d) ≫
      (scalarReductionExtension l E V n).map
        ((C.strictOpen.totalComparison.chain P Q).hom.f d) ≫
      (C.coefficients.ordinary n).hom.app ((openComplex l E j C P Q).X d)
  rw [Functor.map_comp, Category.assoc,
    C.strictOpen.components ((openComplex l E j C P Q).X d) n]
  have hn := (C.ordinaryV.evaluation n).hom.naturality
    ((C.strictOpen.totalComparison.chain P Q).hom.f d)
  change (coefficientSequenceEvaluation l E V n).map
      (C.ordinaryV.functor.map ((C.strictOpen.totalComparison.chain P Q).hom.f d)) ≫
      (C.ordinaryV.evaluation n).hom.app
        ((extension l E j C.operations).obj ((openComplex l E j C P Q).X d)) =
    (C.ordinaryV.evaluation n).hom.app ((sourceComplex l E j C P Q).X d) ≫
      (scalarReductionExtension l E V n).map
        ((C.strictOpen.totalComparison.chain P Q).hom.f d) at hn
  simpa only [Category.assoc] using
    congrArg (fun f ↦ f ≫
      (C.coefficients.ordinary n).hom.app ((openComplex l E j C P Q).X d))
      hn

private theorem strictChain_augmentation (C : Context l E j)
    (P : CochainComplex (scalarReductionSource l E U) ℤ)
    (Q : CochainComplex (scalarReductionSource l E V) ℤ)
    (n : ℕ) (d : ℤ) (W : V.ProEtᵒᵖ)
    (x : ((sourceComplex l E j C P Q).X d).val.obj W) :
    ((finiteExtension l E j C.operations n).map
      ((C.ordinaryU.complexEvaluation l E (openComplex l E j C P Q) n).hom.f d)).val.app W
      (((extensionEvaluation l E j C.operations n).hom.app
        (((C.ordinaryU.functor.mapHomologicalComplex (.up ℤ)).obj
          (openComplex l E j C P Q)).X d)).val.app W
        (((coefficientSequenceEvaluation l E V n).map
          ((strictChain l E j C P Q).hom.f d)).val.app W
          (((C.ordinaryV.complexEvaluation l E (sourceComplex l E j C P Q) n).inv.f d).val.app
            W (coefficientIntegralScalarUnitSection l E V n
              ((sourceComplex l E j C P Q).X d) W x)))) =
      ((C.coefficients.ordinary n).hom.app ((openComplex l E j C P Q).X d)).val.app W
        (coefficientIntegralScalarUnitSection l E V n
          ((extension l E j C.operations).obj ((openComplex l E j C P Q).X d)) W
          (((C.strictOpen.totalComparison.chain P Q).hom.f d).val.app W x)) := by
  have h := congrArg (fun f ↦ f.val.app W
      (((C.ordinaryV.complexEvaluation l E (sourceComplex l E j C P Q) n).inv.f d).val.app
        W (coefficientIntegralScalarUnitSection l E V n
          ((sourceComplex l E j C P Q).X d) W x)))
    (strictChain_components l E j C P Q n d)
  have hc := congrArg (fun f ↦ f.val.app W
      (coefficientIntegralScalarUnitSection l E V n
        ((sourceComplex l E j C P Q).X d) W x))
    (congrArg (fun f ↦ f.f d)
      (C.ordinaryV.complexEvaluation l E (sourceComplex l E j C P Q) n).inv_hom_id)
  have hn := congrArg (fun f ↦ f.val.app W x)
    ((coefficientOrdinaryScalarAdjunction l E V n).unit.naturality
      ((C.strictOpen.totalComparison.chain P Q).hom.f d))
  change _ = _ at h
  change ((C.ordinaryV.evaluation n).hom.app ((sourceComplex l E j C P Q).X d)).val.app W
    (((C.ordinaryV.evaluation n).inv.app ((sourceComplex l E j C P Q).X d)).val.app W
      (coefficientIntegralScalarUnitSection l E V n
        ((sourceComplex l E j C P Q).X d) W x)) =
    coefficientIntegralScalarUnitSection l E V n ((sourceComplex l E j C P Q).X d) W x at hc
  change coefficientIntegralScalarUnitSection l E V n
      ((extension l E j C.operations).obj ((openComplex l E j C P Q).X d)) W
      (((C.strictOpen.totalComparison.chain P Q).hom.f d).val.app W x) =
    ((scalarReductionExtension l E V n).map
      ((C.strictOpen.totalComparison.chain P Q).hom.f d)).val.app W
        (coefficientIntegralScalarUnitSection l E V n _ W x) at hn
  exact h.trans
      (congrArg (fun y ↦
        ((C.coefficients.ordinary n).hom.app ((openComplex l E j C P Q).X d)).val.app W
          (((scalarReductionExtension l E V n).map
            ((C.strictOpen.totalComparison.chain P Q).hom.f d)).val.app W y)) hc |>.trans
          (congrArg (fun y ↦
            ((C.coefficients.ordinary n).hom.app
              ((openComplex l E j C P Q).X d)).val.app W y) hn.symm))

private theorem tensorSystemPaste
    {A B D E' : Type*} [Category* A] [Category* B] [Category* D] [Category* E']
    (F : A ⥤ D) (G : B ⥤ E') (j₀ : B ⥤ A) (J : E' ⥤ D)
    (r : j₀ ⋙ F ≅ G ⋙ J)
    {X Y Z : A} {H K : B} {T V₀ W₀ D₀ : D} {S' U' : E'}
    (qV : F.obj X ≅ T) (qU : G.obj H ≅ S')
    (γ : X ⟶ j₀.obj H) (b : H ⟶ K) (e : j₀.obj K ⟶ Y)
    (a : X ⟶ Z) (θ : Z ⟶ Y) (aV : F.obj Z ⟶ V₀) (aU : G.obj K ⟶ U')
    (ex : J.obj U' ⟶ W₀) (c : F.obj Y ⟶ D₀) (o : D₀ ⟶ W₀) (t₀ : V₀ ⟶ W₀)
    (hγ : γ ≫ j₀.map b ≫ e = a ≫ θ)
    (hm : r.hom.app K ≫ J.map aU ≫ ex = F.map e ≫ c ≫ o)
    (hn : F.map θ ≫ c ≫ o = aV ≫ t₀) :
    (qV.inv ≫ F.map γ ≫ r.hom.app H ≫ J.map qU.hom) ≫
        J.map (qU.inv ≫ G.map b ≫ aU) ≫ ex =
      qV.inv ≫ F.map a ≫ aV ≫ t₀ := by
  calc
    _ = qV.inv ≫ F.map γ ≫ r.hom.app H ≫ J.map (G.map b) ≫ J.map aU ≫ ex := by
      simp only [Functor.map_comp, Category.assoc]
      rw [← J.map_comp_assoc, Iso.hom_inv_id, J.map_id, Category.id_comp]
    _ = qV.inv ≫ F.map γ ≫ F.map (j₀.map b) ≫
        r.hom.app K ≫ J.map aU ≫ ex := by
      rw [← reassoc_of% (r.hom.naturality b)]
    _ = qV.inv ≫ F.map (γ ≫ j₀.map b ≫ e) ≫ c ≫ o := by
      rw [hm]
      simp only [Functor.map_comp, Category.assoc]
    _ = qV.inv ≫ F.map (a ≫ θ) ≫ c ≫ o := by rw [hγ]
    _ = _ := by
      rw [F.map_comp]
      simp only [Category.assoc]
      rw [hn]

/-- Compatible strict open tensor representatives and completion presentations.
This is the representative construction, prior to the completed comparison theorem.
It does not assert existence, uniqueness or realization of a completed tensor map.

Source: Stacks Project, sites-cohomology.tex Tag 0GL1 and sites-modules.tex Tag 0E8I;
strict quotient and completion-unit refinement, original realization proof steps 1--3.
(blueprint: lem-pur-completed-open-tensor-representatives).

Proof: choose the same canonical total-tensor models for integral scalar reduction and
completion on U and V. Compute the reduction/limit adjunction on flat-term K-flat
and K-injective representatives. Its strict scalar augmentation identifies the actual
completion units, giving completionV/U and unitV/U. Exact slice restriction commutes
with this augmented quotient tower and both Roos coordinates; descent gives
restrictionCompletion and its unit square. Use one summand-normalized slice open
extension for the ordinary, quotient and system operations. Its derived open unit is
invertible and is the localization of the summand insertion/collapse pair. The strict
open reduction map restricts on complete objects to completeOpen.r, so sameOpen holds;
completeOpen.d is its inverse-unit realization. The normalized semilinear model supplies
ordinaryV/U and strictOpen using these same operations, not independent choices.

Descend strictOpen.totalComparison.chain on the two flat-term K-flat arguments to
obtain gamma. Restriction preserves their flat-term K-flat property; tensor of two
K-flat complexes is K-flat, as is the extension of the open argument. The normalized
reduction computations of their two total tensors provide aV and aU. On every local
total-tensor summand the quotient map sends (x tensor y) tensor a to
(x tensor a) tensor (y tensor 1), and the open map sends ([x] tensor y) tensor a to
[(x tensor a restricted to U) tensor (y restricted to U tensor 1)]. These formulas
preserve the signed total differential and every quotient transition. At a=1 they
give the displayed scalar-unit augmentation equation. Localizing this single strict
chain map with the actual representative counits gives the first and last squares
of RepresentativeLaws. Thus these are equations before evaluation and total limit;
no faithfulness of finite derived evaluation is asserted. All choices are retained
as existential theorem data, and the arguments apply to unbounded inputs, including
zero objects, the empty open and the identity open immersion. -/
theorem completedOpenTensorRepresentatives [QuasiCompact j]
    (hlV : IsUnit (l : Γ(V, ⊤))) (hlU : IsUnit (l : Γ(U, ⊤))) :
    ∃ (C : Context l E j) (γ : OrdinaryMap l E j C),
      RepresentativeLaws l E j C γ := by
  obtain ⟨C⟩ := completedOpenTensorContext l E j hlV hlU
  obtain ⟨γ, hγ⟩ := openTensorOrdinaryDescent l E j C
  obtain ⟨eV, heV⟩ := OpenSemilinearTensor.ordinaryReductionAugmentedComputation l E V
    C.ambient C.ambientCoherence C.ordinaryV
  obtain ⟨eU, heU⟩ := OpenSemilinearTensor.ordinaryReductionAugmentedComputation l E U
    C.openSite C.openCoherence C.ordinaryU
  refine ⟨C, γ, ?_⟩
  intro P Q hP hQ hfP hfQ
  have hres := CanonicalOpenRestriction.restriction_preservesGood l E j C.operations Q
    ⟨hQ, hfQ⟩
  have hR := hres.1
  have hfR := hres.2
  have hordinary := hγ P Q hP hQ hfP hfQ hR
  have hV := SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
    (completedIntegralCommRingSheafUnrestricted l E V)
    ((OpenSemilinearTensor.extensionComplex l E j C.operations).obj P) Q
    (C.strictOpen.kflat P hP hfP) hQ (C.strictOpen.preservesFlatTerms P hP hfP) hfQ
  have hU := SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
    (completedIntegralCommRingSheafUnrestricted l E U) P
    ((OpenSemilinearTensor.restrictionComplex l E j C.operations).obj Q) hP hR hfP hfR
  have hH : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E V) (sourceComplex l E j C P Q) := hV.1
  have hHU : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E U) (openComplex l E j C P Q) := hU.1
  let H : (integralOperationsGoodComplex l E V).FullSubcategory :=
    ⟨sourceComplex l E j C P Q, hH, hV.2.1⟩
  let HU : (integralOperationsGoodComplex l E U).FullSubcategory :=
    ⟨openComplex l E j C P Q, hHU, hU.2.1⟩
  let EH : (integralOperationsGoodComplex l E V).FullSubcategory :=
    ⟨(OpenSemilinearTensor.extensionComplex l E j C.operations).obj HU.obj,
      C.strictOpen.kflat HU.obj hHU hU.2.1,
      C.strictOpen.preservesFlatTerms HU.obj hHU hU.2.1⟩
  let aV : OpenSemilinearTensor.Computation l E C.ambient C.ordinaryV H.obj hH :=
    ⟨eV.app H, (heV H).1, (heV H).2⟩
  let aU : OpenSemilinearTensor.Computation l E C.openSite C.ordinaryU HU.obj hHU :=
    ⟨eU.app HU, (heU HU).1, (heU HU).2⟩
  let aE : OpenSemilinearTensor.Computation l E C.ambient C.ordinaryV EH.obj EH.property.1 :=
    ⟨eV.app EH, (heV EH).1, (heV EH).2⟩
  obtain ⟨cU, cE, hmodel⟩ := C.strictOpen.model HU.obj hHU hU.2.1
  rw [computation_hom_unique l E U C.openSite C.ordinaryU HU.obj hHU cU aU,
    computation_hom_unique l E V C.ambient C.ordinaryV EH.obj EH.property.1 cE aE] at hmodel
  have hn := eV.hom.naturality
    (X := H) (Y := EH) ⟨(C.strictOpen.totalComparison.chain P Q).hom⟩
  have hnat : C.ambient.reduction.map
        (DerivedCategory.Q.map (C.strictOpen.totalComparison.chain P Q).hom) ≫ aE.iso.hom ≫
        DerivedCategory.Q.map (OpenSemilinearTensor.ordinaryChain l E j C.operations
          C.ordinaryV C.ordinaryU C.strictOpen.ordinary HU.obj).hom =
      aV.iso.hom ≫ DerivedCategory.Q.map (strictChain l E j C P Q).hom := by
    change C.ambient.reduction.map
      (DerivedCategory.Q.map (C.strictOpen.totalComparison.chain P Q).hom) ≫ aE.iso.hom =
      aV.iso.hom ≫ DerivedCategory.Q.map
        ((C.ordinaryV.functor.mapHomologicalComplex (.up ℤ)).map
          (C.strictOpen.totalComparison.chain P Q).hom) at hn
    rw [← Category.assoc, hn, Category.assoc, ← DerivedCategory.Q.map_comp]
    rfl
  refine ⟨hR, hH, hHU, aV, aU, hordinary, strictChain_augmentation l E j C P Q, ?_⟩
  exact tensorSystemPaste C.ambient.reduction C.openSite.reduction
    (shriek l E j C.operations) (J l E j C.operations) C.strictOpen.r
    ((reductionTensorV l E j C).app
      ((shriek l E j C.operations).obj (DerivedCategory.Q.obj P), DerivedCategory.Q.obj Q))
    ((reductionTensorU l E j C).app
      (DerivedCategory.Q.obj P, (star l E j C.operations).obj (DerivedCategory.Q.obj Q)))
    (γ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
    (openRepresentative l E j C P Q hP hR).hom
    ((extension l E j C.operations).mapDerivedCategoryFactors.hom.app HU.obj)
    (sourceRepresentative l E j C P Q hP hQ hfP).hom
    (DerivedCategory.Q.map (C.strictOpen.totalComparison.chain P Q).hom)
    aV.iso.hom aU.iso.hom
    ((systemExtension l E j C.operations).mapDerivedCategoryFactors.hom.app
      ((C.ordinaryU.functor.mapHomologicalComplex (.up ℤ)).obj HU.obj))
    aE.iso.hom
    (DerivedCategory.Q.map (OpenSemilinearTensor.ordinaryChain l E j C.operations
      C.ordinaryV C.ordinaryU C.strictOpen.ordinary HU.obj).hom)
    (DerivedCategory.Q.map (strictChain l E j C P Q).hom) hordinary hmodel hnat

end WeilConjectures.CompletedOpenTensor
