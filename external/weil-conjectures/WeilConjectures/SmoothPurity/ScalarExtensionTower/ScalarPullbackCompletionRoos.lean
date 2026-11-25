/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarPullbackRoosCoordinates
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarCompletionPresentationNormalization
import WeilConjectures.SmoothPurity.Supporting.FixedCalculusScalarModel
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarPullbackStrictTower
import WeilConjectures.SmoothPurity.ScalarExtensionTower.IntegralScalarRoosCounitNormalization
import WeilConjectures.TraceFormula.Integral.IntegralScalarOrdinaryModelComparison
import all WeilConjectures.TraceFormula.Scalar.ScalarModelRoosZeroLiftCore
import WeilConjectures.SmoothPurity.Scalar.ScalarRoosFunctorNaturality
import all WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Fixed cochain coordinates for the scalar/pullback calculation

Source: Stacks 06YY, 07A4 and 0941. The coordinates are constructed from the
ordinary scalar/pullback chain map and a coherent quotient presentation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] HasDerivedCategory.standard
  integralComparisonSequenceScalarModel coefficientSequenceRestriction coefficientSequenceLimit
  integralDerivedPullback integralOrdinaryScalar integralComparisonSequenceScalarPullback
  completedIntegralCommRingSheafUnrestricted
  integralOperationsRoos integralOperationsRoosMap scalarRoosMap

attribute [local implicit_reducible] integralScalarExtension integralScalarExtensionOfUniverses
  integralComparisonDerivedSequenceScalar completedOrdinaryScalarComplex
  integralScalarComplexFunctor integralOperationsGoodLocalization
  integralOperationsRoosFunctor integralOperationsPullbackComplexFunctor
  NatIso.mapHomologicalComplex
  integralOperationsPullbackOnGood integralComparisonSequencePullback
  integralComparisonDerivedSequencePullback HomologicalComplex.asFunctor
  HomologicalComplex.complexOfFunctorsToFunctorToComplex

private theorem bridge_naturality (F : Type u) [Field F] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] F] (X : Scheme.{u})
    (ρF : IntegralComparisonRoosModel l F X)
    {C D : CochainComplex (coefficientSequenceModules l F X) ℤ} (g : C ⟶ D) :
    (coefficientSequenceLimit l F X).map (DerivedCategory.Q.map g) ≫
        (integralComparisonRoosBridge l F X ρF D).hom =
      (integralComparisonRoosBridge l F X ρF C).hom ≫
        DerivedCategory.Q.map (integralOperationsRoosMap
          (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).map g))) := by
  let U := (coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)
  let b := Functor.isoWhiskerRight
      (coefficientSequenceRestriction l F X).mapDerivedCategoryFactors
      (coefficientConstantTowerLimit l F X) ≪≫
    Functor.isoWhiskerLeft U ρF.comparison
  with_unfolding_all exact b.hom.naturality g

private theorem scalarRoos_composite_naturality
    {𝒜 ℬ : Type*} [Category* 𝒜] [Abelian 𝒜] [HasCountableProducts 𝒜]
    [Category* ℬ] [Abelian ℬ] [HasCountableProducts ℬ]
    (F G : 𝒜 ⥤ ℬ) [F.Additive] [G.Additive] (α : F ⟶ G)
    {C₀ C₁ : ℕᵒᵖ ⥤ CochainComplex 𝒜 ℤ}
    {D₀ D₁ D₂ : ℕᵒᵖ ⥤ CochainComplex ℬ ℤ}
    (a : C₀ ⟶ C₁) (b : C₁ ⋙ G.mapHomologicalComplex (.up ℤ) ⟶ D₀)
    (c : D₀ ⟶ D₁) (d : D₁ ⟶ D₂) :
    (F.mapHomologicalComplex (.up ℤ)).map (integralOperationsRoosMap a) ≫
        (NatTrans.mapHomologicalComplex α (.up ℤ)).app (integralOperationsRoos C₁) ≫
        scalarRoosMap G C₁ ≫ integralOperationsRoosMap b ≫
        integralOperationsRoosMap c ≫ integralOperationsRoosMap d =
      scalarRoosMap F C₀ ≫ integralOperationsRoosMap
        (Functor.whiskerRight a (F.mapHomologicalComplex (.up ℤ)) ≫
          Functor.whiskerLeft C₁ (NatTrans.mapHomologicalComplex α (.up ℤ)) ≫ b ≫ c ≫ d) := by
  rw [reassoc_of% (scalarRoos_functor_naturality F G α C₁),
    reassoc_of% (scalarRoosNaturality F a)]
  simp only [integralOperationsRoosMap_comp]

private theorem map_coordinate_composite
    {𝒜 ℬ 𝒞 : Type*} [Category* 𝒜] [Category* ℬ] [Category* 𝒞]
    (A : 𝒜 ⥤ ℬ) (T : ℬ ⥤ 𝒞)
    {X₀ X₁ X₂ X₃ X₄ : 𝒜} {Y Z : ℬ} {V W U : 𝒞}
    (r : X₀ ⟶ X₁) (s : X₁ ⟶ X₂) (v : X₂ ⟶ X₃) (w : X₃ ⟶ X₄)
    (p : X₀ ⟶ X₄) (ε : A.obj X₄ ⟶ Y) (σ : Y ⟶ Z)
    (b : T.obj Y ⟶ V) (b' : T.obj Z ⟶ W) (τ : V ⟶ W) (q : W ⟶ U)
    (hp : p = r ≫ s ≫ (v ≫ w)) (hσ : T.map σ ≫ b' = b ≫ τ) :
    T.map (A.map (r ≫ s)) ≫
        (T.map (A.map v ≫ A.map w ≫ ε ≫ σ) ≫ b' ≫ q) =
      T.map (A.map p) ≫ T.map ε ≫ b ≫ τ ≫ q := by
  rw [hp]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hσ]

private theorem completion_roos_composite
    {𝒜 ℬ 𝒞 𝒟 : Type*} [Category* 𝒜] [Category* ℬ] [Category* 𝒞] [Category* 𝒟]
    (O : 𝒜 ⥤ 𝒟) (R : 𝒜 ⥤ ℬ) (I : ℬ ⥤ 𝒟) (Q : 𝒞 ⥤ 𝒟)
    (α : O ⟶ R ⋙ I)
    {X X₀ X₁ X₂ X₃ X₄ : 𝒜} {V : ℬ} {P₀ P₁ P₂ P₃ P₄ : 𝒞}
    (r : X ⟶ X₀) (s : X₀ ⟶ X₁) (t : X₁ ⟶ X₂)
    (v : X₂ ⟶ X₃) (w : X₃ ⟶ X₄) (γ : X ⟶ X₄)
    (ε : R.obj X₄ ⟶ V) (b : I.obj V ⟶ Q.obj P₂)
    (f₂ : O.obj X₂ ⟶ Q.obj P₀) (f₃ : O.obj X₃ ⟶ Q.obj P₁)
    (a : P₀ ⟶ P₁) (c : P₁ ⟶ P₂) (τ : P₂ ⟶ P₃) (q : P₃ ⟶ P₄)
    (k : P₀ ⟶ P₄)
    (hγ : γ = r ≫ s ≫ t ≫ v ≫ w)
    (hc : O.map w ≫ α.app X₄ ≫ I.map ε ≫ b = f₃ ≫ Q.map c)
    (hf : O.map v ≫ f₃ = f₂ ≫ Q.map a)
    (hk : a ≫ c ≫ τ ≫ q = k) :
    α.app X ≫ I.map (R.map γ ≫ ε) ≫ b ≫ Q.map τ ≫ Q.map q =
      O.map r ≫ O.map s ≫ O.map t ≫ f₂ ≫ Q.map k := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (α.naturality γ), hγ]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hc, reassoc_of% hf]
  simp only [← Q.map_comp, hk]

-- Keep the nested derived comparison functors folded during the calculation.
/-- The scalar completion augmentation respects the pulled coherent quotient tower.
Source: Stacks 06YY, 07A4 and 0941; the quotient calculation in step 1 of
stage3-pur-scalar-pullback-right-roos-normalized.
(blueprint: lem-pur-scalar-pullback-completion-roos).

Proof: transpose the reduction of eR followed by pullbackReduction through the
reduction/limit adjunction. Its counit cancels the reduction of the E-pullback
realization. Pullback normalization identifies the remaining transpose with the
strict pullback tensor-unit tower map attached to (C,eC,kappa). Coherence of
(D,eD,kappaD) identifies its source with the strict quotient tower of R.
At each level, associate the scalar tensors and apply the inverse-image unit.
The scalar/pullback association sends 1 tensor gamma(x) to gamma(1 tensor x).
The formulas hqD and hq identify the two resulting strict tower maps: balancing
and the inverse-image adjunction reduce equality to these nested unit sections.
Every map used is a map of quotient systems, so these equalities preserve all
horizontal transitions before localization. Apply the Roos construction to this
strict equality. The unshifted coordinates are the finite quotient projections
of the scalar completion augmentation; both shifted coordinates are zero.
The scalar/Roos product map followed by scalarPullbackTower is scalarPullbackChain.
Naturality of the K-injective-normalized Roos bridges transports this calculation
to derived limits. The comparison eR and then eP give the ordinary derived maps
on the right. The scalar cochain counit is inverted only through the supplied
isomorphism epsilonD. No scalar realization model, scalar completion inverse,
derived completeness, constructibility of the pulled object, or faithfulness of
finite derived evaluations is used. Zero complexes, identity maps, exponent one,
empty sites and ramified coefficient embeddings use the same balanced tensors. -/
theorem scalarPullbackCompletionRoos (W : Bool → Scheme.{u})
    (ME : CompletedOperations.Models.{u, u} l E W)
    (ρ : IntegralComparisonRoosModel.{u, u} l L (W true))
    (f : W true ⟶ W false)
    (P : (integralOperationsGoodComplex.{u, u} l E (W false)).FullSubcategory)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E (W false)))
    (eP : DerivedCategory.Q.obj P.obj ≅ K)
    (C : CochainComplex (coefficientSequenceModules.{u, u} l E (W false)) ℤ)
    (eC : (ME.calculus false).reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E (W false) n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E (W false) n).obj P.obj)
    (hp : CoefficientReductionPresentation.{u, u} l E (W false)
      (ME.calculus false).toCoefficientDerivedSystemReduction P.obj P.property.1 C eC κ)
    (hc : IsIntegralComparisonPresentationCoherent.{u, u} l E (W false)
      (ME.calculus false) P.obj C eC κ)
    (q :
    (((coefficientSequenceRestriction.{u, u} l L (W true)).mapHomologicalComplex (.up ℤ)).obj
      ((((integralComparisonSequencePullback.{u, u} l L f).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel.{u, u} l E L ι (W false)).E.mapHomologicalComplex
          (.up ℤ)).obj C)))).asFunctor ≅
      (integralOperationsPullbackTowerFunctor.{u, u} l L f).obj
        (((integralOrdinaryScalar l E L ι (W false)).mapHomologicalComplex (.up ℤ)).obj P.obj))
    (hq : ScalarPullbackQuotientFormula l E L ι f P C κ q)
    (R : (integralOperationsGoodComplex.{u, u} l E (W true)).FullSubcategory)
    (eR : DerivedCategory.Q.obj R.obj ≅
      (integralDerivedPullback.{u, u} l E f).obj K)
    (D : CochainComplex (coefficientSequenceModules.{u, u} l E (W true)) ℤ)
    (eD : (ME.calculus true).reduction.obj (DerivedCategory.Q.obj R.obj) ≅
      DerivedCategory.Q.obj D)
    (κD : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E (W true) n).mapHomologicalComplex (.up ℤ)).obj D ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E (W true) n).obj R.obj)
    (hpD : CoefficientReductionPresentation.{u, u} l E (W true)
      (ME.calculus true).toCoefficientDerivedSystemReduction R.obj R.property.1 D eD κD)
    (hcD : IsIntegralComparisonPresentationCoherent.{u, u} l E (W true)
      (ME.calculus true) R.obj D eD κD)
    (εD : (integralComparisonDerivedSequenceScalar.{u, u} l E L ι (W true)).obj
        (DerivedCategory.Q.obj D) ≅
      DerivedCategory.Q.obj
        (((integralComparisonSequenceScalarModel.{u, u} l E L ι (W true)).E.mapHomologicalComplex
          (.up ℤ)).obj D))
    (hεD : εD.hom = (integralComparisonSequenceScalarModel.{u, u} l E L ι (W true)).ε.app D)
    (qD : (((coefficientSequenceRestriction.{u, u} l L (W true)).mapHomologicalComplex
        (.up ℤ)).obj
      (((integralComparisonSequenceScalarModel.{u, u} l E L ι (W true)).E.mapHomologicalComplex
        (.up ℤ)).obj D)).asFunctor ≅
      (integralScalarTowerFunctor.{u, u} l E L ι (W true)).obj R.obj)
    (hqD : ∀ (n : ℕ) (i : ℤ) (U : (W true).ProEtᵒᵖ)
        (s : (coefficientSequenceCommRingSheaf l L (W true)).obj.obj (op (n, U.unop)))
        (x : (R.obj.X i).val.obj U),
        ((qD.hom.app (op n)).f i).val.app U
          (integralComparisonRestrictedSection l L (W true)
            ((integralComparisonSequenceScalarModel l E L ι (W true)).E.obj (D.X i)) n U
            (integralComparisonSequenceTensorSection l E L ι (W true) (D.X i)
              (op (n, U.unop)) s
              (integralComparisonSequenceSection l E (W true) (D.X i) n U
                (((κD n).inv.f i).val.app U
                  (unrestrictedIntegralTensorSection l E (W true) n (R.obj.X i) U 1 x))))) =
          integralScalarTensorSection l E L ι (W true) n (R.obj.X i) U s x) :
    let T := coefficientSequenceLimit.{u, u} l L (W true)
    let A := integralComparisonDerivedSequenceScalar.{u, u} l E L ι (W true)
    let SD :=
      ((integralComparisonSequenceScalarModel.{u, u} l E L ι (W true)).E.mapHomologicalComplex
        (.up ℤ)).obj D
    let rD := T.mapIso (A.mapIso eD ≪≫ εD) ≪≫
      integralComparisonRoosBridge.{u, u} l L (W true) ρ SD ≪≫
      DerivedCategory.Q.mapIso (integralOperationsRoosFunctor.mapIso qD)
    (integralOrdinaryScalar l E L ι (W true)).mapDerivedCategoryFactors.hom.app R.obj ≫
      DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι (W true)).app R.obj) ≫
      rD.inv ≫
      T.map (A.map ((ME.calculus true).reduction.map eR.hom ≫
        pullbackReduction l E W ME f K)) ≫
      scalarPullbackRoosCoordinate l E L ι f P C (ME.calculus false) ρ K eP eC q =
    (integralOrdinaryDerivedScalar l E L ι (W true)).map eR.hom ≫
      (integralOrdinaryDerivedScalar l E L ι (W true)).map
        ((integralDerivedPullback.{u, u} l E f).map eP.inv) ≫
      (integralOrdinaryDerivedScalar l E L ι (W true)).map
        ((integralDerivedPullbackComparison.{u, u} l E f).hom.app P) ≫
      (integralOrdinaryScalar l E L ι (W true)).mapDerivedCategoryFactors.hom.app
        ((integralOperationsPullbackComplexFunctor.{u, u} l E f).obj P.obj) ≫
      DerivedCategory.Q.map (scalarPullbackChain l E L ι f P.obj) := by
  classical
  dsimp only
  let X := W true
  let F := integralDerivedPullback l E f
  let O := integralOrdinaryDerivedScalar l E L ι X
  let A := integralComparisonDerivedSequenceScalar l E L ι X
  let T := coefficientSequenceLimit l L X
  let S := ME.calculus true
  let χ := scalarCompletion l E L ι X
  let SD := ((integralComparisonSequenceScalarModel l E L ι X).E.mapHomologicalComplex
    (.up ℤ)).obj D
  let rD := T.mapIso (A.mapIso eD ≪≫ εD) ≪≫
    integralComparisonRoosBridge l L X ρ SD ≪≫
    DerivedCategory.Q.mapIso (integralOperationsRoosFunctor.mapIso qD)
  obtain ⟨SX⟩ := fixedCalculusScalarModel l E L ι X S ρ
  have hs := scalarCompletionPresentationNormalization l E L ι X S ρ SX
    R D eD κD hpD hcD εD hεD qD hqD
  let B := integralComparisonDerivedSequencePullback l E f
  let H := ((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj C
  let cp := (integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.hom.app C
  let TE := coefficientSequenceLimit l E X
  let z := B.map ((ME.calculus false).reduction.map eP.inv ≫ eC.hom) ≫ cp
  let γ := eR.hom ≫ (ME.pullback f).realization.hom.app K ≫ TE.map z
  have hAdj : S.reduction.map γ ≫ S.adjunction.counit.app (DerivedCategory.Q.obj H) =
      S.reduction.map eR.hom ≫ pullbackReduction l E W ME f K ≫ z := by
    have hz := S.adjunction.counit.naturality z
    change S.reduction.map (TE.map z) ≫
      S.adjunction.counit.app (DerivedCategory.Q.obj H) =
      S.adjunction.counit.app _ ≫ z at hz
    dsimp only [γ, pullbackReduction]
    simp only [Functor.map_comp, Category.assoc]
    rw [hz]
  obtain ⟨qE, hqE, hME⟩ := (ME.pullback f).normalization P C eC κ hp hc
  let CE := ((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj H
  let SH := ((integralComparisonSequenceScalarModel l E L ι X).E.mapHomologicalComplex
    (.up ℤ)).obj H
  let CL := ((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj SH
  let a : CE.asFunctor ⋙ completedOrdinaryScalarComplex l E L ι X ⟶ CL.asFunctor :=
    { app n := ScalarRoosLiftProof.levelChange l E L ι X H n.unop
      naturality n m h := ScalarRoosLiftProof.levelChange_horizontal l E L ι X H h }
  obtain ⟨t, e, ht, he, hχmodel⟩ := integralScalarOrdinaryModelComparison l E L ι X
  have hCounit := integralScalarRoosCounitNormalization l E L ι X S (ME.roos true) ρ SX t e he
    hχmodel H a (fun n i U s x ↦
      ScalarRoosLiftProof.scalarComponent_tensor l E L ι X (H.X i) n U s x)
  let σ := (NatIso.mapHomologicalComplex
    (integralComparisonSequenceScalarPullback l E L ι f) (.up ℤ)).hom.app C
  let σ' : SH ⟶
      ((integralComparisonSequencePullback l L f).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel l E L ι (W false)).E.mapHomologicalComplex
          (.up ℤ)).obj C) := σ
  let τ := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
    (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).map σ')
  have hσ := bridge_naturality l L X ρ σ
  have hγ : γ = eR.hom ≫ F.map eP.inv ≫
      (integralDerivedPullbackComparison l E f).hom.app P ≫
      DerivedCategory.Q.map (integralOperationsRoosMap qE.inv) ≫
      (integralComparisonRoosBridge l E X (ME.roos true) H).inv := by
    let b := integralComparisonRoosBridge l E X (ME.roos true) H
    let qe := DerivedCategory.Q.mapIso (integralOperationsRoosFunctor.mapIso qE)
    have hnat := (ME.pullback f).realization.hom.naturality eP.inv
    dsimp only [Functor.comp_map] at hnat
    have hγcomp : γ ≫ b.hom ≫ qe.hom =
        eR.hom ≫ F.map eP.inv ≫ (integralDerivedPullbackComparison l E f).hom.app P := by
      dsimp only [γ, z, b, qe, Iso.trans_hom, Functor.mapIso_hom]
      simp only [Functor.map_comp, Category.assoc]
      rw [← Category.assoc ((ME.pullback f).realization.hom.app K), ← hnat]
      simp only [Category.assoc]
      rw [hME]
    change γ = eR.hom ≫ F.map eP.inv ≫
      (integralDerivedPullbackComparison l E f).hom.app P ≫ qe.inv ≫ b.inv
    apply (cancel_mono (b.hom ≫ qe.hom)).1
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id] using hγcomp
  -- The strict tower square identifies the resulting scalar/Roos chain.
  have hchain :
      ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).map
          (integralOperationsRoosMap qE.inv) ≫
        (NatIso.mapHomologicalComplex t (.up ℤ)).hom.app (integralOperationsRoos CE.asFunctor) ≫
        scalarRoosMap (completedOrdinaryScalarExtension l E L ι X) CE.asFunctor ≫
        integralOperationsRoosMap a ≫ integralOperationsRoosMap τ ≫
        integralOperationsRoosMap q.hom = scalarPullbackChain l E L ι f P.obj := by
    let G := integralOrdinaryScalar l E L ι X
    let b := Functor.whiskerLeft CE.asFunctor
      (NatIso.mapHomologicalComplex t (.up ℤ)).hom
    let c := Functor.whiskerRight qE.inv (G.mapHomologicalComplex (.up ℤ))
    have hb : c ≫ b ≫ a ≫ τ ≫ q.hom = (scalarPullbackTower l E L ι f).app P.obj :=
      scalarPullbackStrictTower l E L ι f P C κ qE hqE q hq t ht a
        (fun n i U s x ↦
          ScalarRoosLiftProof.scalarComponent_tensor l E L ι X (H.X i) n U s x)
    calc
      _ = scalarRoosMap G ((integralOperationsPullbackTowerFunctor l E f).obj P.obj) ≫
          integralOperationsRoosMap (c ≫ b ≫ a ≫ τ ≫ q.hom) :=
        scalarRoos_composite_naturality G (completedOrdinaryScalarExtension l E L ι X)
          t.hom qE.inv a τ q.hom
      _ = _ := by rw [hb]; rfl
  change _ ≫ _ ≫ rD.inv ≫ _ ≫ _ = _
  rw [reassoc_of% hs]
  let ε := S.adjunction.counit.app (DerivedCategory.Q.obj H)
  let c := scalarPullbackRoosCoordinate l E L ι f P C (ME.calculus false) ρ K eP eC q
  have hCoord :
      T.map (A.map (S.reduction.map eR.hom ≫ pullbackReduction l E W ME f K)) ≫ c =
      T.map (A.map (S.reduction.map γ ≫ ε)) ≫
        T.map ((integralComparisonSequenceScalarModel l E L ι X).ε.app H) ≫
        (integralComparisonRoosBridge l L X ρ SH).hom ≫
        DerivedCategory.Q.map (integralOperationsRoosMap τ) ≫
        DerivedCategory.Q.map (integralOperationsRoosMap q.hom) := by
    exact map_coordinate_composite A T
      (S.reduction.map eR.hom) (pullbackReduction l E W ME f K)
      (B.map ((ME.calculus false).reduction.map eP.inv ≫ eC.hom)) cp
      (S.reduction.map γ ≫ ε)
      ((integralComparisonSequenceScalarModel l E L ι X).ε.app H)
      (DerivedCategory.Q.map σ)
      (integralComparisonRoosBridge l L X ρ SH).hom _
      (DerivedCategory.Q.map (integralOperationsRoosMap τ))
      (DerivedCategory.Q.map (integralOperationsRoosMap q.hom)) hAdj hσ
  change χ.app _ ≫ SX.realization.hom.app _ ≫ _ ≫ c = _
  rw [hCoord]
  have hfac := (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.naturality
    (integralOperationsRoosMap qE.inv)
  dsimp only [Functor.comp_map] at hfac
  have hcounit : O.map (integralComparisonRoosBridge l E X (ME.roos true) H).inv ≫
      (χ ≫ SX.realization.hom).app (TE.obj (DerivedCategory.Q.obj H)) ≫
      (A ⋙ T).map ε ≫
      (T.map ((integralComparisonSequenceScalarModel l E L ι X).ε.app H) ≫
        (integralComparisonRoosBridge l L X ρ SH).hom) =
      (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app
        (integralOperationsRoos CE.asFunctor) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex t (.up ℤ)).hom.app
            (integralOperationsRoos CE.asFunctor) ≫
          scalarRoosMap (completedOrdinaryScalarExtension l E L ι X) CE.asFunctor ≫
          integralOperationsRoosMap a) := by
    simpa only [NatTrans.comp_app, Functor.comp_map, Category.assoc] using hCounit
  have h := completion_roos_composite O S.reduction (A ⋙ T) DerivedCategory.Q
    (χ ≫ SX.realization.hom)
    eR.hom (F.map eP.inv) ((integralDerivedPullbackComparison l E f).hom.app P)
    (DerivedCategory.Q.map (integralOperationsRoosMap qE.inv))
    (integralComparisonRoosBridge l E X (ME.roos true) H).inv γ ε
    (T.map ((integralComparisonSequenceScalarModel l E L ι X).ε.app H) ≫
      (integralComparisonRoosBridge l L X ρ SH).hom) _ _
    (((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).map
      (integralOperationsRoosMap qE.inv))
    ((NatIso.mapHomologicalComplex t (.up ℤ)).hom.app
        (integralOperationsRoos CE.asFunctor) ≫
      scalarRoosMap (completedOrdinaryScalarExtension l E L ι X) CE.asFunctor ≫
      integralOperationsRoosMap a)
    (integralOperationsRoosMap τ) (integralOperationsRoosMap q.hom)
    (scalarPullbackChain l E L ι f P.obj) hγ hcounit hfac
    (by simpa only [Category.assoc] using hchain)
  simp only [NatTrans.comp_app, Functor.comp_map, Category.assoc] at h
  exact h

end WeilConjectures.ScalarExtensionTower
