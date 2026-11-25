/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Compact.CompactSupportSystemEvaluationDiagram
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Finite components of strict open reduction on K-flat representatives

Source: Stacks Tags 0E8I, 0GL1, 06YY and 0941; the strict-model normalization in
`lem-sf-integral-open-reduction-comparison`
(blueprint: lem-sf-integral-open-tensor-representative).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian

universe t u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

attribute [local instance 10000] Functor.preservesZeroMorphisms_of_additive

private theorem exactSquare_fac
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    {R : C ⥤ D} {G : D ⥤ F} {L : C ⥤ E} {S : E ⥤ F}
    [hR : R.Additive] [hG : G.Additive] [hL : L.Additive] [hS : S.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (e : R ⋙ G ≅ L ⋙ S) (K : CochainComplex C ℤ) :
    (mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj K) ≫
      S.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
      S.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K) =
    G.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map
        (HomologicalComplex.Hom.isoOfComponents (fun i ↦ e.app (K.X i))
          (fun i k _h ↦ (e.hom.naturality (K.d i k)).symm)).hom := by
  have hc := mapDerivedCategoryCompIso_hom_app_factors R G K
  have hi : (mapDerivedCategoryCompIso R G).hom.app (DerivedCategory.Q.obj K) ≫
      (R ⋙ G).mapDerivedCategoryFactors.hom.app K =
    G.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj K) := by
    apply (cancel_epi ((mapDerivedCategoryCompIso R G).inv.app (DerivedCategory.Q.obj K))).mp
    rw [Iso.inv_hom_id_app_assoc]
    exact hc.symm
  simp only [mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [mapDerivedCategoryCompIso_hom_app_factors]
  erw [mapDerivedCategoryNatIso_fac]
  erw [← Category.assoc, hi, Category.assoc]
  rfl

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X V : Scheme.{t}} (j : X ⟶ V) [IsOpenImmersion j]
  (o : IntegralOpenReduction.Operations l E j)

attribute [local irreducible] scalarReductionExtension HasDerivedCategory.standard
  CategoryTheory.Functor.mapDerivedCategory

/-- The consecutive scalar quotient map, with the specified derived adjunction.
Source: Stacks 06YY and 0941
(blueprint: lem-sf-integral-open-tensor-representative). -/
def integralOpenReductionStep (W : Scheme.{t}) (n : ℕ) :
    coefficientFiniteDerivedExtension l E W (n + 1) ⟶
      coefficientFiniteDerivedExtension l E W n ⋙ normalizedDVRRes l E W (Nat.le_succ n) :=
  coefficientQuotientNatTrans (coefficientFiniteAdjunction l E W (n + 1))
    (coefficientFiniteAdjunction l E W n) (normalizedDVRRes l E W (Nat.le_succ n))
    (compactSupportSystemRestrictionComp l E W (Nat.le_succ n))

/-- Evaluation of the specified strict comparison, through the finite evaluations.
Source: Stacks 0941, the strict comparison of open reduction
(blueprint: lem-sf-integral-open-tensor-representative). -/
def integralOpenReductionAlpha
    (SV : CoefficientDerivedSystemCalculus l E V)
    (SX : CoefficientDerivedSystemCalculus l E X)
    (tensor : IntegralOpenReduction.TensorComparison l E j o)
    (r : IntegralOpenReduction.Comparison l E j o SV SX tensor)
    (K : (IntegralOpenReduction.complete l E X).FullSubcategory) (n : ℕ) :
    (coefficientFiniteDerivedExtension l E V n).obj
        ((IntegralOpenReduction.shriek l E j o).obj K.obj) ≅
      (compactSupportCanonicalJLevel l E j o n).obj
        ((coefficientFiniteDerivedExtension l E X n).obj K.obj) :=
  ((SV.reductionEvaluation n).app ((IntegralOpenReduction.shriek l E j o).obj K.obj)).symm ≪≫
    (coefficientSequenceDerivedEvaluation l E V n).mapIso (r.r.app K) ≪≫
    (compactSupportCanonicalJEvaluation l E j o n).app (SX.reduction.obj K.obj) ≪≫
    (compactSupportCanonicalJLevel l E j o n).mapIso ((SX.reductionEvaluation n).app K.obj)

/-- The tensor comparison applied degreewise, with the two composites kept nested.
Source: Stacks 0GL1, degreewise open tensor comparison
(blueprint: lem-sf-integral-open-tensor-representative). -/
def integralOpenTensorChainIso
    (tensor : IntegralOpenReduction.TensorComparison l E j o)
    (Q : CochainComplex (scalarReductionSource l E X) ℤ) (n : ℕ) :
    ((scalarReductionExtension l E V n).mapHomologicalComplex (.up ℤ)).obj
        (((IntegralOpenReduction.extension l E j o).mapHomologicalComplex (.up ℤ)).obj Q) ≅
      ((IntegralOpenReduction.finiteExtension l E j o n).mapHomologicalComplex (.up ℤ)).obj
        (((scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ)).obj Q) :=
  HomologicalComplex.Hom.isoOfComponents (fun i ↦ (tensor.ordinary n).app (Q.X i))
    (fun i k _h ↦ ((tensor.ordinary n).hom.naturality (Q.d i k)).symm)

attribute [local irreducible] coefficientFiniteReductionModel
  integralOpenReductionAlpha integralOpenTensorChainIso

/-- The localization of the actual ordinary open tensor isomorphism on a K-flat model.
This is a construction from chain isomorphisms, with no chosen existence witness.
Source: Stacks 0GL1, proof of lemma-j-shriek-and-tensor
(blueprint: lem-sf-integral-open-tensor-representative). -/
def integralOpenTensorRepresentativeIso
    (tensor : IntegralOpenReduction.TensorComparison l E j o)
    (Q : CochainComplex (scalarReductionSource l E X) ℤ)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l E X) Q)
    (hJQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology V) (R := completedIntegralCommRingSheafUnrestricted l E V)
      (((IntegralOpenReduction.extension l E j o).mapHomologicalComplex (.up ℤ)).obj Q))
    (n : ℕ) :
    (coefficientFiniteDerivedExtension l E V n).obj
        ((IntegralOpenReduction.shriek l E j o).obj (DerivedCategory.Q.obj Q)) ≅
      (compactSupportCanonicalJLevel l E j o n).obj
        ((coefficientFiniteDerivedExtension l E X n).obj (DerivedCategory.Q.obj Q)) :=
  let := coefficientFiniteExtensionAdditive l E X n
  let := coefficientFiniteExtensionAdditive l E V n
  let := IntegralOpenReduction.extensionAdditive l E j o
  let := IntegralOpenReduction.finiteExtensionAdditive l E j o n
  (coefficientFiniteDerivedExtension l E V n).mapIso
      ((IntegralOpenReduction.extension l E j o).mapDerivedCategoryFactors.app Q) ≪≫
    coefficientFiniteReductionModel l E V _ hJQ n ≪≫
    DerivedCategory.Q.mapIso (integralOpenTensorChainIso l E j o tensor Q n) ≪≫
    ((IntegralOpenReduction.finiteExtension l E j o n).mapDerivedCategoryFactors.app
      (((scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ)).obj Q)).symm ≪≫
    (compactSupportCanonicalJLevel l E j o n).mapIso
      (coefficientFiniteReductionModel l E X Q hQ n).symm

attribute [local irreducible] integralOpenTensorRepresentativeIso

/-- A strict comparison evaluates to the localization of its prescribed tensor components.
Source: Stacks 0GL1 and 0941; Step 3 of the parent quotient-square argument.
(blueprint: lem-sf-integral-open-tensor-representative).

Proof: Apply r.strictModel to Q, its flat terms, and its completeness. Retain its
K-flatness proof for the open extension. Apply finite derived evaluation to the
whole-system representative equation. The two CoefficientReductionPresentation
identities replace the evaluated representative maps by reductionEvaluation followed
by coefficientFiniteReductionModel. The finite chain component equation identifies
the evaluated chain isomorphism, after extensionEvaluation, with the degreewise
ordinary tensor comparison. Exact localization commutes with composition of these
chain maps. Naturality of the exact-localization comparison moves the finite
representative maps through extension. Cancel the representative isomorphisms and
the two finite-reduction model isomorphisms. The resulting equality is precisely
alpha = the displayed localization of tensor.ordinary. This is a comparison of
individual finite components, with no assertion about quotient arrows. It applies
to the empty open, the zero complex, n=0, and unbounded complexes. -/
theorem integralOpenTensorRepresentative
    (SV : CoefficientDerivedSystemCalculus l E V)
    (SX : CoefficientDerivedSystemCalculus l E X)
    (tensor : IntegralOpenReduction.TensorComparison l E j o)
    (r : IntegralOpenReduction.Comparison l E j o SV SX tensor)
    (Q : CochainComplex (scalarReductionSource l E X) ℤ)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l E X) Q)
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l E X) (Q.X i))
    (hc : IntegralOpenReduction.complete l E X (DerivedCategory.Q.obj Q)) :
    ∃ hJQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology V) (R := completedIntegralCommRingSheafUnrestricted l E V)
      (((IntegralOpenReduction.extension l E j o).mapHomologicalComplex (.up ℤ)).obj Q),
      ∀ n : ℕ,
        integralOpenReductionAlpha l E j o SV SX tensor r ⟨DerivedCategory.Q.obj Q, hc⟩ n =
          integralOpenTensorRepresentativeIso l E j o tensor Q hQ hJQ n := by
  obtain ⟨hJQ, C, D, eC, eD, κC, κD, f, hC, _haC, hD, _haD, hs, hf⟩ :=
    r.strictModel Q hQ hflat hc
  refine ⟨hJQ, fun n ↦ ?_⟩
  have hAX := coefficientFiniteExtensionAdditive l E X n
  have hAV := coefficientFiniteExtensionAdditive l E V n
  have hAJ := IntegralOpenReduction.extensionAdditive l E j o
  let J : coefficientSequenceModules l E X ⥤ coefficientSequenceModules l E V :=
    IntegralOpenReduction.systemExtension l E j o
  let F : normalizedDVRModules l E X n ⥤ normalizedDVRModules l E V n :=
    IntegralOpenReduction.finiteExtension l E j o n
  let EX := coefficientSequenceEvaluation l E X n
  let EV := coefficientSequenceEvaluation l E V n
  have hAddEV : EV.Additive := coefficientSequenceEvaluation_additiveInstance l E V n
  have hAddEX : EX.Additive := coefficientSequenceEvaluation_additiveInstance l E X n
  have hAddJ : J.Additive := IntegralOpenReduction.systemExtensionAdditive l E j o
  have hAddF : F.Additive := IntegralOpenReduction.finiteExtensionAdditive l E j o n
  have hLimEX : PreservesFiniteLimits EX := coefficientSequenceEvaluation_limits l E X n
  have hColEX : PreservesFiniteColimits EX := coefficientSequenceEvaluation_colimits l E X n
  have hLimEV : PreservesFiniteLimits EV := coefficientSequenceEvaluation_limits l E V n
  have hColEV : PreservesFiniteColimits EV := coefficientSequenceEvaluation_colimits l E V n
  have hLimJ : PreservesFiniteLimits J := IntegralOpenReduction.systemExtensionLimits l E j o
  have hColJ : PreservesFiniteColimits J := IntegralOpenReduction.systemExtensionColimits l E j o
  have hLimF : PreservesFiniteLimits F :=
    compactSupportFiniteExtensionPreservesFiniteLimits l E j o n
  have hColF : PreservesFiniteColimits F :=
    compactSupportFiniteExtensionPreservesFiniteColimits l E j o n
  have hZeroEV : EV.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive EV
  have hZeroEX : EX.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive EX
  have hZeroJ : J.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive J
  have hZeroF : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive F
  let JO : scalarReductionSource l E X ⥤ scalarReductionSource l E V :=
    IntegralOpenReduction.extension l E j o
  have hAddJO : JO.Additive := IntegralOpenReduction.extensionAdditive l E j o
  let f' : D ≅ (J.mapHomologicalComplex (.up ℤ)).obj C := f
  let b := JO.mapDerivedCategoryFactors.hom.app Q
  let a : SV.reduction.obj (JO.mapDerivedCategory.obj (DerivedCategory.Q.obj Q)) ⟶
      J.mapDerivedCategory.obj (SX.reduction.obj (DerivedCategory.Q.obj Q)) :=
    r.r.hom.app ⟨DerivedCategory.Q.obj Q, hc⟩
  let θ : J ⋙ EV ≅ EX ⋙ F := IntegralOpenReduction.extensionEvaluation l E j o n
  let γ : J.mapDerivedCategory ⋙ EV.mapDerivedCategory ≅
      EX.mapDerivedCategory ⋙ F.mapDerivedCategory :=
    compactSupportCanonicalJEvaluation l E j o n
  let ξ :
      (EV.mapHomologicalComplex (.up ℤ)).obj ((J.mapHomologicalComplex (.up ℤ)).obj C) ≅
        (F.mapHomologicalComplex (.up ℤ)).obj ((EX.mapHomologicalComplex (.up ℤ)).obj C) :=
    HomologicalComplex.Hom.isoOfComponents (fun i ↦ θ.app (C.X i))
      (fun i k _h ↦ (θ.hom.naturality (C.d i k)).symm)
  have hγ :
      γ.hom.app (DerivedCategory.Q.obj C) ≫
        F.mapDerivedCategory.map (EX.mapDerivedCategoryFactors.hom.app C) ≫
        F.mapDerivedCategoryFactors.hom.app ((EX.mapHomologicalComplex (.up ℤ)).obj C) =
      EV.mapDerivedCategory.map (J.mapDerivedCategoryFactors.hom.app C) ≫
        EV.mapDerivedCategoryFactors.hom.app ((J.mapHomologicalComplex (.up ℤ)).obj C) ≫
        DerivedCategory.Q.map ξ.hom := by
    exact exactSquare_fac (R := J) (G := EV) (L := EX) (S := F)
      (hR := hAddJ) (hG := hAddEV) (hL := hAddEX) (hS := hAddF) θ C
  let TX : scalarReductionSource l E X ⥤ normalizedDVRModules l E X n :=
    scalarReductionExtension l E X n
  let TV : scalarReductionSource l E V ⥤ normalizedDVRModules l E V n :=
    scalarReductionExtension l E V n
  let kC : (EX.mapHomologicalComplex (.up ℤ)).obj C ≅
      (TX.mapHomologicalComplex (.up ℤ)).obj Q := κC n
  let kD : (EV.mapHomologicalComplex (.up ℤ)).obj D ≅
      (TV.mapHomologicalComplex (.up ℤ)).obj ((JO.mapHomologicalComplex (.up ℤ)).obj Q) :=
    κD n
  let χ : (TV.mapHomologicalComplex (.up ℤ)).obj
        ((JO.mapHomologicalComplex (.up ℤ)).obj Q) ≅
      (F.mapHomologicalComplex (.up ℤ)).obj ((TX.mapHomologicalComplex (.up ℤ)).obj Q) :=
    integralOpenTensorChainIso l E j o tensor Q n
  have hξ (i : ℤ) : ξ.hom.f i = θ.hom.app (C.X i) := rfl
  have hχ (i : ℤ) : χ.hom.f i = (tensor.ordinary n).hom.app (Q.X i) := by
    dsimp only [χ]
    unfold integralOpenTensorChainIso
    rfl
  have hchain :
      (EV.mapHomologicalComplex (.up ℤ)).map f'.hom ≫ ξ.hom ≫
        (F.mapHomologicalComplex (.up ℤ)).map kC.hom = kD.hom ≫ χ.hom := by
    apply HomologicalComplex.Hom.ext
    funext i
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, hξ, hχ]
    exact hf n i
  have hCn :
      EX.mapDerivedCategory.map eC.hom ≫ EX.mapDerivedCategoryFactors.hom.app C ≫
        DerivedCategory.Q.map kC.hom =
      (SX.reductionEvaluation n).hom.app (DerivedCategory.Q.obj Q) ≫
        (coefficientFiniteReductionModel l E X Q hQ n).hom := hC.1 n
  have hDn :
      EV.mapDerivedCategory.map eD.hom ≫ EV.mapDerivedCategoryFactors.hom.app D ≫
        DerivedCategory.Q.map kD.hom =
      (SV.reductionEvaluation n).hom.app
          (DerivedCategory.Q.obj ((JO.mapHomologicalComplex (.up ℤ)).obj Q)) ≫
        (coefficientFiniteReductionModel l E V
          ((JO.mapHomologicalComplex (.up ℤ)).obj Q) hJQ n).hom := hD.1 n
  have hchainQ := congrArg DerivedCategory.Q.map hchain
  simp only [Functor.map_comp] at hchainQ
  have hFC := congrArg F.mapDerivedCategory.map hCn
  simp only [Functor.map_comp] at hFC
  have hs' :
      a ≫ J.mapDerivedCategory.map eC.hom ≫ J.mapDerivedCategoryFactors.hom.app C =
      SV.reduction.map b ≫ eD.hom ≫ DerivedCategory.Q.map f'.hom := hs
  have he := congrArg (fun g ↦ EV.mapDerivedCategory.map g ≫
      EV.mapDerivedCategoryFactors.hom.app ((J.mapHomologicalComplex (.up ℤ)).obj C) ≫
      DerivedCategory.Q.map ξ.hom ≫
      DerivedCategory.Q.map
        ((F.mapHomologicalComplex (.up ℤ)).map kC.hom)) hs'
  simp only [Functor.map_comp, Category.assoc] at he
  have hnγ := γ.hom.naturality eC.hom
  have hnF := F.mapDerivedCategoryFactors.hom.naturality kC.hom
  have hnEV := EV.mapDerivedCategoryFactors.hom.naturality f'.hom
  have hnρ := (SV.reductionEvaluation n).hom.naturality b
  simp only [Functor.comp_map, Functor.comp_obj] at hnγ hnF hnEV hnρ
  erw [reassoc_of% hnEV, hchainQ, reassoc_of% hDn,
    reassoc_of% hnρ] at he
  erw [← reassoc_of% hγ, reassoc_of% hnγ, ← hnF, reassoc_of% hFC] at he
  apply Iso.ext
  unfold integralOpenReductionAlpha integralOpenTensorRepresentativeIso
  dsimp only [compactSupportCanonicalJLevel, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, Functor.mapIso_hom]
  change
    (SV.reductionEvaluation n).inv.app
        (JO.mapDerivedCategory.obj (DerivedCategory.Q.obj Q)) ≫
      EV.mapDerivedCategory.map a ≫ γ.hom.app (SX.reduction.obj (DerivedCategory.Q.obj Q)) ≫
      F.mapDerivedCategory.map ((SX.reductionEvaluation n).hom.app (DerivedCategory.Q.obj Q)) =
    (coefficientFiniteDerivedExtension l E V n).map b ≫
      (coefficientFiniteReductionModel l E V
        ((JO.mapHomologicalComplex (.up ℤ)).obj Q) hJQ n).hom ≫
      DerivedCategory.Q.map χ.hom ≫
      F.mapDerivedCategoryFactors.inv.app ((TX.mapHomologicalComplex (.up ℤ)).obj Q) ≫
      F.mapDerivedCategory.map (coefficientFiniteReductionModel l E X Q hQ n).inv
  apply (cancel_epi ((SV.reductionEvaluation n).hom.app
    (JO.mapDerivedCategory.obj (DerivedCategory.Q.obj Q)))).mp
  apply (cancel_mono (F.mapDerivedCategory.map
      (coefficientFiniteReductionModel l E X Q hQ n).hom ≫
      F.mapDerivedCategoryFactors.hom.app ((TX.mapHomologicalComplex (.up ℤ)).obj Q))).mp
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id]
  erw [F.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]
  simpa only [Functor.map_comp, Category.assoc] using he

end WeilConjectures
