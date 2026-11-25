/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenSemilinearTensorModelData
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitFixedCalculusModels
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitCanonicalModels
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionOrdinaryAssociationChain

/-! # Augmented open reduction descent

Source: Stacks Project, Modules on Sites, Tags 0E8I and 03DI.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.SemilinearSections
namespace WeilConjectures.OpenSemilinearTensor
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  coefficientSequenceRestriction coefficientSequenceEvaluation

private theorem ordinaryIso (W : Scheme.{t})
    (M : CompletionUnit.OrdinaryModel l E W) (A : OrdinaryReduction l E W) :
    ∃ b : M.tensor ≅ A.functor, ∀ (P : scalarReductionSource l E W) (n : ℕ),
      (coefficientSequenceEvaluation l E W n).map (b.hom.app P) ≫
        (A.evaluation n).hom.app P = (M.evaluation n).hom.app P := by
  classical
  have existsIso (P : scalarReductionSource l E W) :=
    WeilConjectures.sequenceIsoOfSuccessor l E W (M.tensor.obj P) (A.functor.obj P)
      (fun n ↦ (M.evaluation n).app P ≪≫ ((A.evaluation n).app P).symm)
      (by
        intro n
        dsimp only [Iso.trans_hom, Iso.symm_hom, Iso.app]
        apply (cancel_mono ((normalizedDVRModuleRes l E W (Nat.le_succ n)).map
          ((A.evaluation n).hom.app P))).1
        simp only [Functor.map_comp, Category.assoc]
        rw [A.quotient P (n + 1) n (Nat.le_succ n)]
        simp only [Iso.inv_hom_id_app_assoc]
        rw [← M.transition P (Nat.le_succ n)]
        simp only [← Functor.map_comp, Iso.inv_hom_id_app,
          Category.comp_id])
  choose b hb using existsIso
  let e : M.tensor ≅ A.functor := NatIso.ofComponents b (by
    intro P Q f
    apply WeilConjectures.sequence_hom_ext l E W
    intro n
    simp only [Functor.map_comp, hb]
    exact ((M.evaluation n) ≪≫ (A.evaluation n).symm).hom.naturality f)
  refine ⟨e, ?_⟩
  intro P n
  dsimp only [e, NatIso.ofComponents_hom_app]
  rw [hb]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]

private theorem ordinaryUnitTransport (W : Scheme.{t})
    (M : CompletionUnit.OrdinaryModel l E W) (A : OrdinaryReduction l E W)
    (b : M.tensor ≅ A.functor)
    (hb : ∀ (P : scalarReductionSource l E W) (n : ℕ),
      (coefficientSequenceEvaluation l E W n).map (b.hom.app P) ≫
        (A.evaluation n).hom.app P = (M.evaluation n).hom.app P)
    (P : scalarReductionSource l E W) (n : ℕ) (V : W.ProEtᵒᵖ)
    (x : P.val.obj V) :
    ((((M.adjunction.ofNatIsoLeft b).unit.app P) ≫
      limit.π ((coefficientSequenceRestriction l E W).obj (A.functor.obj P)) (op n) ≫
      (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
        (A.functor.obj P) ≫
      (scalarReductionRestriction l E W n).map ((A.evaluation n).hom.app P)).val.app V) x =
      unrestrictedIntegralTensorSection l E W n P V 1 x := by
  have hm : (M.adjunction.ofNatIsoLeft b).unit.app P ≫
      limit.π ((coefficientSequenceRestriction l E W).obj (A.functor.obj P)) (op n) ≫
      (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
        (A.functor.obj P) ≫
      (scalarReductionRestriction l E W n).map ((A.evaluation n).hom.app P) =
    M.adjunction.unit.app P ≫
      limit.π ((coefficientSequenceRestriction l E W).obj (M.tensor.obj P)) (op n) ≫
      (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
        (M.tensor.obj P) ≫
      (scalarReductionRestriction l E W n).map ((M.evaluation n).hom.app P) := by
    simp only [Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app, Functor.whiskerRight_app]
    change (M.adjunction.unit.app P ≫
      lim.map ((coefficientSequenceRestriction l E W).map (b.hom.app P))) ≫ _ ≫ _ ≫ _ = _
    simp only [lim_map, Category.assoc]
    rw [reassoc_of% (limMap_π ((coefficientSequenceRestriction l E W).map
      (b.hom.app P)) (op n))]
    have he := (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.naturality
      (b.hom.app P)
    change ((coefficientSequenceRestriction l E W).map (b.hom.app P)).app (op n) ≫
      (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
        (A.functor.obj P) = _ at he
    rw [reassoc_of% he]
    rw [← Functor.map_comp, hb]
  exact (congrArg (fun f ↦ f.val.app V x) hm).trans (M.unit_tensor P n V x)

private theorem eqIsoSection (W : Scheme.{t}) {I : Type*} [Category I]
    {F G : I ⥤ scalarReductionSource l E W} (h : F = G) (P : I)
    (V : W.ProEtᵒᵖ) (x : (F.obj P).val.obj V) :
    HEq (((eqToIso h).hom.app P).val.app V x) x := by
  cases h
  rfl

private theorem ordinaryUnitSection (W : Scheme.{t})
    (M : CompletionUnit.OrdinaryModel l E W) (P : scalarReductionSource l E W)
    (n : ℕ) (V : W.ProEtᵒᵖ) (x : P.val.obj V) :
    HEq (((M.adjunction.unit.app P ≫
      limit.π ((coefficientSequenceRestriction l E W).obj (M.tensor.obj P))
        (op n)).val.app V) x)
      (((M.evaluation n).inv.app P).val.app V
        (coefficientIntegralScalarUnitSection l E W n P V x)) := by
  have hu := M.unit_tensor P n V x
  have hs := (scalarReductionExtension_adjunction l E W n).choose_spec
    P V x
  have hh : ((eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
      (M.tensor.obj P) ≫
      (scalarReductionRestriction l E W n).map
        ((M.evaluation n).hom.app P)).val.app V
      (((M.adjunction.unit.app P ≫ limit.π _ (op n)).val.app V) x) =
    coefficientIntegralScalarUnitSection l E W n P V x := by
    change _ = (((scalarReductionExtension_adjunction l E W n).choose.unit.app
      P).val.app V) x
    refine hu.trans ?_
    dsimp only [unrestrictedIntegralTensorSection, unrestrictedIntegralReductionFunctor,
      unrestrictedIntegralReductionExistence, scalarReductionExistence] at hs ⊢
    exact hs.symm
  let N := (scalarReductionRestriction l E W n).obj
    ((coefficientSequenceEvaluation l E W n).obj (M.tensor.obj P))
  let s := (scalarReductionRestriction l E W n).mapIso
    ((M.evaluation n).app P)
  let y : N.val.obj V :=
    ((eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
      (M.tensor.obj P)).val.app V
      (((M.adjunction.unit.app P ≫ limit.π _ (op n)).val.app V) x)
  have hi := congrArg (fun z ↦ s.inv.val.app V z) hh
  have he := congrArg (fun g : N ⟶ N ↦ g.val.app V y) s.hom_inv_id
  have hx := eqIsoSection l E W
    (coefficientSequenceRestriction_evaluation l E W n)
    (M.tensor.obj P) V
    (((M.adjunction.unit.app P ≫ limit.π _ (op n)).val.app V) x)
  change s.inv.val.app V (s.hom.val.app V y) = y at he
  change s.inv.val.app V (s.hom.val.app V y) = _ at hi
  exact hx.symm.trans (heq_of_eq (he.symm.trans hi))

-- Prove the generic mate formula before specializing to the coefficient sheaf categories.
private theorem derivedAdjunctionTranspose {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (δ : C ⥤ D) (L : D ⥤ C) [δ.Additive] [L.Additive]
    [PreservesFiniteLimits δ] [PreservesFiniteColimits δ] (adj : δ ⊣ L)
    (Q : CochainComplex C ℤ) (Z : CochainComplex D ℤ)
    (a : (δ.mapHomologicalComplex (.up ℤ)).obj Q ⟶ Z) :
    adj.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _
      (δ.mapDerivedCategoryFactors.hom.app Q ≫ DerivedCategory.Q.map a) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv Q Z a) ≫
        L.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj Z) := by
  have hf : δ.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj Q) =
      δ.mapDerivedCategoryFactors.hom.app Q := by
    erw [δ.mapDerivedCategoryFactorsh_hom_app Q]
    change δ.mapDerivedCategory.map (𝟙 _) ≫ _ ≫ 𝟙 _ ≫
      DerivedCategory.Qh.map (𝟙 _) = _
    erw [CategoryTheory.Functor.map_id, DerivedCategory.Qh.map_id,
      Category.id_comp, Category.comp_id]
    exact Category.comp_id _
  have hη := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ))
    δ.mapDerivedCategoryFactorsh.hom L.rightDerivedFunctorUnit
    ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient, hf] at hη
  have hn := L.rightDerivedFunctorUnit.naturality
    ((HomotopyCategory.quotient _ (.up ℤ)).map a)
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  change ((adj.mapDerivedCategoryRightDerivedAdjunction).unit.app _ ≫
    L.rightDerivedFunctor.map (δ.mapDerivedCategoryFactors.hom.app Q)) ≫ _ = _
  erw [hη]
  rw [Category.assoc]
  erw [← hn]
  change DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app Q) ≫
    DerivedCategory.Q.map ((L.mapHomologicalComplex (.up ℤ)).map a) ≫ _ = _
  rw [← DerivedCategory.Q.map_comp_assoc]
  rfl

private theorem constantTranspose (W : Scheme.{t})
    (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (a : ((Functor.const ℕᵒᵖ : scalarReductionSource l E W ⥤ _).mapHomologicalComplex
      (.up ℤ)).obj Q ⟶ Z) :
    (integralComparisonConstantAdjunction l E W).homEquiv _ _
      ((Functor.const ℕᵒᵖ : scalarReductionSource l E W ⥤ _).mapDerivedCategoryFactors.hom.app Q ≫
        DerivedCategory.Q.map a) =
      DerivedCategory.Q.map
          (((constLimAdj : (Functor.const ℕᵒᵖ : scalarReductionSource l E W ⥤ _) ⊣
            lim).mapHomologicalComplex (.up ℤ)).homEquiv Q Z a) ≫
        DerivedCategory.Q.map ((CompletionUnit.termwiseLimitComparison l E W).hom.app Z) ≫
          (CompletionUnit.constantLimitUnit l E W).app Z := by
  let δ : scalarReductionSource l E W ⥤ ℕᵒᵖ ⥤ scalarReductionSource l E W :=
    Functor.const ℕᵒᵖ
  let L : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W := lim
  let adj : δ ⊣ L := constLimAdj
  have hc : DerivedCategory.Q.map
        ((CompletionUnit.termwiseLimitComparison l E W).hom.app Z) ≫
      (CompletionUnit.constantLimitUnit l E W).app Z =
    L.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj Z) := by
    dsimp only [CompletionUnit.constantLimitUnit, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.trans_hom,
      Functor.associator_hom_app, Functor.associator_inv_app]
    simp only [Category.assoc]
    have hq : (DerivedCategory.quotientCompQhIso
        (ℕᵒᵖ ⥤ scalarReductionSource l E W)).hom.app Z = 𝟙 _ := rfl
    have hqi (K : CochainComplex (scalarReductionSource l E W) ℤ) :
        (DerivedCategory.quotientCompQhIso (scalarReductionSource l E W)).inv.app K =
          𝟙 _ := rfl
    have hfac : ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
        scalarReductionSource l E W).mapHomotopyCategoryFactors (.up ℤ)).inv.app Z =
          𝟙 _ := rfl
    erw [hq, hqi, hfac]
    simp only [Functor.comp_obj, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
      ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    rfl
  rw [hc]
  exact derivedAdjunctionTranspose δ L adj Q Z a

-- Keep the strict augmentation calculation independent of a transported model's data.
private theorem ordinaryAugmentedPresentation (W : Scheme.{t})
    (S : CoefficientDerivedSystemCalculus l E W) (M : CompletionUnit.OrdinaryModel l E W)
    (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj Q) ≅
      DerivedCategory.Q.obj ((M.quotient l E W).obj Q))
    (he : S.adjunction.homEquiv _ _ e.hom =
      DerivedCategory.Q.map ((M.adjunction.mapHomologicalComplex (.up ℤ)).unit.app Q) ≫
        (CompletionUnit.systemLimitUnit l E W M
          (CompletionUnit.constantLimitUnit l E W)).app ((M.quotient l E W).obj Q)) :
    IntegralOpenReduction.AugmentedPresentation l E W S Q _ e
      (fun n ↦ (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app Q) := by
  let C := (M.quotient l E W).obj Q
  let Z := ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C
  let d := Functor.mapHomologicalComplexCompIso
    (Iso.refl (coefficientSequenceRestriction l E W ⋙
      (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ _))) (.up ℤ)
  let f : Q ⟶ ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)).obj Z :=
    (M.adjunction.mapHomologicalComplex (.up ℤ)).unit.app Q ≫ d.inv.app C
  let a := ((constLimAdj : (Functor.const ℕᵒᵖ : scalarReductionSource l E W ⥤ _) ⊣
    lim).mapHomologicalComplex (.up ℤ)).homEquiv Q Z |>.symm f
  refine ⟨a, ?_, ?_⟩
  · intro i n V x
    have ha : (a.f i).app (op n) =
        M.adjunction.unit.app (Q.X i) ≫
          limit.π ((coefficientSequenceRestriction l E W).obj
            (M.tensor.obj (Q.X i))) (op n) := by
      dsimp only [a, f, Adjunction.homEquiv_counit, HomologicalComplex.comp_f,
        Functor.mapHomologicalComplex_map_f, Adjunction.mapHomologicalComplex_counit_app_f,
        Adjunction.mapHomologicalComplex_unit_app_f]
      change (M.adjunction.unit.app (Q.X i) ≫ 𝟙 _) ≫
        limit.π _ (op n) = _
      rw [Category.comp_id]
    rw [ha]
    change HEq _ (((M.evaluation n).inv.app (Q.X i)).val.app V
      (coefficientIntegralScalarUnitSection l E W n (Q.X i) V x))
    exact ordinaryUnitSection l E W M (Q.X i) n V x
  · change S.adjunction.homEquiv _ _ e.hom = _
    rw [he]
    have hn := (integralComparisonConstantAdjunction l E W).homEquiv_naturality_right
      ((Functor.const ℕᵒᵖ : scalarReductionSource l E W ⥤ _).mapDerivedCategoryFactors.hom.app
        Q ≫ DerivedCategory.Q.map a)
      ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app C)
    rw [Category.assoc] at hn
    erw [hn]
    rw [constantTranspose l E W Q Z a, Equiv.apply_symm_apply]
    have hd : d.inv.app C ≫
        (CompletionUnit.termwiseLimitComparison l E W).hom.app Z =
        M.limitComparison.hom.app C := by
      apply limit.hom_ext
      intro n
      apply HomologicalComplex.hom_ext
      intro i
      rw [Category.assoc, HomologicalComplex.comp_f]
      erw [CompletionUnit.termwiseLimitComparison_projection l E W Z n.unop i]
      change (𝟙 _ ≫ _) = _
      rw [Category.id_comp]
      exact (M.limitComparison_projection C n.unop i).symm
    change _ ≫ (DerivedCategory.Q.map (M.limitComparison.hom.app C) ≫
      (CompletionUnit.constantLimitUnit l E W).app Z ≫ _) = _
    dsimp only [f]
    simp only [Functor.map_comp, Category.assoc]
    rw [← DerivedCategory.Q.map_comp_assoc (d.inv.app C)
      ((CompletionUnit.termwiseLimitComparison l E W).hom.app Z), hd]
    rfl

/-- Natural augmented computation of a single ordinary quotient reduction on good models.
Source: Stacks 06YS, 06YY, 0941 and 09T5
(blueprint: lem-sf-ordinary-reduction-augmented-computation).

Proof: The evaluation isomorphisms and their quotient equations identify A with the
ordinary simultaneous quotient-tensor functor. Transport the actual scalar units through
these isomorphisms; their quotient compatibility gives one strict augmentation. Derive
the ordinary tensor/limit adjunction using flat-term K-flat resolutions and K-injective
resolutions on the sequence site. Its right adjoint is the specified total limit.
Uniqueness of left adjoints identifies its left functor with S.reduction. The normalized
adjunction identifies the transpose of its comparison with the strict augmentation.
Finite scalar adjunctions and the unit-projection equations give the presentation
normalization. This supplies a natural comparison on the full category of good models,
including its augmentation as a whole system arrow. -/
theorem ordinaryReductionAugmentedComputation (W : Scheme.{t})
    (S : CoefficientDerivedSystemCalculus l E W)
    (cS : CoefficientDerivedSystemCoherence l E W S) (A : OrdinaryReduction l E W) :
    ∃ e : integralOperationsGoodLocalization l E W ⋙ S.reduction ≅
      (integralOperationsGoodComplex l E W).ι ⋙
        A.functor.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q,
      ∀ P : (integralOperationsGoodComplex l E W).FullSubcategory,
        CoefficientReductionPresentation l E W S.toCoefficientDerivedSystemReduction
          P.obj P.property.1 _ (e.app P) (A.complexEvaluation l E P.obj) ∧
        IntegralOpenReduction.AugmentedPresentation l E W S P.obj _ (e.app P)
          (A.complexEvaluation l E P.obj) := by
  have _coherence := cS
  obtain ⟨M₀, ⟨D₀⟩⟩ := CompletionUnit.fixedCalculusModels l E W S
  obtain ⟨b, hb⟩ := ordinaryIso l E W M₀ A
  let M : CompletionUnit.OrdinaryModel l E W := {
    tensor := A.functor
    additive := A.additive
    evaluation := A.evaluation
    transition := fun P {_ _} h ↦ A.quotient P _ _ h
    adjunction := M₀.adjunction.ofNatIsoLeft b
    unit_tensor := ordinaryUnitTransport l E W M₀ A b hb
    limitComparison := M₀.limitComparison
    limitComparison_projection := M₀.limitComparison_projection }
  obtain ⟨_, ε, _, hε, heval, hhom⟩ :=
    CompletionUnit.fixedDerivedComparison l E W S M
      (CompletionUnit.termwiseLimitComparison l E W)
      (CompletionUnit.termwiseLimitComparison_projection l E W)
      (CompletionUnit.constantLimitUnit l E W)
      (CompletionUnit.constantLimitUnit_normalization l E W)
  let e : integralOperationsGoodLocalization l E W ⋙ S.reduction ≅
      (integralOperationsGoodComplex l E W).ι ⋙
        A.functor.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun P ↦
      @asIso _ _ _ _ (ε.app P.obj) (hε P.obj P.property.1 P.property.2))
      (fun {_ _} f ↦ ε.naturality f.hom)
  refine ⟨e, ?_⟩
  intro P
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro n
    exact heval P.obj P.property.1 P.property.2 n
  · intro m n h
    apply HomologicalComplex.hom_ext
    intro i
    exact A.quotient (P.obj.X i) m n h
  · apply ordinaryAugmentedPresentation l E W S M P.obj (e.app P)
    have hh := hhom P.obj ((M.quotient l E W).obj P.obj) (𝟙 _)
    simp only [CategoryTheory.Functor.map_id] at hh
    erw [Category.comp_id, Adjunction.homEquiv_id] at hh
    exact hh

end WeilConjectures.OpenSemilinearTensor
