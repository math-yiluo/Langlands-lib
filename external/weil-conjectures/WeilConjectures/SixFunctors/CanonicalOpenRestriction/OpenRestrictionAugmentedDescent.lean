/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOpenReduction.IntegralOpenReductionDefinitions
import WeilConjectures.SixFunctors.CanonicalOpenRestriction.OrdinaryOpenRestrictionQuotient
import WeilConjectures.SixFunctors.CanonicalOpenRestriction.OpenRestrictionGoodComplex
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitOrdinaryAdjunction
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitFixedCalculusModels
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitCanonicalModels
import all WeilConjectures.SixFunctors.OpenSemilinearTensor.OrdinaryReductionAugmentedComputation
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Augmented restriction descent

Source: Stacks Project, Tags 0E8I, 0GL1, 03DJ, 06YY and 0941.
This isolates the representative construction, independently of reconstruction or
realization through total limits.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] HasDerivedCategory.standard
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.IntegralOpenReduction
namespace WeilConjectures.CanonicalOpenRestriction

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
  (o : Operations l E j)
  (SU : CoefficientDerivedSystemCalculus l E U)
  (SX : CoefficientDerivedSystemCalculus l E X)

local instance descentRestrictionLimits : PreservesFiniteLimits (restriction l E j o) := by
  let : PreservesLimitsOfSize.{0, 0} o.integral.inverse :=
    o.integral.toAdjunction.rightAdjoint_preservesLimits
  have h : PreservesFiniteLimits o.integral.inverse :=
    PreservesLimitsOfSize.preservesFiniteLimits o.integral.inverse
  dsimp only [restriction]
  exact @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ (by infer_instance) h

local instance descentRestrictionColimits : PreservesFiniteColimits (restriction l E j o) := by
  let : PreservesColimitsOfSize.{0, 0} o.integral.inverse :=
    o.integral.symm.toAdjunction.leftAdjoint_preservesColimits
  have h : PreservesFiniteColimits o.integral.inverse :=
    PreservesColimitsOfSize.preservesFiniteColimits o.integral.inverse
  dsimp only [restriction]
  exact @comp_preservesFiniteColimits _ _ _ _ _ _ _ _ (by infer_instance) h

local instance descentSystemRestrictionLimits :
    PreservesFiniteLimits (systemRestriction l E j o) := by
  let : PreservesLimitsOfSize.{0, 0} o.systems.inverse :=
    o.systems.toAdjunction.rightAdjoint_preservesLimits
  have h : PreservesFiniteLimits o.systems.inverse :=
    PreservesLimitsOfSize.preservesFiniteLimits o.systems.inverse
  dsimp only [systemRestriction]
  exact @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ (by infer_instance) h

local instance descentSystemRestrictionColimits :
    PreservesFiniteColimits (systemRestriction l E j o) := by
  let : PreservesColimitsOfSize.{0, 0} o.systems.inverse :=
    o.systems.symm.toAdjunction.leftAdjoint_preservesColimits
  have h : PreservesFiniteColimits o.systems.inverse :=
    PreservesColimitsOfSize.preservesFiniteColimits o.systems.inverse
  dsimp only [systemRestriction]
  exact @comp_preservesFiniteColimits _ _ _ _ _ _ _ _ (by infer_instance) h

private theorem augmentedComputation (T : Scheme.{t})
    (S : CoefficientDerivedSystemCalculus l E T) (M : CompletionUnit.OrdinaryModel l E T) :
    ∃ e : integralOperationsGoodLocalization l E T ⋙ S.reduction ≅
      (integralOperationsGoodComplex l E T).ι ⋙ M.quotient l E T ⋙ DerivedCategory.Q,
      ∀ R : (integralOperationsGoodComplex l E T).FullSubcategory,
        CoefficientReductionPresentation l E T S.toCoefficientDerivedSystemReduction
          R.obj R.property.1 _ (e.app R)
            (fun n ↦ (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app R.obj) ∧
        AugmentedPresentation l E T S R.obj _ (e.app R)
          (fun n ↦ (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app R.obj) := by
  obtain ⟨_, ε, _, hε, heval, hhom⟩ :=
    CompletionUnit.fixedDerivedComparison l E T S M
      (CompletionUnit.termwiseLimitComparison l E T)
      (CompletionUnit.termwiseLimitComparison_projection l E T)
      (CompletionUnit.constantLimitUnit l E T)
      (CompletionUnit.constantLimitUnit_normalization l E T)
  let e : integralOperationsGoodLocalization l E T ⋙ S.reduction ≅
      (integralOperationsGoodComplex l E T).ι ⋙ M.quotient l E T ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun R ↦
      @asIso _ _ _ _ (ε.app R.obj) (hε R.obj R.property.1 R.property.2))
      (fun {_ _} f ↦ ε.naturality f.hom)
  refine ⟨e, ?_⟩
  intro R
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro n
    exact heval R.obj R.property.1 R.property.2 n
  · intro m n h
    apply HomologicalComplex.hom_ext
    intro i
    exact M.transition (R.obj.X i) h
  · apply OpenSemilinearTensor.ordinaryAugmentedPresentation l E T S M R.obj (e.app R)
    have hh := hhom R.obj ((M.quotient l E T).obj R.obj) (𝟙 _)
    simp only [CategoryTheory.Functor.map_id] at hh
    erw [Category.comp_id, Adjunction.homEquiv_id] at hh
    exact hh

private theorem cancelComparison
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A B H I : D} {M N : C} (a : A ⟶ B) (b : B ⟶ H) (c : H ⟶ I)
    (d : F.obj N ≅ I) (e : M ≅ N) :
    (a ≫ b ≫ c ≫ d.inv ≫ F.map e.inv) ≫ F.map e.hom ≫ d.hom = a ≫ b ≫ c := by
  simp only [Category.assoc, ← F.map_comp_assoc, e.inv_hom_id,
    F.map_id, Category.id_comp, d.inv_hom_id, Category.comp_id]

/-- Descent of the strict restriction/tensor isomorphism, before identification with a mate.
Source: Stacks sites-modules.tex, Tags 03DJ and 0E8I; sites-cohomology.tex,
Tags 0G7E, 06YY, 0GL1 and 0941; first step of the canonical restriction construction.
(blueprint: lem-sf-open-restriction-augmented-descent).

Proof: use the ordinary quotient-tensor functor on the ringed sequence site. Its
augmentation consists of all scalar-adjunction units and its horizontal maps of the
quotient projections. Restriction to the localized site preserves flat terms and
K-flatness. Tensor and restriction commute by the sectionwise map keeping both
factors, and its inverse has the same formula. Transport using o.integral, o.finite
and o.systems, retaining their actual units and counits. The maps commute with the
quotient projections and scalar units, so they give one strict system isomorphism
and one augmented chain isomorphism on every good complex. In each degree its
finite component is the finite-adjunction transpose of inverse tensor comparison:
applying extension followed by its counit sends each summand tensor generator to
the original restricted tensor. The generator normalization of tensor identifies
this map with the unit/inverse-tensor/counit word displayed below.

Derive the ordinary quotient-tensor/limit adjunction on the sequence site. Uniqueness
of left adjoints compares its reduction with SU.reduction and SX.reduction. These
comparisons take scalar units to the augmentations just constructed; the finite
adjunctions identify their evaluations with the recorded reductionEvaluation maps.
Conjugate the localized strict chain isomorphism by these comparisons. Naturality
for chain maps and inverse quasi-isomorphisms descends it along the localization of
good complexes. Each component has the localized chain inverse, giving s. These
conjugations are its displayed representative square. This construction uses no
extension comparison r, no completeness, and includes zero complexes and empty opens. -/
theorem openRestrictionAugmentedDescent
    (tensor : TensorComparison l E j o) :
    ∃ s : star l E j o ⋙ SU.reduction ≅ SX.reduction ⋙ P l E j o,
      (∀ (Q : CochainComplex (scalarReductionSource l E X) ℤ)
    (hQ : integralOperationsGoodComplex l E X Q),
    ∃ (hRes : integralOperationsGoodComplex l E U
        (((restriction l E j o).mapHomologicalComplex (.up ℤ)).obj Q))
      (CX : CochainComplex (coefficientSequenceModules l E X) ℤ)
      (CU : CochainComplex (coefficientSequenceModules l E U) ℤ)
      (eX : SX.reduction.obj (DerivedCategory.Q.obj Q) ≅ DerivedCategory.Q.obj CX)
      (eU : SU.reduction.obj (DerivedCategory.Q.obj
        (((restriction l E j o).mapHomologicalComplex (.up ℤ)).obj Q)) ≅ DerivedCategory.Q.obj CU)
      (κX : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj CX ≅
          ((scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ)).obj Q)
      (κU : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E U n).mapHomologicalComplex (.up ℤ)).obj CU ≅
          ((scalarReductionExtension l E U n).mapHomologicalComplex (.up ℤ)).obj
            (((restriction l E j o).mapHomologicalComplex (.up ℤ)).obj Q))
      (f : CU ≅ ((systemRestriction l E j o).mapHomologicalComplex (.up ℤ)).obj CX),
      CoefficientReductionPresentation l E X SX.toCoefficientDerivedSystemReduction
        Q hQ.1 CX eX κX ∧
      AugmentedPresentation l E X SX Q CX eX κX ∧
      CoefficientReductionPresentation l E U SU.toCoefficientDerivedSystemReduction
        (((restriction l E j o).mapHomologicalComplex (.up ℤ)).obj Q) hRes.1 CU eU κU ∧
      AugmentedPresentation l E U SU
        (((restriction l E j o).mapHomologicalComplex (.up ℤ)).obj Q) CU eU κU ∧
      (SU.reduction.map ((restriction l E j o).mapDerivedCategoryFactors.hom.app Q) ≫
        eU.hom ≫ DerivedCategory.Q.map f.hom =
      s.hom.app (DerivedCategory.Q.obj Q) ≫ (P l E j o).map eX.hom ≫
        (systemRestriction l E j o).mapDerivedCategoryFactors.hom.app CX) ∧
      (∀ (n : ℕ) (i : ℤ),
        (coefficientSequenceEvaluation l E U n).map (f.hom.f i) ≫
          ((o.finite n).unitIso.app _ ≪≫
    (o.finite n).inverse.mapIso
      ((o.transportEvaluation n).app ((systemRestriction l E j o).obj (CX.X i))).symm ≪≫
    (o.finite n).inverse.mapIso
      ((SemilinearSections.evaluation.{t+1, t, max u (t+1)}
        ((ProEt.topology X).over (openObject j))
        (fun k ↦ (rings l E X k).over (openObject j))
        (fun k ↦ ((ProEt.topology X).overPullback CommRingCat.{max u (t+1)}
          (openObject j)).map (transitions l E X k)) n).mapIso
        (o.systems.counitIso.app _)) ≪≫
    (o.finite n).inverse.mapIso ((o.openSystems.restrictionEvaluation n).app (CX.X i))).hom ≫
          (finiteRestriction l E j o n).map ((κX n).hom.f i) =
        (κU n).hom.f i ≫ (((o.finite n).toAdjunction.comp
          (SheafOfModules.localizedSystemAdjunction.{t+1, t, max u (t+1)}
            (rings l E X n) (openObject j))).unit.app _ ≫
    (finiteRestriction l E j o n).map
      ((tensor.ordinary n).inv.app ((restriction l E j o).obj (Q.X i))) ≫
    (finiteRestriction l E j o n).map
      ((scalarReductionExtension l E X n).map
        ((ordinaryAdjunction l E j o).counit.app (Q.X i)))))) := by
  let MX := Classical.choice (CompletionUnit.ordinaryModel_exists l E X)
  let MU := Classical.choice (CompletionUnit.ordinaryModel_exists l E U)
  let eX := (augmentedComputation l E X SX MX).choose
  have heX := (augmentedComputation l E X SX MX).choose_spec
  let eU := (augmentedComputation l E U SU MU).choose
  have heU := (augmentedComputation l E U SU MU).choose_spec
  let ordinary := (ordinaryRestrictionQuotient l E j o tensor MX MU).choose
  have hord := (ordinaryRestrictionQuotient l E j o tensor MX MU).choose_spec
  let goodX := integralOperationsGoodComplex l E X
  let goodU := integralOperationsGoodComplex l E U
  let R := (restriction l E j o).mapHomologicalComplex (.up ℤ)
  let G : goodX.FullSubcategory ⥤ goodU.FullSubcategory :=
    ObjectProperty.lift goodU (goodX.ι ⋙ R)
      (fun Q ↦ restriction_preservesGood l E j o Q.obj Q.property)
  let L := integralOperationsGoodLocalization l E X
  let W := (HomologicalComplex.quasiIso
    (scalarReductionSource l E X) (.up ℤ)).inverseImage goodX.ι
  let : L.IsLocalization W := integralOperationsGoodLocalization_isLocalization l E X
  let ec : R ⋙ MU.quotient l E U ≅
      MX.quotient l E X ⋙ (systemRestriction l E j o).mapHomologicalComplex (.up ℤ) :=
    NatIso.ofComponents (fun Q ↦ HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ ordinary.app (Q.X i)) (by
        intro i k hik
        exact (ordinary.hom.naturality (Q.d i k)).symm)) (by
      intro Q Q' f
      apply HomologicalComplex.Hom.ext
      funext i
      exact ordinary.hom.naturality (f.f i))
  let b : L ⋙ (star l E j o ⋙ SU.reduction) ≅
      L ⋙ (SX.reduction ⋙ P l E j o) :=
    Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft goodX.ι (restriction l E j o).mapDerivedCategoryFactors)
        SU.reduction ≪≫
      Functor.isoWhiskerLeft G eU ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft goodX.ι ec) DerivedCategory.Q ≪≫
      Functor.isoWhiskerLeft (goodX.ι ⋙ MX.quotient l E X)
        (systemRestriction l E j o).mapDerivedCategoryFactors.symm ≪≫
      Functor.isoWhiskerRight eX.symm (P l E j o)
  let s := Localization.liftNatIso L W _ _
    (star l E j o ⋙ SU.reduction) (SX.reduction ⋙ P l E j o) b
  refine ⟨s, ?_⟩
  intro Q hQ
  let QX : goodX.FullSubcategory := ⟨Q, hQ⟩
  refine ⟨(G.obj QX).property, (MX.quotient l E X).obj Q,
    (MU.quotient l E U).obj (R.obj Q), eX.app QX, eU.app (G.obj QX),
    (fun n ↦ (NatIso.mapHomologicalComplex (MX.evaluation n) (.up ℤ)).app Q),
    (fun n ↦ (NatIso.mapHomologicalComplex (MU.evaluation n) (.up ℤ)).app (R.obj Q)),
    ec.app Q, (heX QX).1, (heX QX).2, (heU (G.obj QX)).1, (heU (G.obj QX)).2, ?_, ?_⟩
  · have hs : s.hom.app (L.obj QX) = b.hom.app QX := by
      dsimp only [s, Localization.liftNatIso]
      simp only [Localization.liftNatTrans_app, Localization.Lifting.iso,
        Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp, Category.comp_id]
    change _ = s.hom.app (L.obj QX) ≫ _ ≫ _
    have hc : _ = b.hom.app QX ≫ (P l E j o).map (eX.app QX).hom ≫
        (systemRestriction l E j o).mapDerivedCategoryFactors.hom.app
          ((MX.quotient l E X).obj Q) := (cancelComparison (P l E j o)
      (M := SX.reduction.obj (DerivedCategory.Q.obj Q))
      (N := DerivedCategory.Q.obj ((MX.quotient l E X).obj Q))
      (SU.reduction.map ((restriction l E j o).mapDerivedCategoryFactors.hom.app Q))
      (eU.hom.app (G.obj QX)) (DerivedCategory.Q.map (ec.hom.app Q))
      ((systemRestriction l E j o).mapDerivedCategoryFactors.app
        ((MX.quotient l E X).obj Q)) (eX.app QX)).symm
    exact hc.trans (congrArg (fun k ↦ k ≫ (P l E j o).map (eX.app QX).hom ≫
      (systemRestriction l E j o).mapDerivedCategoryFactors.hom.app
        ((MX.quotient l E X).obj Q)) hs.symm)
  · intro n i
    exact hord (Q.X i) n

end WeilConjectures.CanonicalOpenRestriction
