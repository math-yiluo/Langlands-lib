/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitCanonicalModels
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitFiniteMateComparison
import WeilConjectures.TraceFormula.Coherent.CoherentQuotientModelComparison

/-! # Whole-system comparison of strict quotient presentations

Source: Stacks 06YY, 0941 and 099N(5), the strict quotient-system construction.
(blueprint: lem-trf-coherent-quotient-reduction-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  constantSheaf
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem modelsForCalculus (W : Scheme.{t})
    (hlW : ∀ x : W, IsUnit (l : W.residueField x))
    (S : CoefficientDerivedSystemCalculus l E W) :
    ∃ (M : CompletionUnit.OrdinaryModel l E W),
      Nonempty (CompletionUnit.DerivedModel l E W S M) := by
  let (x : W) : Invertible (l : W.residueField x) := (hlW x).invertible
  obtain ⟨S₀, _, M, ⟨D₀⟩⟩ := CompletionUnit.canonicalModels l E W
  let θ := S.adjunction.leftAdjointUniq S₀.adjunction
  let ε : DerivedCategory.Q ⋙ S.reduction ⟶ M.quotient l E W ⋙ DerivedCategory.Q :=
    Functor.whiskerLeft DerivedCategory.Q θ.hom ≫ D₀.reductionComparison
  have hε : S.reduction.IsLeftDerivedFunctor ε
      (HomologicalComplex.quasiIso (scalarReductionSource l E W) (.up ℤ)) :=
    (Functor.isLeftDerivedFunctor_iff_of_iso
      (LF := S.reduction) (LF' := S₀.reduction) (α := ε) D₀.reductionComparison
      (HomologicalComplex.quasiIso (scalarReductionSource l E W) (.up ℤ)) θ rfl).2
        D₀.reduction_isLeftDerived
  have hhom (Q : CochainComplex (scalarReductionSource l E W) ℤ)
      (I : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (a : (M.quotient l E W).obj Q ⟶ I) :
      S.adjunction.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)
          (ε.app Q ≫ DerivedCategory.Q.map a) =
        DerivedCategory.Q.map
          ((M.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv Q I a) ≫
            D₀.systemUnit.app I := by
    rw [← D₀.hom_normalization Q I a]
    change S.adjunction.homEquiv _ _
      ((θ.hom.app (DerivedCategory.Q.obj Q) ≫ D₀.reductionComparison.app Q) ≫
        DerivedCategory.Q.map a) = _
    rw [Category.assoc, S.adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
    rw [S.adjunction.unit_leftAdjointUniq_hom_app S₀.adjunction]
    exact (S₀.adjunction.homEquiv_unit _ _ _).symm
  refine ⟨M, ⟨{
    towerLimitComparison := D₀.towerLimitComparison
    towerLimitComparison_projection := D₀.towerLimitComparison_projection
    limitUnit := D₀.limitUnit
    limitUnit_normalization := D₀.limitUnit_normalization
    roos := D₀.roos
    roos_normalization := D₀.roos_normalization
    systemUnit := D₀.systemUnit
    system_isIso := D₀.system_isIso
    systemUnit_composition := D₀.systemUnit_composition
    reductionComparison := ε
    reduction_isLeftDerived := hε
    reduction_isIso := ?_
    reduction_evaluation := ?_
    hom_normalization := hhom }⟩⟩
  · intro Q hQ hf
    have := D₀.reduction_isIso Q hQ hf
    change IsIso (θ.hom.app (DerivedCategory.Q.obj Q) ≫ D₀.reductionComparison.app Q)
    infer_instance
  · apply CompletionUnit.finiteComparison_of_unit l E W S M D₀.towerLimitComparison
      D₀.towerLimitComparison_projection D₀.limitUnit D₀.limitUnit_normalization ε
    intro Q
    have h := hhom Q ((M.quotient l E W).obj Q) (𝟙 _)
    have hid : ε.app Q ≫ DerivedCategory.Q.map
        (𝟙 ((M.quotient l E W).obj Q)) = ε.app Q := by
      rw [CategoryTheory.Functor.map_id]
      exact Category.comp_id _
    rw [hid] at h
    simpa only [Adjunction.homEquiv_id, D₀.systemUnit_composition,
      Category.assoc] using h

attribute [local irreducible] CoefficientReductionPresentation

/-- A coherent presentation is the canonical derived reduction comparison followed
by the unique strict quotient isomorphism fixed by its finite comparisons.
Source: Stacks 06YY, 06YS, 0941, ordinary tensor/restriction adjunction and descent.
(blueprint: lem-trf-coherent-quotient-reduction-comparison).

Proof: form the ordinary quotient tensor system, with transition maps induced by
quotient reduction and unit given by the sections 1 tensor x. The extension/restriction
Hom bijections and the limit universal property give its adjunction. Derive this
adjunction using flat-term K-flat resolutions and simultaneous K-injective resolutions.
Exact restriction identifies the right derived functor with coefficientSequenceLimit.
The unique comparison of left adjoints transports the derived counit to the supplied
S.reduction. Its finite comparisons agree by transposing S.unit_projection and
S.counit_projection, so the resulting ordinary and derived data are M and D.
For a presentation, transpose its coherent strict tower map through the ordinary
constant/limit and tensor/limit adjunctions to obtain a chain map a. Its prescribed
generator values identify every finite scalar adjunct with the tensor unit. The
finite Hom bijections give the last equation below; these finite isomorphisms
detect that a itself is an isomorphism of strict system complexes.
The ordinary adjunction transposes D.reductionComparison followed by Q(a) to the
localization of the strict tensor-unit map. Coherence transposes e to exactly the
same entire tower map. The constant/limit and reduction/limit Hom bijections are
injective, proving the displayed equality before taking any derived limit.
Zero complexes and exponent one use the same adjunctions; no completeness or
faithfulness of finite derived evaluation is assumed. -/
theorem coherentQuotientReductionComparison (W : Scheme.{t})
    (_hlW : ∀ x : W, IsUnit (l : W.residueField x))
    (S : CoefficientDerivedSystemCalculus l E W) :
    ∃ (M : CompletionUnit.OrdinaryModel l E W)
      (D : CompletionUnit.DerivedModel l E W S M),
    ∀ (P : (integralOperationsGoodComplex l E W).FullSubcategory)
      (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (e : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
      (κ : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
          (unrestrictedIntegralFiniteComplex l E W n).obj P.obj),
      CoefficientReductionPresentation l E W S.toCoefficientDerivedSystemReduction
        P.obj P.property.1 C e κ →
      IsIntegralComparisonPresentationCoherent l E W S P.obj C e κ →
      ∃ a : (M.quotient l E W).obj P.obj ≅ C,
        D.reductionComparison.app P.obj ≫ DerivedCategory.Q.map a.hom = e.hom ∧
        ∀ n : ℕ,
          ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).mapIso a ≪≫
            κ n = (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app P.obj := by
  obtain ⟨M, ⟨D⟩⟩ := modelsForCalculus l E W _hlW S
  refine ⟨M, D, ?_⟩
  intro P C e κ _hpres hcoh
  exact coherentQuotientModelComparison l E W S M D P.obj C e κ hcoh

end WeilConjectures
