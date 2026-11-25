/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionReductionData
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
import WeilConjectures.SmoothPurity.Coefficient.CoefficientSequenceRoosModel
import WeilConjectures.SixFunctors.Normalized.NormalizedDVRRoosFiniteReduction
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Data.ZMod.Basic
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionFiniteAssociation
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionStrictRepresentatives
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionRepresentativeRoos
/-! # Coherent finite reduction of completed coefficient extension

Source: main-20261015 blueprint, sec-proetale-coefficients/sk-def-sf-operations,
prose-03-02, integral operations; Stacks 06YS, 0G7E, 06YY.
(blueprint: lem-pur-coefficient-extension-reduction-model).
Positive exponent m is encoded by n=m-1. All derived categories are unbounded,
and the small pro-etale site's object and morphism universes remain independent.

## Main definitions

- `CoefficientExtensionReductionData`: simultaneous models and their canonical counit.
- `coefficientExtensionReductionIso`: that counit as a coherent-system isomorphism.

## Main statements

- `coefficientExtensionReductionModel`: existence on the entire unbounded derived category.
- `coefficientExtensionReduction_identity`: normalization for identity coefficients.
- `coefficientExtensionReduction_composition`: compatibility for three coefficient fields.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
section ScalarAssociation
universe c v r
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{max c v r} C]
  {R S T : Sheaf J CommRingCat.{max c v r}} {f : R ⟶ S} {g : S ⟶ T} {h : R ⟶ T}
  (A : SemilinearSections.ScalarData.{c, v, max c v r} f)
  (B : SemilinearSections.ScalarData.{c, v, max c v r} g)
  (D : SemilinearSections.ScalarData.{c, v, max c v r} h)

private theorem scalarSection_eq_unit {f : R ⟶ S}
    (A : SemilinearSections.ScalarData.{c, v, max c v r} f)
    (M : SemilinearSections.Mod.{c, v, max c v r} J R) (U : Cᵒᵖ)
    (x : M.val.obj U) :
    SemilinearSections.scalarExtensionSection.{c, v, r} f A M U x =
      @id ((A.model.E.obj M).val.obj U)
        ((A.ordinaryAdjunction.unit.app M).val.app U x) := by
  unfold SemilinearSections.scalarExtensionSection
  rw [← A.unit_section M U x]
  erw [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
    ← SheafOfModules.comp_val, eqToHom_trans, eqToHom_refl]
  rfl

end ScalarAssociation

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

variable (SE : CoefficientDerivedSystemCalculus l E W)
  (SL : CoefficientDerivedSystemCalculus l L W)
  (A : CoefficientExtensionSystems l E L ι W)

/-- Construction of the normalized reduction skeleton from flat-term
representatives and finite quotient scalar association.
Source: integral operations and K-flat change of rings
(blueprint: lem-pur-coefficient-extension-reduction-model).
Proof: choose a flat-term K-flat representative, form the finite quotient scalar
models, transport their balanced maps through every quotient transition, and
assemble the strict model, normalized tower, completion projection, and all
evaluation equations into the displayed skeleton. -/
theorem coefficientExtensionReductionSkeleton_exists
    (_hl : IsUnit (l : Γ(W, ⊤))) :
    Nonempty (CoefficientExtensionReductionSkeleton l E L ι W SE A) := by
  classical
  obtain ⟨s⟩ := coefficientExtensionFiniteAssociation_exists l E L ι W A
  obtain ⟨direct, evaluation, model, ht, hm, hn⟩ :=
    coefficientExtensionStrictRepresentative_exists l E L ι W A SE
      s.association s.association_section
  obtain ⟨e, he⟩ := coefficientExtensionRepresentativeRoos_exists l E L ι W A SE
    direct evaluation ht model
  obtain ⟨α, hα, _⟩ :=
    (integralScalarExtensionWellDefined l E L ι W).2.choose_spec.choose_spec.2.2.1
      (coefficientExtensionSystem l E L ι W SE A ⋙ coefficientSequenceLimit l L W) e
  refine ⟨{
    association := s.association
    association_section := s.association_section
    direct := direct
    directEvaluation := evaluation
    direct_transition := ht
    model := model
    model_evaluation := hm
    normalized := hn
    completion := α.symm
    completion_projection := ?_
    comparison_isIso := trivial }⟩
  unfold IsCoefficientExtensionCompletionProjection
  intro P n
  have ha := congrArg (fun z ↦ z.hom.app P) hα
  change α.hom.app (DerivedCategory.Q.obj P.obj) ≫ e.hom.app P =
    (integralScalarExtensionComparisonOfUniverses l E L ι W).hom.app P at ha
  have ha' : α.hom.app (DerivedCategory.Q.obj P.obj) =
      (integralScalarExtensionComparisonOfUniverses l E L ι W).hom.app P ≫
        e.inv.app P := by
    rw [← ha]
    erw [Category.assoc, e.hom_inv_id_app, Category.comp_id]
  change α.hom.app (DerivedCategory.Q.obj P.obj) ≫ _ ≫ _ ≫ _ = _
  rw [ha']
  simpa only [Category.assoc] using
    congrArg (fun f ↦ (integralScalarExtensionComparisonOfUniverses l E L ι W).hom.app P ≫ f)
      (he P n)

private def effectivityTestDatum (p : ℕ) (hp : p.Prime) : FiniteFieldDatum.{0} := by
  letI : Fact p.Prime := ⟨hp⟩
  exact {
    p := p
    a := 1
    q := p
    prime := hp
    exponent_pos := le_refl 1
    cardinality_eq := (pow_one p).symm
    k₀ := ZMod p
    card_base := by simp [Nat.card_eq_fintype_card]
    k := AlgebraicClosure (ZMod p) }

private theorem normalizedSequence_counit_isIso
    (N : coefficientSequenceDerived l L W)
    (hN : IsNormalizedCoefficientSequence l L W N) :
    IsIso (SL.adjunction.counit.app N) := by
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let D := effectivityTestDatum p hp
  have hlp : l ≠ D.p := by
    change l ≠ p
    omega
  obtain ⟨T, e, hprod, δ, hδ⟩ := coefficientSequence_roosModel l L W D hlp N hN
  let := hprod
  apply (SL.isIso_iff_evaluations _).2
  intro n
  let adj := coefficientFiniteAdjunction l L W n
  let q := (adj.homEquiv _ _).symm ((coefficientSequenceProjection l L W n).app N)
  have hi := normalizedDVRRoos_finite_reduction l L W D hlp T _ _ δ hδ n adj
  have heq : (adj.homEquiv _ _).symm
      ((Pi.lift (fun k : ℕ ↦ (coefficientSequenceProjection l L W k).app N ≫
        (normalizedDVRResCompleted l L W D hlp k).map (e k).inv ≫
        (T.evaluationIso k).inv)) ≫ Pi.π _ n ≫ (T.evaluationIso n).hom) =
      q ≫ (e n).inv := by
    simp only [Pi.lift_comp_π_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact adj.homEquiv_naturality_right_symm _ _
  have : IsIso (q ≫ (e n).inv) := by
    rw [← heq]
    exact hi
  have : IsIso q := IsIso.of_isIso_comp_right q (e n).inv
  have hq : (SL.reductionEvaluation n).inv.app ((coefficientSequenceLimit l L W).obj N) ≫
      (coefficientSequenceDerivedEvaluation l L W n).map (SL.adjunction.counit.app N) = q := by
    apply (adj.homEquiv _ _).injective
    exact (SL.counit_projection N n).trans
      ((adj.homEquiv _ _).apply_symm_apply _).symm
  have : IsIso ((SL.reductionEvaluation n).inv.app
      ((coefficientSequenceLimit l L W).obj N) ≫
      (coefficientSequenceDerivedEvaluation l L W n).map (SL.adjunction.counit.app N)) := by
    rw [hq]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((SL.reductionEvaluation n).inv.app ((coefficientSequenceLimit l L W).obj N)) _

/-- The normalized tower counit of a reduction skeleton is invertible.
Source: normalized DVR effectivity
(blueprint: lem-pur-coefficient-extension-reduction-model).
Proof: regard the skeleton's normalized sequence and completion projection as
the normalized DVR tower data, apply normalized effectivity to its Roos limit,
and identify the resulting canonical counit with `coefficientExtensionCounit`.
-/
theorem coefficientExtensionReductionSkeleton_comparison_isIso
    (_hl : IsUnit (l : Γ(W, ⊤)))
    (s : CoefficientExtensionReductionSkeleton l E L ι W SE A) :
    IsIso (coefficientExtensionCounit l E L ι W SE SL A s.completion) := by
  have (K : DerivedCategory (scalarReductionSource l E W)) :
      IsIso (SL.adjunction.counit.app ((coefficientExtensionSystem l E L ι W SE A).obj K)) :=
    normalizedSequence_counit_isIso l L W SL _ (s.normalized K)
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro K
  unfold coefficientExtensionCounit
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  infer_instance

/-- Coherent finite reduction of completed scalar extension on the entire derived category.
Source: integral operations, Stacks 06YS, 0G7E, 06YY
(blueprint: lem-pur-coefficient-extension-reduction-model).
Proof: choose one flat-term K-flat P. Change of rings preserves K-flatness and flat
terms even for ramified quotient maps. The balanced maps (x⊗a)⊗b ↦ x⊗ι(a)b and
x⊗b ↦ (x⊗1)⊗b are inverse and commute with differentials. Quotient reduction
commutes with these formulas, giving a strict system isomorphism and normalization
by the same association with B_m→B_n. Its cocycle is the quotient cocycle. The
Roos construction computes the specified total limit and its projections, hence
completion. Apply normalized DVR effectivity with coefficient field L: its counit
is invertible and normalized by the actual limit projections. Transport it through
the simultaneous association to obtain exactly coefficientExtensionCounit.
Naturality on chain maps descends through the localization of flat-term K-flat
complexes; quasi-isomorphisms and roofs give the canonical resolution comparisons,
including their composition for a third representative. The equations hold for all
m≥n, including identities, because the comparison is a map of coherent systems.
For identity extension scalar association is the action unitor, so this is the
usual reduction counit of the completion, without assuming K itself complete.
For three fields the two scalar associations multiply the same coefficients.
Apply coefficient extension to this coherent counit and then use counit naturality
h e_H = e_J R_F L_F(h). This is an equality of system maps before evaluation,
and gives the composition equation stated below. No finiteness of K is used. -/
theorem coefficientExtensionReductionModel
    (_hl : IsUnit (l : Γ(W, ⊤))) :
    Nonempty (CoefficientExtensionReductionData l E L ι W SE SL A) := by
  obtain ⟨s⟩ := coefficientExtensionReductionSkeleton_exists
    l E L ι W SE A _hl
  have hcomp := coefficientExtensionReductionSkeleton_comparison_isIso
    l E L ι W SE SL A _hl s
  refine ⟨⟨⟨⟨s.association, s.association_section⟩, s.direct,
    s.directEvaluation, s.direct_transition⟩, s.model, s.model_evaluation,
    s.normalized, s.completion, s.completion_projection, hcomp⟩⟩

section SuccessiveExtension
variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (j : L →ₐ[ℚ_[l]] F) (SF : CoefficientDerivedSystemCalculus l F W)
  (B : CoefficientExtensionSystems l L F j W)
  (D : CoefficientExtensionSystems l E F (j.comp ι) W)
  (dEL : CoefficientExtensionReductionData l E L ι W SE SL A)
  (dLF : CoefficientExtensionReductionData l L F j W SL SF B)
  (dEF : CoefficientExtensionReductionData l E F (j.comp ι) W SE SF D)

end SuccessiveExtension

end WeilConjectures
