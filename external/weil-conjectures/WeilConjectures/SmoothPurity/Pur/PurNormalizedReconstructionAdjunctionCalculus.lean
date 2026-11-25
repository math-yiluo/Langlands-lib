/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import all WeilConjectures.SmoothPurity.Normalized.NormalizedDVREffectivity
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientSequenceRoosModel
import WeilConjectures.SmoothPurity.Coefficient.CoefficientConstantTowerRoos
import all WeilConjectures.SixFunctors.Normalized.NormalizedDVRKFlatReductionModel
import WeilConjectures.SixFunctors.Normalized.NormalizedDVRKFlatTransition
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import WeilConjectures.CategoryTheory.AdjointEquivalenceConjugation.AdjointEquivalenceConjugation

/-!
# Normalized reconstruction and its adjunction calculus

Source: current Weil blueprint, chap-Smooth-purity,
prop-pur-adic-reconstruction-trace-coherence, sole proof paragraph
(blueprint: lem-pur-normalized-reconstruction-adjunction-calculus).

All categories are unbounded. The system category, reduction, total limit and their
unit/counit are the recorded evaluation calculus, with its actual projection normalization.
The property Q selects any replete full subcategory; Q = top gives the entire normalized
category. No cohomological, constructibility or Tor-amplitude restriction is imposed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u tX tY tZ v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
namespace WeilConjectures
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence unrestrictedIntegralReductionExistence
  normalizedDVRResCompletedComp normalizedDVRKFlatComparison
attribute [local instance 4000] normalizedDVRKFlatReductionModelLocal1
attribute [local instance] normalizedDVRKFlatReductionModelLocal2
  normalizedDVRKFlatReductionModelLocal3

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

private theorem reconstructionProjectionTransition
    (D : FiniteFieldDatum.{0}) (hlp : l ≠ D.p)
    (N : coefficientSequenceDerived l E W) (n : ℕ) :
    (coefficientSequenceProjection l E W (n + 1)).app N ≫
      (normalizedDVRResCompleted l E W D hlp (n + 1)).map
        ((coefficientSequenceDerivedTransition l E W n.le_succ).app N) ≫
      (normalizedDVRResCompletedComp l E W D hlp n.le_succ).hom.app
        ((coefficientSequenceDerivedEvaluation l E W n).obj N) =
      (coefficientSequenceProjection l E W n).app N := by
  obtain ⟨hp, δ, hδ⟩ := coefficientConstantTower_roos l E W D hlp
    ((coefficientSequenceDerivedRestriction l E W).obj N)
  let := hp
  have h := adjacentRoosProjection _ _ _ δ hδ n
  simp only [Pi.lift_comp_π_assoc, Pi.lift_comp_π] at h
  change ((coefficientConstantTowerProjection l E W (n + 1)).app _ ≫
    (coefficientRestrictedEvaluationIso l E W (n + 1)).hom.app N) ≫ _ ≫ _ =
    (coefficientConstantTowerProjection l E W n).app _ ≫
      (coefficientRestrictedEvaluationIso l E W n).hom.app N
  rw [Category.assoc, ← derivedRestrictedTransition l E W D hlp N n.le_succ]
  rw [← Category.assoc, h]

private theorem reconstructionFiniteTransition
    (D : FiniteFieldDatum.{0}) (hlp : l ≠ D.p)
    (S : CoefficientDerivedSystemCalculus l E W)
    (K : DerivedCategory (scalarReductionSource l E W)) (n : ℕ) :
    (S.reductionEvaluation (n + 1)).inv.app K ≫
      (coefficientSequenceDerivedTransition l E W n.le_succ).app (S.reduction.obj K) =
      normalizedDVRReductionTransition l E W D hlp n.le_succ K ≫
        (normalizedDVRRes l E W n.le_succ).map ((S.reductionEvaluation n).inv.app K) := by
  have h := adjointTransition (coefficientFiniteAdjunction l E W (n + 1))
    (coefficientFiniteAdjunction l E W n) (normalizedDVRRes l E W n.le_succ)
    (normalizedDVRResCompletedComp l E W D hlp n.le_succ)
    (S.adjunction.unit.app K ≫
      (coefficientSequenceProjection l E W (n + 1)).app (S.reduction.obj K))
    (S.adjunction.unit.app K ≫
      (coefficientSequenceProjection l E W n).app (S.reduction.obj K))
    ((coefficientSequenceDerivedTransition l E W n.le_succ).app (S.reduction.obj K)) (by
      have ht := reconstructionProjectionTransition l E W D hlp (S.reduction.obj K) n
      change (coefficientSequenceProjection l E W (n + 1)).app (S.reduction.obj K) ≫
        (coefficientFiniteDerivedRestriction l E W (n + 1)).map
          ((coefficientSequenceDerivedTransition l E W n.le_succ).app
            (S.reduction.obj K)) ≫
        (normalizedDVRResCompletedComp l E W D hlp n.le_succ).hom.app _ = _ at ht
      simpa only [Category.assoc] using congrArg
        (fun f ↦ S.adjunction.unit.app K ≫ f) ht)
  have ha (j : ℕ) : ((coefficientFiniteAdjunction l E W j).homEquiv _ _).symm
      (S.adjunction.unit.app K ≫
        (coefficientSequenceProjection l E W j).app (S.reduction.obj K)) =
      (S.reductionEvaluation j).inv.app K := by
    apply ((coefficientFiniteAdjunction l E W j).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    exact S.unit_projection K j
  rw [ha, ha] at h
  exact h

/-- Normalized reconstruction over any scheme, using the actual reduction adjunction.
Source: the normalized DVR/Roos reconstruction argument in the sole proof paragraph of
prop-pur-adic-reconstruction-trace-coherence
(blueprint: lem-pod-unrestricted-normalized-reconstruction).

Proof: realize the normalized evaluated tower by its two-coordinate Roos triangle.
DVR effectivity makes its total limit complete and its finite counit maps invertible;
conservativity of evaluations inverts the actual system counit. For a complete object,
compare its K-flat quotient tower with the reduction tower, retaining each transition.
Transport its Roos triangle and use uniqueness of derived limits. The adjunction triangle
then makes its actual unit invertible. The argument is independent of the characteristic
of the scheme: the auxiliary finite field datum only requires a prime different from l. -/
theorem purNormalizedReconstructionOfScheme
    (S : CoefficientDerivedSystemCalculus l E W) :
    (∀ (N : coefficientSequenceDerived l E W), IsNormalizedCoefficientSequence l E W N →
      IntegralOnSlice.IsComplete l E W none ((coefficientSequenceLimit l E W).obj N) ∧
        IsIso (S.adjunction.counit.app N)) ∧
    (∀ (K : DerivedCategory (scalarReductionSource l E W)),
      IntegralOnSlice.IsComplete l E W none K → IsIso (S.adjunction.unit.app K)) := by
  have hc (N : coefficientSequenceDerived l E W)
      (hN : IsNormalizedCoefficientSequence l E W N) :
      IntegralOnSlice.IsComplete l E W none ((coefficientSequenceLimit l E W).obj N) ∧
        IsIso (S.adjunction.counit.app N) := by
    obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
    let : Fact p.Prime := ⟨hp⟩
    let D : FiniteFieldDatum.{0} := {
      p := p, a := 1, q := p, prime := hp, exponent_pos := le_refl 1,
      cardinality_eq := (pow_one p).symm, k₀ := ZMod p,
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
    have hlp : l ≠ D.p := by change l ≠ p; omega
    obtain ⟨T, e, hprod, δ, hδ⟩ := coefficientSequence_roosModel l E W D hlp N hN
    let := hprod
    have heff := normalizedDVRTower_effectivity l E W D hlp T _ _ δ hδ
    refine ⟨⟨D, hlp, heff.2.2⟩, ?_⟩
    apply (S.isIso_iff_evaluations _).2
    intro n
    let adj := coefficientFiniteAdjunction l E W n
    let q := (adj.homEquiv _ _).symm ((coefficientSequenceProjection l E W n).app N)
    have hi := normalizedDVRRoos_finite_reduction l E W D hlp T _ _ δ hδ n adj
    have heq : (adj.homEquiv _ _).symm
        ((Pi.lift (fun k : ℕ ↦ (coefficientSequenceProjection l E W k).app N ≫
          (normalizedDVRResCompleted l E W D hlp k).map (e k).inv ≫
          (T.evaluationIso k).inv)) ≫ Pi.π _ n ≫ (T.evaluationIso n).hom) =
        q ≫ (e n).inv := by
      simp only [Pi.lift_comp_π_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact adj.homEquiv_naturality_right_symm _ _
    have : IsIso (q ≫ (e n).inv) := by rw [← heq]; exact hi
    have : IsIso q := IsIso.of_isIso_comp_right q (e n).inv
    have hq : (S.reductionEvaluation n).inv.app ((coefficientSequenceLimit l E W).obj N) ≫
        (coefficientSequenceDerivedEvaluation l E W n).map (S.adjunction.counit.app N) =
        q := by
      apply (adj.homEquiv _ _).injective
      exact (S.counit_projection N n).trans
        ((adj.homEquiv _ _).apply_symm_apply _).symm
    have : IsIso ((S.reductionEvaluation n).inv.app
        ((coefficientSequenceLimit l E W).obj N) ≫
        (coefficientSequenceDerivedEvaluation l E W n).map (S.adjunction.counit.app N)) := by
      rw [hq]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((S.reductionEvaluation n).inv.app ((coefficientSequenceLimit l E W).obj N)) _
  refine ⟨hc, ?_⟩
  intro K hK
  obtain ⟨D, hlp, P, G, q, hq, eG, hp, δ, hδ⟩ := hK
  let := hp
  have : QuasiIso q := hq.1
  let e : (DerivedCategory.Q.obj P : DerivedCategory (scalarReductionSource l E W)) ≅ K :=
    asIso (DerivedCategory.Q.map q) ≪≫ eG
  let N := S.reduction.obj K
  let X := (coefficientSequenceDerivedRestriction l E W).obj N
  obtain ⟨hpX, δX, hδX⟩ := coefficientConstantTower_roos l E W D hlp X
  let := hpX
  have hi (n : ℕ) : IsIso (normalizedDVRKFlatComparison l E W n P) :=
    representativeComparison_isIso l E W n P hq.2
  let a (n : ℕ) :=
    (scalarReductionDerivedRestriction l E W n).mapIso
        ((scalarReductionDerivedExtension l E W n).mapIso e.symm) ≪≫
      @asIso _ _ _ _ (normalizedDVRKFlatComparison l E W n P) (hi n)
  let b (n : ℕ) := (coefficientRestrictedEvaluationIso l E W n).app N ≪≫
    (scalarReductionDerivedRestriction l E W n).mapIso ((S.reductionEvaluation n).app K)
  let d (n : ℕ) := b n ≪≫ a n
  have ht (n : ℕ) : (normalizedDVRTowerTransition l E W D hlp n.le_succ).app X ≫
      (d n).hom = (d (n + 1)).hom ≫
        (integralReductionTower l E W D hlp P).map (homOfLE n.le_succ).op := by
    have hs := restrictionIsoSquare
      (scalarReductionDerivedRestriction l E W (n + 1))
      (scalarReductionDerivedRestriction l E W n) (normalizedDVRRes l E W n.le_succ)
      (normalizedDVRResCompletedComp l E W D hlp n.le_succ)
      ((S.reductionEvaluation (n + 1)).app K).symm
      ((S.reductionEvaluation n).app K).symm
      ((coefficientSequenceDerivedTransition l E W n.le_succ).app N)
      (normalizedDVRReductionTransition l E W D hlp n.le_succ K)
      (reconstructionFiniteTransition l E W D hlp S K n)
    have hk := normalizedDVR_kflat_transition l E W D hlp P hq.2 K e n
      (normalizedDVRIntegralAdjunction l E W (n + 1))
      (normalizedDVRIntegralAdjunction l E W n)
      (normalizedDVRKFlatUnit l E W D hlp (n + 1) P hq.2)
      (normalizedDVRKFlatUnit l E W D hlp n P hq.2)
    dsimp only [d, b, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
    simp only [Category.assoc]
    rw [← Category.assoc, derivedRestrictedTransition l E W D hlp N n.le_succ]
    simp only [Category.assoc]
    dsimp only [Functor.mapIso_inv, Iso.symm_inv, Iso.app_hom] at hs
    have hsr :
        (normalizedDVRResCompleted l E W D hlp (n + 1)).map
            ((coefficientSequenceDerivedTransition l E W n.le_succ).app N) ≫
          (normalizedDVRResCompletedComp l E W D hlp n.le_succ).hom.app
            ((coefficientSequenceDerivedEvaluation l E W n).obj N) ≫
          (scalarReductionDerivedRestriction l E W n).map
            ((S.reductionEvaluation n).hom.app K) =
        (scalarReductionDerivedRestriction l E W (n + 1)).map
            ((S.reductionEvaluation (n + 1)).hom.app K) ≫
          (scalarReductionDerivedRestriction l E W (n + 1)).map
            (normalizedDVRReductionTransition l E W D hlp n.le_succ K) ≫
          (normalizedDVRResCompletedComp l E W D hlp n.le_succ).hom.app
            ((scalarReductionDerivedExtension l E W n).obj K) := hs
    rw [reassoc_of% hsr]
    dsimp only [a, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_hom]
    simpa only [integralReductionTower, Functor.ofOpSequence_map_homOfLE_succ,
      normalizedDVRReductionTransition, X, N, normalizedDVRTowerEvaluation,
      coefficientConstantTowerEvaluation, Category.assoc] using congrArg
      (fun f ↦ (coefficientRestrictedEvaluationIso l E W (n + 1)).hom.app N ≫
        (scalarReductionDerivedRestriction l E W (n + 1)).map
          ((S.reductionEvaluation (n + 1)).hom.app K) ≫ f) hk
  obtain ⟨hpP, δP, hδP⟩ := roosTransport
    (fun n ↦ (normalizedDVRTowerTransition l E W D hlp n.le_succ).app X)
    (fun n ↦ (integralReductionTower l E W D hlp P).map (homOfLE n.le_succ).op)
    ((coefficientSequenceLimit l E W).obj N) _ δX hδX d
    (fun n ↦ (coefficientConstantTowerProjection l E W n).app X ≫ (d n).hom) ht
    (fun n ↦ by simp only [Pi.lift_comp_π_assoc])
  let := hpP
  obtain ⟨φ⟩ := (exists_isDerivedLimit_and_iso
    (fun n ↦ (integralReductionTower l E W D hlp P).obj (Opposite.op n))
    (fun n ↦ (integralReductionTower l E W D hlp P).map (homOfLE n.le_succ).op)).2
    K ((coefficientSequenceLimit l E W).obj N) ⟨_, δ, hδ⟩ ⟨_, δP, hδP⟩
  have : IsIso (S.adjunction.counit.app N) := (hc N (S.reduction_normalized K)).2
  have : IsIso (S.adjunction.unit.app ((coefficientSequenceLimit l E W).obj N) ≫
      (coefficientSequenceLimit l E W).map (S.adjunction.counit.app N)) := by
    rw [S.adjunction.right_triangle_components]
    exact CategoryTheory.IsIso.id _
  have : IsIso (S.adjunction.unit.app ((coefficientSequenceLimit l E W).obj N)) :=
    IsIso.of_isIso_comp_right _ ((coefficientSequenceLimit l E W).map
      (S.adjunction.counit.app N))
  have : IsIso (S.adjunction.unit.app K ≫
      (S.reduction ⋙ coefficientSequenceLimit l E W).map φ.hom) := by
    rw [← S.adjunction.unit.naturality φ.hom]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((S.reduction ⋙ coefficientSequenceLimit l E W).map φ.hom)

/-- Reconstruction uses the actual evaluation-calculus adjunction.
Source: the sole proof paragraph of prop-pur-adic-reconstruction-trace-coherence
(blueprint: lem-pur-normalized-reconstruction-adjunction-calculus).
Proof: (1) K-flat scalar extension shows reduction is normalized, as recorded in S.
(2) Apply lemma-sp-tower-adjunction-foundation--2 to the evaluated normalized tower.
The resulting scalar-extension comparisons are precisely S.counit_projection;
joint conservativity of derived evaluation makes the actual counit invertible.
The same effectivity theorem gives completeness of its total limit.
(3) The triangle identity makes reduction of the unit invertible. Its first evaluation
is reduction modulo the uniformizer, by S.unit_projection. Apply
lemma-reduction-derived-nakayama between the complete source and complete target.
Naturality is already that of S.adjunction. No boundedness is used. -/
theorem purNormalizedReconstruction
    (_hl : IsUnit (l : Γ(W, ⊤))) (S : CoefficientDerivedSystemCalculus l E W) :
    (∀ (N : coefficientSequenceDerived l E W), IsNormalizedCoefficientSequence l E W N →
      IntegralOnSlice.IsComplete l E W none ((coefficientSequenceLimit l E W).obj N) ∧
        IsIso (S.adjunction.counit.app N)) ∧
    (∀ (K : DerivedCategory (scalarReductionSource l E W)),
      IntegralOnSlice.IsComplete l E W none K → IsIso (S.adjunction.unit.app K)) := by
  exact purNormalizedReconstructionOfScheme l E W S

variable (hl : IsUnit (l : Γ(W, ⊤))) (S : CoefficientDerivedSystemCalculus l E W)
  (Q : ObjectProperty (coefficientSequenceDerived l E W)) [Q.IsClosedUnderIsomorphisms]

namespace PurReconstruction

variable {C₁ : Type u₁} [Category.{v₁} C₁] {N₁ : Type u₂} [Category.{v₂} N₁]
  {C₂ : Type u₃} [Category.{v₃} C₂] {N₂ : Type u₄} [Category.{v₄} N₂]
  {C₃ : Type u₅} [Category.{v₅} C₃] {N₃ : Type u₆} [Category.{v₆} N₃]

/-- Realization L_Y F R_X. Source: the same proof paragraph
(blueprint: lem-pur-normalized-reconstruction-adjunction-calculus). -/
def realized (eX : C₁ ≌ N₁) (eY : C₂ ≌ N₂) (F : N₁ ⥤ N₂) : C₁ ⥤ C₂ :=
  eX.functor ⋙ F ⋙ eY.inverse

/-- The transported adjunction is the composite of the three specified adjunctions.
Source: the same proof paragraph
(blueprint: lem-pur-normalized-reconstruction-adjunction-calculus). -/
def realizedAdjunction (eX : C₁ ≌ N₁) (eY : C₂ ≌ N₂)
    {F : N₁ ⥤ N₂} {G : N₂ ⥤ N₁} (adj : F ⊣ G) :
    realized eX eY F ⊣ realized eY eX G :=
  (eX.toAdjunction.comp adj).comp eY.symm.toAdjunction

/-- The natural identification Fbar L_X = L_Y F, induced by the actual system counit.
Source: the same proof paragraph
(blueprint: lem-pur-normalized-reconstruction-adjunction-calculus). -/
def realizationComparison (eX : C₁ ≌ N₁) (eY : C₂ ≌ N₂) (F : N₁ ⥤ N₂) :
    eX.inverse ⋙ realized eX eY F ≅ F ⋙ eY.inverse :=
  isoWhiskerRight eX.counitIso (F ⋙ eY.inverse) ≪≫ Functor.leftUnitor _

/-- Realization of a transformation, by functorial whiskering.
Source: the same proof paragraph
(blueprint: lem-pur-normalized-reconstruction-adjunction-calculus). -/
def realizedTransformation (eX : C₁ ≌ N₁) (eY : C₂ ≌ N₂)
    {F F' : N₁ ⥤ N₂} (α : F ⟶ F') : realized eX eY F ⟶ realized eX eY F' :=
  Functor.whiskerLeft eX.functor (Functor.whiskerRight α eY.inverse)

/-- The natural composition comparison inserts e_Y between R_Y and L_Y.
Source: the same proof paragraph
(blueprint: lem-pur-normalized-reconstruction-adjunction-calculus). -/
def compositionComparison (eX : C₁ ≌ N₁) (eY : C₂ ≌ N₂) (eZ : C₃ ≌ N₃)
    (F : N₁ ⥤ N₂) (H : N₂ ⥤ N₃) :
    realized eX eY F ⋙ realized eY eZ H ≅ realized eX eZ (F ⋙ H) :=
  isoWhiskerLeft (eX.functor ⋙ F)
    (isoWhiskerRight eY.counitIso (H ⋙ eZ.inverse) ≪≫ Functor.leftUnitor _)

/-- The explicit transported counit, transpose and composition formulas.
These are propositions about the preceding constructions, with no extra choice of maps.
Source: the same proof paragraph
(blueprint: lem-pur-normalized-reconstruction-adjunction-calculus). -/
structure Calculus (eX : C₁ ≌ N₁) (eY : C₂ ≌ N₂) (eZ : C₃ ≌ N₃) : Prop where
  /-- The counit is u inverse after L epsilon after L F(e). -/
  counit : ∀ (F : N₁ ⥤ N₂) (G : N₂ ⥤ N₁) (adj : F ⊣ G) (K : C₂),
    (realizedAdjunction eX eY adj).counit.app K =
      eY.inverse.map (F.map (eX.counit.app (G.obj (eY.functor.obj K)))) ≫
        eY.inverse.map (adj.counit.app (eY.functor.obj K)) ≫ eY.unitInv.app K
  /-- After the e-induced identifications, the transpose is L(epsilon after F(a)). -/
  transpose : ∀ (F : N₁ ⥤ N₂) (G : N₂ ⥤ N₁) (adj : F ⊣ G)
    (P : N₁) (N : N₂) (a : P ⟶ G.obj N),
    ((realizedAdjunction eX eY adj).homEquiv _ _).symm
        (eX.inverse.map a ≫ (realizationComparison eY eX G).inv.app N) =
      (realizationComparison eX eY F).hom.app P ≫
        eY.inverse.map (F.map a ≫ adj.counit.app N)
  /-- The composition comparison has the specified component L_Z H(e_Y). -/
  composition : ∀ (F : N₁ ⥤ N₂) (H : N₂ ⥤ N₃) (K : C₁),
    (compositionComparison eX eY eZ F H).hom.app K =
      eZ.inverse.map (H.map (eY.counit.app (F.obj (eX.functor.obj K))))
  /-- The composition comparisons commute with transformations in both functors. -/
  transformation : ∀ (F F' : N₁ ⥤ N₂) (H H' : N₂ ⥤ N₃) (α : F ⟶ F') (β : H ⟶ H'),
    Functor.whiskerRight (realizedTransformation eX eY α) (realized eY eZ H) ≫
        Functor.whiskerLeft (realized eX eY F') (realizedTransformation eY eZ β) ≫
        (compositionComparison eX eY eZ F' H').hom =
      (compositionComparison eX eY eZ F H).hom ≫
        realizedTransformation eX eZ (Functor.whiskerRight α H ≫ Functor.whiskerLeft F' β)

private theorem calculus (eX : C₁ ≌ N₁) (eY : C₂ ≌ N₂) (eZ : C₃ ≌ N₃) :
    Calculus eX eY eZ := by
  constructor
  · intro F G adj K
    simp [realizedAdjunction, Functor.map_comp, Category.assoc]
  · intro F G adj P N a
    simpa [realized, realizedAdjunction, realizationComparison, Equivalence.invFunIdAssoc,
      Functor.map_comp, Category.assoc] using
      AdjointEquivalenceConjugation.conjugation_transpose eX eY adj P N a
  · intro F H K
    simp [compositionComparison]
  · intro F F' H H' α β
    ext K
    simp only [realizedTransformation, compositionComparison, realized,
      NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, Functor.comp_map,
      Functor.comp_obj, isoWhiskerLeft_hom, isoWhiskerRight_hom, Iso.trans_hom,
      Functor.leftUnitor_hom_app]
    dsimp only [Functor.id_obj, NatTrans.id_app]
    simp only [Category.comp_id, ← CategoryTheory.Functor.map_comp]
    apply congrArg eZ.inverse.map
    rw [← β.naturality, ← H.map_comp_assoc]
    have hn := eY.counit.naturality (α.app (eX.functor.obj K))
    dsimp only [Functor.id_map, Functor.comp_map] at hn
    dsimp only [Equivalence.counit] at hn
    rw [hn, H.map_comp, Category.assoc]

end PurReconstruction

end WeilConjectures
