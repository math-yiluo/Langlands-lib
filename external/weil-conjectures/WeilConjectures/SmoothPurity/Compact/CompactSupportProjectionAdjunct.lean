/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralRationalQbarCompactSupport
import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeNormalization
import WeilConjectures.SmoothPurity.Compact.CompactSupportRoosTriangleTransport
import WeilConjectures.SmoothPurity.Compact.CompactSupportRoosTriangleUniqueness
import all WeilConjectures.SixFunctors.Compact.CompactSupportReductionTower
import all WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientTransition
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientSequenceRoosModel
import WeilConjectures.SixFunctors.Normalized.NormalizedDVRRoosFiniteReduction
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Data.ZMod.Basic

/-! # Invertibility of the compact-support projection adjunct

The complete projection-adjunct proof is exposed independently of the chosen
integral functor predicate, so that its elaboration does not expand that predicate.
(blueprint: lem-weil-compact-support-projection-adjunct-is-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.proofsInPublic true

set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open TensorProduct Opposite
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients

attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  completedIntegralCoefficientSheafUnrestricted scalarReductionExistence
  scalarReductionDerivedExistence unrestrictedIntegralReductionExistence
  coefficientSequenceEvaluation coefficientSequenceTransition constantSheaf
  sfIntegralCompactSupportValue
  Padic.coefficientExtensionIdeal compactSupportOrdinaryCoefficientTransition

open CategoryTheory.Pretriangulated in
private theorem roos_unique
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {T : ℕ → C} [HasProduct T] (t : ∀ n, T (n + 1) ⟶ T n)
    {M N : C} (p : M ⟶ ∏ᶜ T) (q : N ⟶ ∏ᶜ T)
    (δ : ∏ᶜ T ⟶ M⟦(1 : ℤ)⟧) (ε : ∏ᶜ T ⟶ N⟦(1 : ℤ)⟧)
    (hp : IsDerivedLimitTriangle t M p δ) (hq : IsDerivedLimitTriangle t N q ε) :
    ∃ e : M ≅ N, e.hom ≫ q = p := by
  exact compactSupportRoosTriangleUniqueness t p q δ ε hp hq

open CategoryTheory.Pretriangulated in
private theorem roos_transport {C : Type*} [Category C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] {X Y : ℕ → C}
    (f : ∀ n, X (n + 1) ⟶ X n) (g : ∀ n, Y (n + 1) ⟶ Y n)
    {K L : C} (e : K ≅ L) (a : ∀ n, X n ≅ Y n)
    (p : ∀ n, K ⟶ X n) (q : ∀ n, L ⟶ Y n)
    (ht : ∀ n, f n ≫ (a n).hom = (a (n + 1)).hom ≫ g n)
    (hp : ∀ n, p n ≫ (a n).hom = e.hom ≫ q n)
    (h : ∃ hprod : HasProduct X, letI := hprod
      ∃ δ : (∏ᶜ X) ⟶ K⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle f K (Pi.lift p) δ) :
    ∃ hprod : HasProduct Y, letI := hprod
      ∃ δ : (∏ᶜ Y) ⟶ L⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle g L (Pi.lift q) δ := by
  exact compactSupportRoosTriangleTransport f g e a p q ht hp h

section Adjacent
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem adjacentRestrictionComp (W : Scheme.{u}) (j : ℕ) :
    compactSupportRestrictionComp l E W (j + 1) j j.le_succ =
      sfCompactSupportDerivedRestrictionComp l E W j := by
  rfl

private theorem adjacentReductionMap (W : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource.{u, u} l E W)) (j : ℕ) :
    compactSupportReductionMap l E W (j + 1) j j.le_succ K =
      sfCompactSupportReductionTransition l E W K j := by
  rfl

private theorem adjacentQuotient (j : ℕ) :
    compactSupportLevelQuotient l E (j + 1) j j.le_succ =
      Padic.coefficientExtensionTransition l E (j + 1) := by
  rfl

end Adjacent

section FiniteAction
variable (l : ℕ) [Fact l.Prime]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

private theorem constantTowerTransition_eq
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (W : Scheme.{u})
    (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p) {m n : ℕ} (h : n ≤ m) :
    normalizedDVRTowerTransition l E W D hl h =
      pbcTowerTransition W (completedIntegralCommRingSheafUnrestricted l E W) m n h := by
  rfl

include K₀ hl in
/-- The tensor/restriction adjunct of a specified Roos projection is invertible.
Source: blueprint lem-fix-operation-reduction.proof.md, compact-support paragraph;
Bhatt--Scholze Definition 6.7.6.
(blueprint: lem-weil-compact-support-projection-adjunct-is-iso).
Proof: normalize the native output system using the finite scalar comparison and
quotient cocycle. The normalized coefficient-sequence Roos model and finite-reduction
theorem make its projection adjunct invertible. Transport its Roos triangle to the
specified compact-support terms using the evaluation isomorphisms. A comparison
with the chosen defining Roos triangle preserves the product projection. Adjunction
naturality identifies the required adjunct with this vertex isomorphism followed
by the native projection adjunct and the finite evaluation isomorphism. -/
theorem compactSupportProjectionAdjunct_isIso
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    [HasCountableProducts (DerivedCategory (scalarReductionSource.{u, u} l E Y))]
    (K : sfIntegralConstructibleCategory l E X) (n : ℕ)
    (M : DerivedCategory (scalarReductionSource.{u, u} l E Y))
    (pM : M ⟶ ∏ᶜ (sfCompactSupportTerm l E c K.obj))
    (dM : (∏ᶜ (sfCompactSupportTerm l E c K.obj)) ⟶ M⟦(1 : ℤ)⟧)
    (hM : IsDerivedLimitTriangle (sfCompactSupportTransition l E c K.obj) M pM dM) :
    IsIso (((derivedScalarExtensionRestrictionAdjunction l E Y n).choose.homEquiv M
      ((sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).obj
        ((scalarReductionDerivedExtension l E X n).obj K.obj))).symm
      (pM ≫ Pi.π (sfCompactSupportTerm l E c K.obj) n)) := by
  classical
  let := integralOperationsDerivedCountableProducts l E Y
  let S := (coefficientDerivedSystemEvaluationCalculus.{u, u} l E X).choose
  let N : coefficientSequenceDerived.{u, u} l E Y :=
    (ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) c.i ⋙
    ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.g).obj (S.reduction.obj K.obj)
  have hN : IsNormalizedCoefficientSequence.{u, u} l E Y N :=
    compactSupportNativeSystem_normalized l c K₀ hl E K S
  let F (j : ℕ) := sfIntrinsicCompactSupport c
    (Padic.coefficientExtensionRing l E (j + 1))
  let e (j : ℕ) : (coefficientSequenceDerivedEvaluation.{u, u} l E Y j).obj N ≅
      (F j).obj ((scalarReductionDerivedExtension l E X j).obj K.obj) :=
    (compactSupportSystemEvaluation l E c j).app (S.reduction.obj K.obj) ≪≫
      (F j).mapIso ((S.reductionEvaluation j).app K.obj)
  let primes := Nat.exists_infinite_primes (l + 1)
  let p := primes.choose
  have hpl : l + 1 ≤ p := primes.choose_spec.1
  have hp : p.Prime := primes.choose_spec.2
  let : Fact p.Prime := ⟨hp⟩
  let D : FiniteFieldDatum.{0} := {
    p := p, a := 1, q := p, prime := hp, exponent_pos := le_refl 1,
    cardinality_eq := (pow_one p).symm, k₀ := ZMod p,
    card_base := by simp [Nat.card_eq_fintype_card]
    k := AlgebraicClosure (ZMod p) }
  have hlp : l ≠ D.p := by change l ≠ p; omega
  let adj := (derivedScalarExtensionRestrictionAdjunction l E Y n).choose
  have hq : IsIso ((adj.homEquiv _ _).symm
      ((coefficientSequenceProjection l E Y n).app N)) := by
    let model := coefficientSequence_roosModel l E Y D hlp N hN
    let T := model.choose
    let ε := model.choose_spec.choose
    let hprod := model.choose_spec.choose_spec.choose
    let := hprod
    let δ := model.choose_spec.choose_spec.choose_spec.choose
    have hδ := model.choose_spec.choose_spec.choose_spec.choose_spec
    have hi := normalizedDVRRoos_finite_reduction l E Y D hlp T _ _ δ hδ n adj
    have heq : (adj.homEquiv _ _).symm
        ((Pi.lift (fun j : ℕ ↦ (coefficientSequenceProjection l E Y j).app N ≫
          (normalizedDVRResCompleted l E Y D hlp j).map (ε j).inv ≫
          (T.evaluationIso j).inv)) ≫ Pi.π _ n ≫ (T.evaluationIso n).hom) =
        (adj.homEquiv _ _).symm ((coefficientSequenceProjection l E Y n).app N) ≫
          (ε n).inv := by
      simp only [Pi.lift_comp_π_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact adj.homEquiv_naturality_right_symm _ _
    have : IsIso ((adj.homEquiv _ _).symm
        ((coefficientSequenceProjection l E Y n).app N) ≫ (ε n).inv) := by
      rw [← heq]
      exact hi
    exact IsIso.of_isIso_comp_right _ (ε n).inv
  let := hq
  let Q := (coefficientSequenceDerivedRestriction l E Y).obj N
  let L := (coefficientSequenceLimit l E Y).obj N
  let a (j : ℕ) : (coefficientConstantTowerEvaluation l E Y j).obj Q ≅
      sfCompactSupportTerm l E c K.obj j :=
    (coefficientRestrictedEvaluationIso l E Y j).app N ≪≫
      (scalarReductionDerivedRestriction l E Y j).mapIso (e j)
  let q (j : ℕ) : L ⟶ sfCompactSupportTerm l E c K.obj j :=
    (coefficientSequenceProjection l E Y j).app N ≫
      (scalarReductionDerivedRestriction l E Y j).map (e j).hom
  have ht (j : ℕ) :
      (normalizedDVRTowerTransition l E Y D hlp j.le_succ).app Q ≫ (a j).hom =
      (a (j + 1)).hom ≫ sfCompactSupportTransition l E c K.obj j := by
    let r (W : Scheme.{u}) := (proEtaleCoefficientRestrictScalars W
      (compactSupportLevelQuotient l E (j + 1) j j.le_succ)).mapDerivedCategory
    let ε (i : ℕ) := (compactSupportSystemEvaluation l E c i).hom.app (S.reduction.obj K.obj)
    let ρ (i : ℕ) := (S.reductionEvaluation i).hom.app K.obj
    have H := compactSupportFiniteSquare (F (j + 1)) (F j) (r X) (r Y)
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E (j + 1) j j.le_succ)).hom
      _ _ _ _ _ _ _
      (compactSupportNativeSystemTransition l E c j.le_succ (S.reduction.obj K.obj))
      (compactSupportReductionTransition l E X S.toCoefficientDerivedSystemReduction
        j.le_succ K.obj)
    have H' := compactSupportCompletedSquare (r Y)
      (scalarReductionDerivedRestriction l E Y (j + 1))
      (scalarReductionDerivedRestriction l E Y j)
      (compactSupportRestrictionComp l E Y (j + 1) j j.le_succ).hom
      ((compactSupportCoefficientTransition l E Y j.le_succ).app N)
      (ε (j + 1)) (ε j) ((F (j + 1)).map (ρ (j + 1))) ((F j).map (ρ j))
      ((F (j + 1)).map (compactSupportReductionMap l E X (j + 1) j j.le_succ K.obj))
      ((sfCompactSupportRestriction c
        (compactSupportLevelQuotient l E (j + 1) j j.le_succ)).hom.app
          ((scalarReductionDerivedExtension l E X j).obj K.obj))
      ((pbcTowerTransition Y (completedIntegralCommRingSheafUnrestricted l E Y)
        (j + 1) j j.le_succ).app Q)
      ((coefficientRestrictedEvaluationIso l E Y (j + 1)).hom.app N)
      ((coefficientRestrictedEvaluationIso l E Y j).hom.app N)
      (compactSupportCoefficientTransition_restricted l E Y j.le_succ N) H
    rw [constantTowerTransition_eq l E Y D hlp j.le_succ]
    simpa only [a, e, ε, ρ, sfCompactSupportTransition, sfCompactSupportTerm,
      Nat.succ_eq_add_one, adjacentReductionMap, adjacentRestrictionComp, adjacentQuotient,
      compactSupportLevelQuotient, Padic.coefficientExtensionTransition,
      coefficientFiniteDerivedExtension, sfIntrinsicCompactSupport,
      sfAmbientCompactSupportCandidate, F,
      Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      Functor.map_comp, Category.assoc] using H'
  let roos := coefficientConstantTower_roos l E Y D hlp Q
  let hprod := roos.choose
  let := hprod
  let δ := roos.choose_spec.choose
  have hδ := roos.choose_spec.choose_spec
  let transport := roos_transport
    (fun j ↦ (normalizedDVRTowerTransition l E Y D hlp j.le_succ).app Q)
    (sfCompactSupportTransition l E c K.obj) (Iso.refl L) a
    (fun j ↦ (coefficientConstantTowerProjection l E Y j).app Q) q ht
    (fun j ↦ by simp [q, a, Q, coefficientSequenceProjection, Category.assoc])
    ⟨hprod, δ, hδ⟩
  let hprod' := transport.choose
  let := hprod'
  let δ' := transport.choose_spec.choose
  have hδ' := transport.choose_spec.choose_spec
  let comparison := roos_unique (sfCompactSupportTransition l E c K.obj)
    pM (Pi.lift q) dM δ'
    hM hδ'
  let ε := comparison.choose
  have hε := comparison.choose_spec
  have heq : (adj.homEquiv _ _).symm
      (pM ≫ Pi.π (sfCompactSupportTerm l E c K.obj) n) =
      (scalarReductionDerivedExtension l E Y n).map ε.hom ≫
        (adj.homEquiv _ _).symm ((coefficientSequenceProjection l E Y n).app N) ≫
        (e n).hom := by
    rw [← hε, Category.assoc, Pi.lift_comp_π]
    exact (adj.homEquiv_naturality_left_symm _ _).trans
      (congrArg (fun z ↦ (scalarReductionDerivedExtension l E Y n).map ε.hom ≫ z)
        (adj.homEquiv_naturality_right_symm _ _))
  change IsIso ((adj.homEquiv _ _).symm
    (pM ≫ Pi.π (sfCompactSupportTerm l E c K.obj) n))
  rw [heq]
  infer_instance

end FiniteAction
end WeilConjectures
