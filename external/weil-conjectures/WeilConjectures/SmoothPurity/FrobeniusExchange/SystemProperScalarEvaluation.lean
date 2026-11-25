/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusExchange.SystemOperationExchangeRealization
public import WeilConjectures.SmoothPurity.FrobeniusExchange.SystemScalarFiniteEvaluation
import WeilConjectures.SmoothPurity.FrobeniusExchange.SystemProperScalarEvaluationCompatibility

/-! # Evaluation of the proper scalar mate

Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 06YY, 07A6 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FrobeniusExchange
open AlgebraicGeometry.Scheme.FiniteCompactScalar
open WeilConjectures.SemilinearSections

/-- The finite scalar transpose of the specified direct-image restriction comparison.
Source: Stacks 0D6E and 07A6 (blueprint: lem-sf-system-proper-scalar-evaluation). -/
def finiteDirectScalar
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleConstantDerivedDirectImage f A ⋙ pbcDerivedExtend (scalarRingMap φ Y) ⟶
      pbcDerivedExtend (scalarRingMap φ X) ⋙ proEtaleConstantDerivedDirectImage f B :=
  ((mateEquiv (pbcDerivedScalarAdjunction (scalarRingMap φ X))
    (pbcDerivedScalarAdjunction (scalarRingMap φ Y))).symm
    (TwoSquare.mk _ _ _ _ (sfDerivedImageRestriction f φ).hom))

/-- Finite evaluation of direct image by the specified geometric mate.
Source: Zheng 4.10 (blueprint: lem-sf-system-proper-scalar-evaluation). -/
def systemDirectFiniteEvaluation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    systemDirect l E f ⋙ coefficientSequenceDerivedEvaluation l E Y n ≅
      coefficientSequenceDerivedEvaluation l E X n ⋙
        proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) :=
  letI := systemDirectEvaluation_isIso l E f n
  asIso (systemDirectEvaluation l E f n)

private def evaluationOfMate
    {X Y x y : Type u} [Category.{u} X] [Category.{u} Y]
    [Category.{u} x] [Category.{u} y]
    (E : X ⥤ x) (F : Y ⥤ y)
    {L : X ⥤ Y} {P : Y ⥤ X} {l : x ⥤ y} {p : y ⥤ x}
    (a : L ⊣ P) (b : l ⊣ p) (e : L ⋙ F ≅ E ⋙ l)
    (v : P ⋙ E ≅ F ⋙ p)
    (hv : v.hom = (mateEquiv a b e.inv)) :
    SemilinearSections.AdjunctionEvaluation E F a b where
  left := e
  right := v
  unit A := by
    rw [hv]
    have hh := congrArg (fun z ↦ z ≫ p.map (e.hom.app A))
      (unit_mateEquiv a b e.inv A)
    simp only [Functor.id_obj, Category.assoc] at hh
    rw [← p.map_comp, Iso.inv_hom_id_app] at hh
    erw [p.map_id, Category.comp_id] at hh
    exact hh
  counit B := by
    rw [hv]
    exact mateEquiv_counit a b e.inv B

/-- Evaluation takes the system direct-image scalar mate to the finite scalar transpose.
This concerns arbitrary unbounded systems; it asserts no invertibility of the scalar mate.

Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 06YY, 07A6, 0941 and 0D6E;
step 2 of lem-sf-compact-scalar-evaluation-square.
(blueprint: lem-sf-system-proper-scalar-evaluation).

Proof: on the vertical sequence site, evaluate the ordinary inverse-image unit and
counit against the identity-on-sections direct-image comparison. The scalar/pullback
comparison sends 1 tensor gamma(x) to gamma(1 tensor x). Use the universal cochain
counits to transport this equality to the fixed derived scalar models. The normalized
scalar evaluation isomorphism is the transpose of the restriction/evaluation identity;
the two adjoint-uniqueness comparisons in its definition preserve that transpose.
Expand systemDirectScalar as unit, inverse scalar/pullback comparison and counit.
The evaluated unit and counit equations, followed by evaluation_mate, give the finite
geometric scalar mate. Iterated mate interchange identifies its scalar transpose with
the normalized direct-image restriction comparison: on a K-injective target, resolve
its scalar restriction and use the geometric triangle identity; the resulting map is
the inverse of direct image of the resolution, which specifies sfDerivedImageRestriction.
The finite scalar Hom bijection identifies the maps. Naturality carries the two scalar
evaluation comparisons to the ends, giving the displayed equation. This is an equation
of localized, normalized mate words; no faithfulness of derived evaluation or preservation
of K-injectives by scalar restriction is used. The argument includes n=0, the zero
complex, empty schemes and identity embeddings, without quotient-flatness hypotheses. -/
theorem systemDirectScalar_finiteEvaluation
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (N : coefficientSequenceDerived l E X) :
    letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    letI := Padic.finite_coefficientExtensionRing l L (n + 1) (Nat.succ_pos n)
    (coefficientSequenceDerivedEvaluation l L Y n).map
          ((systemDirectScalar l E L ι f).app N) ≫
        (systemDirectFiniteEvaluation l L f n).hom.app
          ((integralComparisonDerivedSequenceScalar l E L ι X).obj N) ≫
        (proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l L (n + 1))).map
          ((systemScalarFiniteEvaluation l E L ι X n).hom.app N) =
      (systemScalarFiniteEvaluation l E L ι Y n).hom.app ((systemDirect l E f).obj N) ≫
        (pbcDerivedExtend (scalarRingMap (integralScalarQuotientMap l E L ι n) Y)).map
          ((systemDirectFiniteEvaluation l E f n).hom.app N) ≫
    (finiteDirectScalar (integralScalarQuotientMap l E L ι n) f).app
          ((coefficientSequenceDerivedEvaluation l E X n).obj N) := by
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  letI := Padic.finite_coefficientExtensionRing l L (n + 1) (Nat.succ_pos n)
  let adjE := systemAdjunction l E f
  let adjL := systemAdjunction l L f
  let levelE := (sfIntrinsicConstantModuleAdjunction f
    (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategoryRightDerivedAdjunction
  let levelL := (sfIntrinsicConstantModuleAdjunction f
    (Padic.coefficientExtensionRing l L (n + 1))).mapDerivedCategoryRightDerivedAdjunction
  let eE := (systemPullEvaluation l E f n).symm
  let eL := (systemPullEvaluation l L f n).symm
  let vE := systemDirectFiniteEvaluation l E f n
  let vL := systemDirectFiniteEvaluation l L f n
  let A := integralScalarQuotientMap l E L ι n
  let a := (mateEquiv levelE levelL).symm (finiteDirectScalar A f)
  let evE := evaluationOfMate
    (coefficientSequenceDerivedEvaluation l E Y n)
    (coefficientSequenceDerivedEvaluation l E X n)
    adjE levelE eE vE (by rfl)
  let evL := evaluationOfMate
    (coefficientSequenceDerivedEvaluation l L Y n)
    (coefficientSequenceDerivedEvaluation l L X n)
    adjL levelL eL vL (by rfl)
  have h := evaluation_mate adjE adjL levelE levelL evE evL
    (systemScalarFiniteEvaluation l E L ι Y n)
    (systemScalarFiniteEvaluation l E L ι X n)
    (TwoSquare.mk _ _ _ _ (integralComparisonSystemScalarPullback l E L ι f).inv)
    a (systemProperScalarEvaluation_compatibility l E L ι f n) N
  simpa only [evE, evL, evaluationOfMate, systemDirectScalar,
    systemDirectFiniteEvaluation, a, A, vE, vL, Equiv.apply_symm_apply] using h

end WeilConjectures.FrobeniusExchange
