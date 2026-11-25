/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusExchange.SystemOperationExchangeRealization
public import WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteCompactScalarConstructible
import WeilConjectures.SmoothPurity.FrobeniusExchange.SystemProperScalarEvaluation
import WeilConjectures.SmoothPurity.FrobeniusExchange.SystemOpenScalarEvaluation
import all WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteCompactSupportScalarTransport
import all WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteCompactScalarConstructible

/-! # Evaluation of the proper/open scalar word

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks 0941, 06YY and 07A6;
the compact-support paragraph of `proposition-six-operations-change-coefficients`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FrobeniusExchange
open AlgebraicGeometry.Scheme.FiniteCompactScalar

/-- Finite evaluation of compact support on an arbitrary derived system. Both
factors are the specified direct-image and open-adjunction evaluation mates.
Source: Zheng 4.10 (blueprint: lem-sf-compact-scalar-evaluation-square). -/
def systemCompactEvaluation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ) :
    (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g) ⋙
        coefficientSequenceDerivedEvaluation l E Y n ≅
      coefficientSequenceDerivedEvaluation l E X n ⋙
        sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)) := by
  letI := systemDirectEvaluation_isIso l E c.g n
  letI := systemOpenEvaluationInv_isIso l E c.i n
  exact Functor.isoWhiskerLeft (systemDerivedOpen l E c.i)
      (asIso (systemDirectEvaluation l E c.g n)) ≪≫
    Functor.isoWhiskerRight (asIso (systemOpenEvaluationInv l E c.i n)).symm
      (proEtaleConstantDerivedDirectImage c.g
        (Padic.coefficientExtensionRing l E (n + 1)))

private theorem finiteCompactScalar_factors
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : proEtaleDerivedCategory X A) :
    (intrinsicCompactScalar φ c).app K =
      (finiteDirectScalar φ c.g).app
          ((sfIntrinsicExtensionByZero c.i A).mapDerivedCategory.obj K) ≫
        (proEtaleConstantDerivedDirectImage c.g B).map ((finiteOpenScalar φ c.i).app K) := by
  rw [intrinsicCompactScalar_app]
  rw [intrinsic_scalar_transpose_paste]
  congr 1
  · exact (scalarTranspose_app
      (pbcDerivedScalarAdjunction (scalarRingMap φ c.Z))
      (pbcDerivedScalarAdjunction (scalarRingMap φ Y))
      (sfDerivedImageRestriction c.g φ).hom
      ((sfIntrinsicExtensionByZero c.i A).mapDerivedCategory.obj K)).symm
  · congr 1
    exact (scalarTranspose_app
      (pbcDerivedScalarAdjunction (scalarRingMap φ X))
      (pbcDerivedScalarAdjunction (scalarRingMap φ c.Z))
      (Functor.mapDerivedCategorySquareIso (sfOpenRestriction c.i φ)).hom K).symm

private theorem scalarWord_paste
    {C : Type*} [Category* C]
    {A B D E F G H I J K L M : C}
    (x : A ⟶ B) (y : B ⟶ D) (z : D ⟶ E) (q : E ⟶ F) (r : F ⟶ G)
    (v : B ⟶ H) (w : H ⟶ E) (d : H ⟶ I) (e : I ⟶ J) (a : J ⟶ G)
    (s : A ⟶ K) (t : K ⟶ L) (b : L ⟶ I) (k : L ⟶ M) (b' : M ⟶ J)
    (hv : y ≫ z = v ≫ w) (ho : w ≫ q ≫ r = d ≫ e ≫ a)
    (hp : x ≫ v ≫ d = s ≫ t ≫ b) (hb : k ≫ b' = b ≫ e) :
    x ≫ (y ≫ z ≫ q) ≫ r = s ≫ (t ≫ k) ≫ (b' ≫ a) := by
  simp only [Category.assoc]
  rw [reassoc_of% hv, ho, reassoc_of% hp, ← reassoc_of% hb]

private theorem scalarFunctorWord_paste
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    (P : C ⥤ D) (Q : E ⥤ D) (R : F ⥤ D)
    {c₀ c₁ c₂ : C} {e₀ e₁ e₂ e₃ e₄ e₅ : E} {f₀ f₁ f₂ : F}
    (x : c₀ ⟶ c₁) (y : c₁ ⟶ c₂)
    (w : e₀ ⟶ e₁) (q : e₁ ⟶ e₂) (r : e₂ ⟶ e₃)
    (d : e₀ ⟶ e₄) (e : e₄ ⟶ e₅) (a : e₅ ⟶ e₃)
    (t : f₀ ⟶ f₁) (k : f₁ ⟶ f₂)
    (z : P.obj c₂ ⟶ Q.obj e₁) (v : P.obj c₁ ⟶ Q.obj e₀)
    (s : P.obj c₀ ⟶ R.obj f₀) (b : R.obj f₁ ⟶ Q.obj e₄)
    (b' : R.obj f₂ ⟶ Q.obj e₅)
    (hv : P.map y ≫ z = v ≫ Q.map w)
    (ho : w ≫ q ≫ r = d ≫ e ≫ a)
    (hp : P.map x ≫ v ≫ Q.map d = s ≫ R.map t ≫ b)
    (hb : R.map k ≫ b' = b ≫ Q.map e) :
    P.map (x ≫ y) ≫ (z ≫ Q.map q) ≫ Q.map r =
      s ≫ R.map (t ≫ k) ≫ (b' ≫ Q.map a) := by
  have ho' := congrArg Q.map ho
  simp only [Functor.map_comp] at ho'
  simpa only [Functor.map_comp, Category.assoc] using scalarWord_paste
    (P.map x) (P.map y) z (Q.map q) (Q.map r) v (Q.map w)
    (Q.map d) (Q.map e) (Q.map a) s (R.map t) b (R.map k) b' hv ho' hp hb

private theorem systemCompactEvaluation_hom_app
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ)
    (N : coefficientSequenceDerived l E X) :
    (systemCompactEvaluation l E c n).hom.app N =
      (systemDirectFiniteEvaluation l E c.g n).hom.app ((systemDerivedOpen l E c.i).obj N) ≫
        (proEtaleConstantDerivedDirectImage c.g
          (Padic.coefficientExtensionRing l E (n + 1))).map
            ((systemOpenFiniteEvaluation l E c.i n).hom.app N) := by
  rfl

attribute [local irreducible] systemScalarFiniteEvaluation

private theorem systemCompactScalar_evaluation_of_factors
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ)
    (s : ∀ W : Scheme.{u},
      integralComparisonDerivedSequenceScalar l E L ι W ⋙
          coefficientSequenceDerivedEvaluation l L W n ≅
        coefficientSequenceDerivedEvaluation l E W n ⋙
          pbcDerivedExtend (scalarRingMap (integralScalarQuotientMap l E L ι n) W))
    (hproper : ∀ N : coefficientSequenceDerived l E c.Z,
    letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    letI := Padic.finite_coefficientExtensionRing l L (n + 1) (Nat.succ_pos n)
    (coefficientSequenceDerivedEvaluation l L Y n).map
          ((systemDirectScalar l E L ι c.g).app N) ≫
        (systemDirectFiniteEvaluation l L c.g n).hom.app
          ((integralComparisonDerivedSequenceScalar l E L ι c.Z).obj N) ≫
        (proEtaleConstantDerivedDirectImage c.g (Padic.coefficientExtensionRing l L (n + 1))).map
          ((s c.Z).hom.app N) =
      (s Y).hom.app ((systemDirect l E c.g).obj N) ≫
        (pbcDerivedExtend (scalarRingMap (integralScalarQuotientMap l E L ι n) Y)).map
          ((systemDirectFiniteEvaluation l E c.g n).hom.app N) ≫
        (finiteDirectScalar (integralScalarQuotientMap l E L ι n) c.g).app
          ((coefficientSequenceDerivedEvaluation l E c.Z n).obj N))
    (hopen : ∀ N : coefficientSequenceDerived l E X,
    letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    letI := Padic.finite_coefficientExtensionRing l L (n + 1) (Nat.succ_pos n)
    (coefficientSequenceDerivedEvaluation l L c.Z n).map
          ((systemOpenScalar l E L ι c.i).hom.app N) ≫
        (systemOpenFiniteEvaluation l L c.i n).hom.app
          ((integralComparisonDerivedSequenceScalar l E L ι X).obj N) ≫
        (sfIntrinsicExtensionByZero c.i
          (Padic.coefficientExtensionRing l L (n + 1))).mapDerivedCategory.map
            ((s X).hom.app N) =
      (s c.Z).hom.app ((systemDerivedOpen l E c.i).obj N) ≫
        (pbcDerivedExtend (scalarRingMap (integralScalarQuotientMap l E L ι n) c.Z)).map
          ((systemOpenFiniteEvaluation l E c.i n).hom.app N) ≫
        (finiteOpenScalar (integralScalarQuotientMap l E L ι n) c.i).app
          ((coefficientSequenceDerivedEvaluation l E X n).obj N)) :
    letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    letI := Padic.finite_coefficientExtensionRing l L (n + 1) (Nat.succ_pos n)
    ∀ N : coefficientSequenceDerived l E X,
        (coefficientSequenceDerivedEvaluation l L Y n).map
            ((systemCompactScalar l E L ι c).app N) ≫
          (systemCompactEvaluation l L c n).hom.app
            ((integralComparisonDerivedSequenceScalar l E L ι X).obj N) ≫
          (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l L (n + 1))).map
            ((s X).hom.app N) =
        (s Y).hom.app ((systemDerivedOpen l E c.i ⋙ systemDirect l E c.g).obj N) ≫
          (pbcDerivedExtend (scalarRingMap (integralScalarQuotientMap l E L ι n) Y)).map
            ((systemCompactEvaluation l E c n).hom.app N) ≫
          (intrinsicCompactScalar (integralScalarQuotientMap l E L ι n) c).app
            ((coefficientSequenceDerivedEvaluation l E X n).obj N) := by
  let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let := Padic.finite_coefficientExtensionRing l L (n + 1) (Nat.succ_pos n)
  intro N
  let φ := integralScalarQuotientMap l E L ι n
  let JA := systemDerivedOpen l E c.i
  let JB := systemDerivedOpen l L c.i
  let PA := systemDirect l E c.g
  let PB := systemDirect l L c.g
  let jA := (sfIntrinsicExtensionByZero c.i
    (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory
  let jB := (sfIntrinsicExtensionByZero c.i
    (Padic.coefficientExtensionRing l L (n + 1))).mapDerivedCategory
  let pA := proEtaleConstantDerivedDirectImage c.g (Padic.coefficientExtensionRing l E (n + 1))
  let pB := proEtaleConstantDerivedDirectImage c.g (Padic.coefficientExtensionRing l L (n + 1))
  let VX := coefficientSequenceDerivedEvaluation l E X n
  let VZ := coefficientSequenceDerivedEvaluation l E c.Z n
  let WZ := coefficientSequenceDerivedEvaluation l L c.Z n
  let WY := coefficientSequenceDerivedEvaluation l L Y n
  let SX := integralComparisonDerivedSequenceScalar l E L ι X
  let SZ := integralComparisonDerivedSequenceScalar l E L ι c.Z
  let tZ := pbcDerivedExtend (scalarRingMap φ c.Z)
  let tY := pbcDerivedExtend (scalarRingMap φ Y)
  let sX := (s X).hom
  let sZ := (s c.Z).hom
  let sY := (s Y).hom
  let uA := (systemOpenFiniteEvaluation l E c.i n).hom
  let uB := (systemOpenFiniteEvaluation l L c.i n).hom
  let vA := (systemDirectFiniteEvaluation l E c.g n).hom
  let vB := (systemDirectFiniteEvaluation l L c.g n).hom
  let α := (systemOpenScalar l E L ι c.i).hom
  let β := systemDirectScalar l E L ι c.g
  let a := finiteOpenScalar φ c.i
  let b := finiteDirectScalar φ c.g
  have hp : WY.map (β.app (JA.obj N)) ≫ vB.app (SZ.obj (JA.obj N)) ≫
        pB.map (sZ.app (JA.obj N)) =
      sY.app (PA.obj (JA.obj N)) ≫ tY.map (vA.app (JA.obj N)) ≫
        b.app (VZ.obj (JA.obj N)) :=
    hproper (JA.obj N)
  have ho : WZ.map (α.app N) ≫ uB.app (SX.obj N) ≫ jB.map (sX.app N) =
      sZ.app (JA.obj N) ≫ tZ.map (uA.app N) ≫ a.app (VX.obj N) :=
    hopen N
  have hv : WY.map (PB.map (α.app N)) ≫ vB.app (JB.obj (SX.obj N)) =
      vB.app (SZ.obj (JA.obj N)) ≫ pB.map (WZ.map (α.app N)) := vB.naturality (α.app N)
  have hb : tY.map (pA.map (uA.app N)) ≫ b.app (jA.obj (VX.obj N)) =
      b.app (VZ.obj (JA.obj N)) ≫ pB.map (tZ.map (uA.app N)) := b.naturality (uA.app N)
  rw [systemCompactEvaluation_hom_app, systemCompactEvaluation_hom_app,
    finiteCompactScalar_factors]
  change WY.map (β.app (JA.obj N) ≫ PB.map (α.app N)) ≫
      (vB.app (JB.obj (SX.obj N)) ≫ pB.map (uB.app (SX.obj N))) ≫
      pB.map (jB.map (sX.app N)) =
    sY.app (PA.obj (JA.obj N)) ≫
      tY.map (vA.app (JA.obj N) ≫ pA.map (uA.app N)) ≫
      (b.app (jA.obj (VX.obj N)) ≫ pB.map (a.app (VX.obj N)))
  exact scalarFunctorWord_paste WY pB tY
    (β.app (JA.obj N)) (PB.map (α.app N))
    (WZ.map (α.app N)) (uB.app (SX.obj N)) (jB.map (sX.app N))
    (sZ.app (JA.obj N)) (tZ.map (uA.app N)) (a.app (VX.obj N))
    (vA.app (JA.obj N)) (pA.map (uA.app N))
    (vB.app (JB.obj (SX.obj N))) (vB.app (SZ.obj (JA.obj N)))
    (sY.app (PA.obj (JA.obj N))) (b.app (VZ.obj (JA.obj N)))
    (b.app (jA.obj (VX.obj N))) hv ho hp hb

/-- The evaluated system scalar word is the intrinsic finite scalar transpose,
through scalar evaluation and the fixed proper/open evaluation maps. This is an
identity of arrows for arbitrary systems, without constructibility, boundedness,
Noetherian, completeness or cartesian-system hypotheses.

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks 0941, 06YY, 07A6;
`proposition-six-operations-change-coefficients`, compact-support paragraph, and step 3 of
`lem-sf-compact-support-system-scalar-finite-invertible`.
(blueprint: lem-sf-compact-scalar-evaluation-square).

Proof: on the vertical sequence site use the compatible quotient ring maps
induced by the embedding. The ScalarSystems evaluation comparison is the
transpose of identity-on-sections restriction evaluation. Transport its source
model to integralComparisonSequenceScalarModel using the unique isomorphism of
universal cochain left-derived pairs. Transport each target model to the fixed
pbcDerivedExtend in the same way. This gives the scalar evaluation isomorphisms
s below, normalized on K-flat representatives by tensor evaluation.

Evaluate the unit, pullback/scalar comparison, and counit defining
systemDirectScalar. The unit and counit equations in AdjunctionEvaluation and
SemilinearSections.evaluation_mate identify the resulting word with the finite
proper scalar mate. For the open factor apply that calculation to the exact
open adjunction; evaluation preserves its inverse because the open mate is an
isomorphism. The resulting finite open map is the transpose of sfOpenRestriction.
Scalar mate pasting identifies the composite of these two transposes with the
transpose of sfCompactSupportRestriction, namely intrinsicCompactScalar.
Naturality moves the two scalar evaluation comparisons to the ends and gives
exactly the displayed equality, using the specified systemCompactEvaluation.
All equations are checked on the same ordinary units and universal cochain
counits before localization; no equality is inferred from derived evaluations.
The construction includes n=0, zero complexes, empty schemes and identity
embeddings, and does not require any finite quotient map to be flat. -/
theorem systemCompactScalar_evaluation_square
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ) :
    letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    letI := Padic.finite_coefficientExtensionRing l L (n + 1) (Nat.succ_pos n)
    ∃ s : ∀ W : Scheme.{u},
      integralComparisonDerivedSequenceScalar l E L ι W ⋙
          coefficientSequenceDerivedEvaluation l L W n ≅
        coefficientSequenceDerivedEvaluation l E W n ⋙
          pbcDerivedExtend (scalarRingMap (integralScalarQuotientMap l E L ι n) W),
      ∀ N : coefficientSequenceDerived l E X,
        (coefficientSequenceDerivedEvaluation l L Y n).map
            ((systemCompactScalar l E L ι c).app N) ≫
          (systemCompactEvaluation l L c n).hom.app
            ((integralComparisonDerivedSequenceScalar l E L ι X).obj N) ≫
          (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l L (n + 1))).map
            ((s X).hom.app N) =
        (s Y).hom.app ((systemDerivedOpen l E c.i ⋙ systemDirect l E c.g).obj N) ≫
          (pbcDerivedExtend (scalarRingMap (integralScalarQuotientMap l E L ι n) Y)).map
            ((systemCompactEvaluation l E c n).hom.app N) ≫
          (intrinsicCompactScalar (integralScalarQuotientMap l E L ι n) c).app
            ((coefficientSequenceDerivedEvaluation l E X n).obj N) := by
  let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let := Padic.finite_coefficientExtensionRing l L (n + 1) (Nat.succ_pos n)
  refine ⟨fun W ↦ systemScalarFiniteEvaluation l E L ι W n, ?_⟩
  exact systemCompactScalar_evaluation_of_factors l E L ι c n
    (fun W ↦ systemScalarFiniteEvaluation l E L ι W n)
    (fun N ↦ systemDirectScalar_finiteEvaluation l E L ι c.g n N)
    (fun N ↦ systemOpenScalar_finiteEvaluation l E L ι c.i n N)

end WeilConjectures.FrobeniusExchange
