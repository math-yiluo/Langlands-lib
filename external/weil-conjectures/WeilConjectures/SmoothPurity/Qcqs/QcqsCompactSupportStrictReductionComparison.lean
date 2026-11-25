/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeSystemEvaluation
import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportStrictReductionData
import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportStrictReductionGamma

/-! # Strict proper/open comparison before total inverse limit

Source: Bhatt--Scholze, Definition 6.7.6 and Lemma 6.7.7; Stacks 0941, 0F7J
(blueprint: lem-qcqs-compact-support-strict-reduction-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open PurCompactSupport

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

/-- The strict proper/open reduction comparison and the independently recorded limit
identification, retaining their actual projection coordinates. No morphism from the
ambient proper/open value to the recorded integral value is asserted here.

Source: Bhatt--Scholze Definition 6.7.6 and Lemma 6.7.7; Stacks 0941, 0F7J
(blueprint: lem-qcqs-compact-support-strict-reduction-comparison).

Proof: choose simultaneous coefficient reduction calculi on X and Y. The open
scalar-adjunction mate is tensor extension on strict flat-term K-flat complexes;
its quotient maps commute with each transition because both maps send a pure tensor
to the same tensor with reduced coefficient. Apply separately derived proper image
in the varying-ring diagram category. Its scalar mate gives beta on the entire
strict derived system, for every ambient input, with no constructibility hypothesis.
Evaluation of this map is the ordered proper/open scalar mate;
the scalar adjunction units give the first equation, including both endpoint changes
of finite coordinates. Construct everything on simultaneous resolutions and descend
through quasi-isomorphisms, so beta is natural in the derived input.

For gamma, restrict this native system to completed scalars and compare with the
chosen coherent tower of exists_compactSupportReductionTower. Its evaluation
comparisons and every quotient transition are those of the native system. The
universal right-derived comparison identifies its total limit with the RF used by
exists_compactSupportRepresentativeComparison. Compose its recorded gamma with
this right-derived comparison. The normalization of the derived limit projections
identifies each resulting projection with the chosen Roos projection, whose finite
scalar adjunct is sfCompactSupportFiniteReductionIso. This is the second equation.
All comparisons concern whole strict diagrams before limit; no equality of maps is
inferred merely from equality of finite evaluations. At zero input and on the empty
scheme all constructions and the two equations reduce to their zero versions. -/
theorem qcqsCompactSupport_strictReductionComparison :
    ∃ (SX : CoefficientDerivedSystemCalculus l E X)
      (SY : CoefficientDerivedSystemCalculus l E Y),
    let N := SX.reduction ⋙ ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) c.i ⋙
      ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) c.g
    let e (n : ℕ) : N ⋙ coefficientSequenceDerivedEvaluation l E Y n ≅
        scalarReductionDerivedExtension l E X n ⋙
          sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c :=
      Functor.isoWhiskerLeft SX.reduction (compactSupportSystemEvaluation l E c n) ≪≫
        Functor.isoWhiskerRight (SX.reductionEvaluation n)
          (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)))
    ∃ (β : image (completed l E) c ⋙ SY.reduction ⟶ N)
      (γ : sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
          (sfIntegralConstructible l E Y).ι ≅
        (sfIntegralConstructible l E X).ι ⋙ N ⋙
          coefficientSequenceLimit l E Y),
      (∀ (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ),
        (SY.reductionEvaluation n).inv.app ((image (completed l E) c).obj K) ≫
            (coefficientSequenceDerivedEvaluation l E Y n).map (β.app K) ≫
            (e n).hom.app K =
          (finiteReductionIso l E Y n).inv.app ((image (completed l E) c).obj K) ≫
            (comparison (reduction l E (n + 1) (Nat.le_add_left 1 n)) c).app K ≫
            (finiteImageIso l E n c).hom.app
              ((pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) X)).obj
                K) ≫
            (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1))
              c).map ((finiteReductionIso l E X n).hom.app K)) ∧
      (∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
        γ.hom.app K ≫ (coefficientSequenceProjection l E Y n).app
              ((N).obj K.obj) ≫
            (coefficientFiniteDerivedRestriction l E Y n).map
              ((e n).hom.app K.obj) =
          (coefficientFiniteAdjunction l E Y n).unit.app
              ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K).obj ≫
            (coefficientFiniteDerivedRestriction l E Y n).map
              (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom) := by
  classical
  obtain ⟨SX, SY, hdata⟩ :=
    qcqsCompactSupport_strictReductionData l E K₀ hl c
  dsimp at hdata
  obtain ⟨β, hβ⟩ := hdata
  obtain ⟨γ, hγ⟩ :=
    qcqsCompactSupport_strictReductionGamma l E K₀ hl c SX SY
  dsimp at hγ
  refine ⟨SX, SY, ?_⟩
  dsimp
  exact ⟨β, γ, hβ, hγ⟩

end WeilConjectures
