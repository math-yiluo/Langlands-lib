/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientAction
public import WeilConjectures.SixFunctors.FrobeniusExchange.SystemOperationExchangeRealization
import WeilConjectures.SmoothPurity.FrobeniusExchange.CompactSupportSystemScalarFiniteInvertible
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated

/-! # A step of normalized compact-support scalar comparison

Source: proposition-six-operations-change-coefficients, compact-support and final paragraphs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Coefficient coefficientInclusion)

variable (l : ℕ) [Fact l.Prime]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [xo : X.Over (Spec (.of K₀))] [yo : Y.Over (Spec (.of K₀))]
  [xft : LocallyOfFiniteType (X ↘ Spec (.of K₀))] [xqc : QuasiCompact (X ↘ Spec (.of K₀))]
  [yft : LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [yqc : QuasiCompact (Y ↘ Spec (.of K₀))]
  [fo : f.IsOver (Spec (.of K₀))] [fs : IsSeparated f]
  [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]
  (c : Compactification f)

include hl xo yo xft xqc yft yqc fo fs fft fqc

/-- Realization of the proper/open scalar mate is invertible on integral constructible
inputs. Source: proposition-six-operations-change-coefficients, compact-support paragraph;
normalized scalar isomorphisms, proof steps 2--4
(blueprint: lem-sf-compact-support-coefficient-exchange-invertible).
Proof: scalar extension preserves bounded integral constructibility. At every quotient,
choose the bounded constructible etale antecedent of the input. Tensor/pullback
compatibility identifies its scalar extension with the reduction of the completed
extension; exact full faithfulness of the etale/pro-etale pullback detects boundedness.
Finite compact-support scalar transport identifies the evaluated proper/open mate
with an isomorphism. The semilinear system calculus identifies these evaluations with
the evaluations of the actual whole-system mate. Joint conservativity proves that
mate invertible. The source comparison is invertible by normalized effectivity on the
constructible compact-support output, and the target comparison is the inverse scalar
reduction isomorphism. Applying the total-limit functor and composing these maps gives
invertibility of the displayed coefficient exchange. No quotient map is assumed flat. -/
theorem sfCompactSupportCoefficientExchange_isIso
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (K : sfIntegralConstructibleCategory l E X) :
    IsIso ((FrobeniusExchange.coefficientExchange l E L ι
      (FrobeniusExchange.systemDerivedOpen l E c.i ⋙ FrobeniusExchange.systemDirect l E c.g)
      (FrobeniusExchange.systemDerivedOpen l L c.i ⋙ FrobeniusExchange.systemDirect l L c.g)
      (FrobeniusExchange.systemCompactScalar l E L ι c)).app K) := by
  have hunit (W : Scheme.{u}) [W.Over (Spec (.of K₀))] (x : W) :
      IsUnit (l : W.residueField x) := by
    let φ := ((Scheme.ΓSpecIso (.of K₀)).inv ≫
      (W ↘ Spec (.of K₀)).appTop ≫ W.Γevaluation x).hom
    exact Eq.mp (congrArg IsUnit (map_natCast φ l)) (hl.map φ)
  let (x : X) : Invertible (l : X.residueField x) := (hunit X x).invertible
  let (y : Y) : Invertible (l : Y.residueField y) := (hunit Y y).invertible
  let H := FrobeniusExchange.systemDerivedOpen l E c.i ⋙
    FrobeniusExchange.systemDirect l E c.g
  let H' := FrobeniusExchange.systemDerivedOpen l L c.i ⋙
    FrobeniusExchange.systemDirect l L c.g
  have hc : IsIso ((FrobeniusExchange.operationReduction l E H).app K.obj) := by
    apply (((FrobeniusExchange.models l E).system Y).isIso_iff_evaluations _).2
    intro n
    have h := (FrobeniusExchange.compactRealization_exists
      l E K₀ hl f c).choose_spec K n
    have hi : IsIso
        ((scalarReductionDerivedExtension l E Y n).map
            ((FrobeniusExchange.compactRealization l E K₀ hl f c).hom.app K) ≫
          (((FrobeniusExchange.models l E).system Y).reductionEvaluation n).inv.app
            ((FrobeniusExchange.compactImage l E f c).obj K.obj) ≫
          (coefficientSequenceDerivedEvaluation l E Y n).map
            ((FrobeniusExchange.operationReduction l E H).app K.obj) ≫
          (FrobeniusExchange.compactFiniteEvaluation l E c n).hom.app K.obj) := by
      exact h.symm ▸ (inferInstance :
        IsIso (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom)
    have : IsIso
        ((((FrobeniusExchange.models l E).system Y).reductionEvaluation n).inv.app
            ((FrobeniusExchange.compactImage l E f c).obj K.obj) ≫
          (coefficientSequenceDerivedEvaluation l E Y n).map
            ((FrobeniusExchange.operationReduction l E H).app K.obj) ≫
          (FrobeniusExchange.compactFiniteEvaluation l E c n).hom.app K.obj) :=
      IsIso.of_isIso_comp_left
        ((scalarReductionDerivedExtension l E Y n).map
          ((FrobeniusExchange.compactRealization l E K₀ hl f c).hom.app K)) _
    have : IsIso
        ((coefficientSequenceDerivedEvaluation l E Y n).map
            ((FrobeniusExchange.operationReduction l E H).app K.obj) ≫
          (FrobeniusExchange.compactFiniteEvaluation l E c n).hom.app K.obj) :=
      IsIso.of_isIso_comp_left
        ((((FrobeniusExchange.models l E).system Y).reductionEvaluation n).inv.app
          ((FrobeniusExchange.compactImage l E f c).obj K.obj)) _
    exact IsIso.of_isIso_comp_right _
      ((FrobeniusExchange.compactFiniteEvaluation l E c n).hom.app K.obj)
  let N := (FrobeniusExchange.reduction l E X).obj K.obj
  have he : IsIso ((FrobeniusExchange.systemCompactScalar l E L ι c).app N) := by
    let : c.Z.Over (Spec (.of K₀)) := ⟨c.g ≫ (Y ↘ Spec (.of K₀))⟩
    have : LocallyOfFiniteType (c.Z ↘ Spec (.of K₀)) :=
      inferInstanceAs (LocallyOfFiniteType (c.g ≫ (Y ↘ Spec (.of K₀))))
    have : QuasiCompact (c.Z ↘ Spec (.of K₀)) :=
      inferInstanceAs (QuasiCompact (c.g ≫ (Y ↘ Spec (.of K₀))))
    have : IsLocallyNoetherian c.Z :=
      LocallyOfFiniteType.isLocallyNoetherian (c.Z ↘ Spec (.of K₀))
    have : CompactSpace c.Z :=
      QuasiCompact.compactSpace_of_compactSpace (c.Z ↘ Spec (.of K₀))
    have : IsNoetherian c.Z := ⟨⟩
    have : IsLocallyNoetherian Y :=
      LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of K₀))
    have : CompactSpace Y :=
      QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of K₀))
    have : IsNoetherian Y := ⟨⟩
    apply (((FrobeniusExchange.models l L).system Y).isIso_iff_evaluations _).2
    intro n
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let B := Padic.coefficientExtensionRing l L (n + 1)
    have : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    have : Finite B := Padic.finite_coefficientExtensionRing l L (n + 1) (Nat.succ_pos n)
    have : ObjectProperty.IsClosedUnderIsomorphisms
        (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X) :=
      (proEtale_bounded_constructible_isTriangulated X A).1
    have : ObjectProperty.IsClosedUnderIsomorphisms
        (intrinsicFiniteTorsionConstructible l L (n + 1) (Nat.succ_pos n) X) :=
      (proEtale_bounded_constructible_isTriangulated X B).1
    have hN : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X
        ((coefficientSequenceDerivedEvaluation l E X n).obj N) :=
      ObjectProperty.prop_of_iso _
        ((((FrobeniusExchange.models l E).system X).reductionEvaluation n).app K.obj).symm
        (K.property.2.choose_spec.choose_spec.2 n).1
    let T := (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).obj K
    let e := (((FrobeniusExchange.models l L).system X).reductionEvaluation n).app T.obj
    let e' := (coefficientSequenceDerivedEvaluation l L X n).mapIso
      ((FrobeniusExchange.scalarReductionIso l E L ι X).app K)
    have hS : intrinsicFiniteTorsionConstructible l L (n + 1) (Nat.succ_pos n) X
        ((coefficientSequenceDerivedEvaluation l L X n).obj
          ((integralComparisonDerivedSequenceScalar l E L ι X).obj N)) :=
      ObjectProperty.prop_of_iso _ (e.symm ≪≫ e')
        (T.property.2.choose_spec.choose_spec.2 n).1
    exact FrobeniusExchange.systemCompactScalar_evaluation_isIso l E L ι c N n hN hS
  change IsIso (((FrobeniusExchange.models l E).system Y).adjunction.counit.app
    ((FrobeniusExchange.reduction l E X ⋙ H).obj K.obj)) at hc
  have hs : IsIso
      ((FrobeniusExchange.scalarSourceComparison l E L ι H).app K.obj) := by
    change IsIso
      (((FrobeniusExchange.scalarModels l E L ι).model Y).realization.hom.app
          ((FrobeniusExchange.realize l E H).obj K.obj) ≫
        (coefficientSequenceLimit l L Y).map
          ((integralComparisonDerivedSequenceScalar l E L ι Y).map
            (((FrobeniusExchange.models l E).system Y).adjunction.counit.app
              ((FrobeniusExchange.reduction l E X ⋙ H).obj K.obj))))
    infer_instance
  change IsIso ((FrobeniusExchange.scalarSourceComparison l E L ι H).app K.obj ≫
    (coefficientSequenceLimit l L Y).map
      ((FrobeniusExchange.systemCompactScalar l E L ι c).app N) ≫
    (H' ⋙ coefficientSequenceLimit l L Y).map
      ((FrobeniusExchange.scalarReductionIso l E L ι X).inv.app K))
  infer_instance

end WeilConjectures
