/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Compact.CompactSupportReductionTowerData
import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeSystemEvaluation

/-! # Native presentation of a coherent compact-support tower

Source: the canonical coefficient comparisons in blueprint
`lem-coef-integral-compact-support.proof.md`, paragraphs 1–2, and the native
construction of `lem-weil-compact-support-reduction-tower-functor`.
(blueprint: def-weil-compact-support-native-tower-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
-- Use the same coefficient-category structures as the tower construction.
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
  WeilConjectures.SemilinearSections.locallyBijective
  WeilConjectures.SemilinearSections.moduleAbelian WeilConjectures.SemilinearSections.hasDerived
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- A tower and its evaluations retain their native construction, before taking a limit.
Keeping the condition abstract prevents the canonical evaluation pasting from being
expanded in the predicates of every downstream choice expression.
Source: blueprint `lem-coef-integral-compact-support.proof.md`, paragraphs 1–2;
Bhatt--Scholze, Definition 6.7.6.
(blueprint: def-weil-compact-support-native-tower-presentation). -/
@[no_expose, irreducible]
def IsNativeCompactSupportTowerPresentation
    (T : DerivedCategory (scalarReductionSource l E X) ⥤
      DerivedCategory (pbcTowers Y (completedIntegralCommRingSheafUnrestricted l E Y)))
    (e : ∀ n : ℕ, T ⋙ pbcTowerEvaluation Y (completedIntegralCommRingSheafUnrestricted l E Y) n ≅
      compactSupportRestrictedLevel l E c n) : Prop :=
  ∃ S : CoefficientDerivedSystemCalculus l E X,
    let N := S.reduction ⋙
      ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) c.i ⋙
      ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) c.g
    T = N ⋙ coefficientSequenceDerivedRestriction l E Y ∧
      HEq e (fun n : ℕ ↦
        Functor.isoWhiskerLeft N (coefficientRestrictedEvaluationIso l E Y n) ≪≫
          (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight
            (Functor.associator _ _ _ ≪≫
              Functor.isoWhiskerLeft S.reduction (compactSupportSystemEvaluation l E c n) ≪≫
              (Functor.associator _ _ _).symm ≪≫
              Functor.isoWhiskerRight (S.reductionEvaluation n) _) _)

end WeilConjectures
