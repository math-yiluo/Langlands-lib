/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeSystemEvaluation

import WeilConjectures.SixFunctors.IntegralSystemRealization.Reduction.IntegralReductionPullbackModel
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperationModels
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.IntegralOpenReductionIso
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.IntegralOpenFiniteEvaluation
import WeilConjectures.SixFunctors.IntegralSystemRealization.Native.IntegralNativeOpenComparison

/-! # Strict coefficient reduction for open image

Source: Stacks 07A6, 0941; Bhatt--Scholze 6.7.6--6.7.7.
(blueprint: lem-strict-coefficient-open-reduction). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open PurCompactSupport

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {X Y : Scheme.{u}}

/-- Native evaluation in the finite ringed open-image presentation.
Source: Stacks 03DI, 0D6E (blueprint: lem-strict-coefficient-open-reduction). -/
def strictCoefficientOpenEvaluation (f : X ⟶ Y) [IsOpenImmersion f] (n : ℕ) :
    ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f ⋙
      coefficientSequenceDerivedEvaluation l E Y n ≅
    coefficientSequenceDerivedEvaluation l E X n ⋙
      (openExtension (finite l E (n + 1) (Nat.le_add_left 1 n)) f).mapDerivedCategory := by
  have := sfIntrinsicExtensionByZero_additive f
    (Padic.coefficientExtensionRing l E (n + 1))
  have := (sfIntrinsicExtensionByZero_exact f
    (Padic.coefficientExtensionRing l E (n + 1))).2.1
  have := (sfIntrinsicExtensionByZero_exact f
    (Padic.coefficientExtensionRing l E (n + 1))).2.2
  let e := ProEtale.VaryingRing.evalJ (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) f n ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryNatIso
      (compactSupportOpenModel f (Padic.coefficientExtensionRing l E (n + 1))))
  exact e ≪≫ Functor.isoWhiskerLeft _
    (Functor.mapDerivedCategoryNatIso (finiteOpenIso l E n f)).symm

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  HasDerivedCategory.standard pullbackTensorCalculus
attribute [local implicit_reducible] PurCompactSupport.completed
  SemilinearSections.moduleAbelian SemilinearSections.systemRing

private theorem reductionUniq_evaluation (W : Scheme.{u})
    (S T : CoefficientDerivedSystemCalculus l E W)
    (K : DerivedCategory (scalarReductionSource l E W)) (n : ℕ) :
    (coefficientSequenceDerivedEvaluation l E W n).map
        ((S.adjunction.leftAdjointUniq T.adjunction).hom.app K) ≫
      (T.reductionEvaluation n).hom.app K = (S.reductionEvaluation n).hom.app K := by
  let V := coefficientSequenceDerivedEvaluation l E W n
  let R := coefficientFiniteDerivedRestriction l E W n
  let α := S.adjunction.leftAdjointUniq T.adjunction
  have he : (S.reductionEvaluation n).inv.app K ≫ V.map (α.hom.app K) =
      (T.reductionEvaluation n).inv.app K := by
    apply ((coefficientFiniteAdjunction l E W n).homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, R.map_comp,
      ← Category.assoc, ← S.unit_projection]
    have hp := (coefficientSequenceProjection l E W n).naturality (α.hom.app K)
    dsimp only [Functor.comp_map] at hp
    rw [Category.assoc, ← hp, ← Category.assoc]
    rw [Adjunction.unit_leftAdjointUniq_hom_app, T.unit_projection]
  apply (cancel_epi ((S.reductionEvaluation n).inv.app K)).1
  simpa only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] using
    congrArg (fun f ↦ f ≫ (T.reductionEvaluation n).hom.app K) he

private noncomputable def nativeOpenEvaluation (f : X ⟶ Y) [IsOpenImmersion f] (n : ℕ) :
    ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f ⋙
      coefficientSequenceDerivedEvaluation l E Y n ≅
    coefficientSequenceDerivedEvaluation l E X n ⋙
      (sfIntrinsicExtensionByZero f
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory := by
  have := sfIntrinsicExtensionByZero_additive f
    (Padic.coefficientExtensionRing l E (n + 1))
  have := (sfIntrinsicExtensionByZero_exact f
    (Padic.coefficientExtensionRing l E (n + 1))).2.1
  have := (sfIntrinsicExtensionByZero_exact f
    (Padic.coefficientExtensionRing l E (n + 1))).2.2
  exact ProEtale.VaryingRing.evalJ (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) f n ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryNatIso
      (compactSupportOpenModel f (Padic.coefficientExtensionRing l E (n + 1))))

private theorem canonicalOpenReduction
    (o : IntegralSystemRealization.Operations l E)
    (model : IntegralSystemRealization.RealizationModel l E o)
    (f : X ⟶ Y) [IsOpenImmersion f] :
    ∃ β : (openExtension (completed l E) f).mapDerivedCategory ⋙
        (pullbackTensorCalculus l E Y).reduction ⟶
      (pullbackTensorCalculus l E X).reduction ⋙
        ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) f,
      ∀ (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ),
        (coefficientSequenceDerivedEvaluation l E Y n).map (β.app K) ≫
          (nativeOpenEvaluation l E f n).hom.app
            ((pullbackTensorCalculus l E X).reduction.obj K) =
        ((pullbackTensorCalculus l E Y).reductionEvaluation n).hom.app
            ((openExtension (completed l E) f).mapDerivedCategory.obj K) ≫
          (IntegralSystemRealization.openFiniteReduction l E f n).app K ≫
          (sfIntrinsicExtensionByZero f
            (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.map
              (((pullbackTensorCalculus l E X).reductionEvaluation n).inv.app K) := by
  have : ∀ K, IsIso ((model.openReduction l E f).app K) := fun K ↦
    IntegralSystemRealization.integralOpenReductionIso l E o model f K
  have : IsIso (model.openReduction l E f) := NatIso.isIso_of_isIso_app _
  let e := IntegralSystemRealization.integralNativeOpenIso l E f (o.extension f)
  let β := inv (model.openReduction l E f) ≫
    Functor.whiskerLeft (pullbackTensorCalculus l E X).reduction e.hom
  refine ⟨β, ?_⟩
  intro K n
  have := sfIntrinsicExtensionByZero_additive f
    (Padic.coefficientExtensionRing l E (n + 1))
  have := (sfIntrinsicExtensionByZero_exact f
    (Padic.coefficientExtensionRing l E (n + 1))).2.1
  have := (sfIntrinsicExtensionByZero_exact f
    (Padic.coefficientExtensionRing l E (n + 1))).2.2
  let V := coefficientSequenceDerivedEvaluation l E Y n
  let j := (sfIntrinsicExtensionByZero f
    (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory
  have hm := IntegralSystemRealization.integralOpenFiniteEvaluation l E o model f K n
  have he := IntegralSystemRealization.integralNativeOpenComparison l E f
    (o.extension f) (o.openEvaluation f)
    ((pullbackTensorCalculus l E X).reduction.obj K) n
  change V.map (β.app K) ≫ _ = _
  dsimp only [β, NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [V.map_comp, Category.assoc]
  rw [show V.map (e.hom.app _) ≫ (nativeOpenEvaluation l E f n).hom.app _ =
      ((o.openEvaluation f).evaluation n).hom.app _ from he]
  apply (cancel_epi (V.map ((model.openReduction l E f).app K))).1
  have hc := congr_app (IsIso.hom_inv_id (model.openReduction l E f)) K
  simp only [NatTrans.comp_app, NatTrans.id_app] at hc
  simp only [← V.map_comp_assoc, hc, V.map_id, Category.id_comp]
  rw [reassoc_of% hm]
  rw [← j.map_comp, Iso.hom_inv_id_app]
  erw [j.map_id, Category.comp_id]

private theorem nativeOpenReduction (f : X ⟶ Y) [IsOpenImmersion f]
    (SX : CoefficientDerivedSystemCalculus l E X)
    (SY : CoefficientDerivedSystemCalculus l E Y) :
    ∃ β : (openExtension (completed l E) f).mapDerivedCategory ⋙ SY.reduction ⟶
        SX.reduction ⋙ ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) f,
      ∀ (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ),
        (coefficientSequenceDerivedEvaluation l E Y n).map (β.app K) ≫
          (nativeOpenEvaluation l E f n).hom.app (SX.reduction.obj K) =
        (SY.reductionEvaluation n).hom.app
            ((openExtension (completed l E) f).mapDerivedCategory.obj K) ≫
          (IntegralSystemRealization.openFiniteReduction l E f n).app K ≫
          (sfIntrinsicExtensionByZero f
            (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.map
              ((SX.reductionEvaluation n).inv.app K) := by
  obtain ⟨o, _, _, _⟩ := IntegralSystemRealization.integralSystemOperationModels l E
  obtain ⟨model⟩ := IntegralSystemRealization.integralReductionPullbackModel l E o
  obtain ⟨β₀, hβ₀⟩ := canonicalOpenReduction l E o model f
  let S₀ := pullbackTensorCalculus l E X
  let T₀ := pullbackTensorCalculus l E Y
  let a := S₀.adjunction.leftAdjointUniq SX.adjunction
  let b := T₀.adjunction.leftAdjointUniq SY.adjunction
  let p := (openExtension (completed l E) f).mapDerivedCategory
  let P := ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) f
  let β : p ⋙ SY.reduction ⟶ SX.reduction ⋙ P :=
    Functor.whiskerLeft p b.inv ≫ β₀ ≫ Functor.whiskerRight a.hom P
  refine ⟨β, ?_⟩
  intro K n
  have := sfIntrinsicExtensionByZero_additive f
    (Padic.coefficientExtensionRing l E (n + 1))
  have := (sfIntrinsicExtensionByZero_exact f
    (Padic.coefficientExtensionRing l E (n + 1))).2.1
  have := (sfIntrinsicExtensionByZero_exact f
    (Padic.coefficientExtensionRing l E (n + 1))).2.2
  let EX := coefficientSequenceDerivedEvaluation l E X n
  let EY := coefficientSequenceDerivedEvaluation l E Y n
  let q := (sfIntrinsicExtensionByZero f
    (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory
  have ha : EX.map (a.hom.app K) ≫ (SX.reductionEvaluation n).hom.app K =
      (S₀.reductionEvaluation n).hom.app K := reductionUniq_evaluation l E X S₀ SX K n
  have hb : EY.map (b.hom.app (p.obj K)) ≫
      (SY.reductionEvaluation n).hom.app (p.obj K) =
        (T₀.reductionEvaluation n).hom.app (p.obj K) :=
    reductionUniq_evaluation l E Y T₀ SY (p.obj K) n
  have ha' : (S₀.reductionEvaluation n).inv.app K ≫ EX.map (a.hom.app K) =
      (SX.reductionEvaluation n).inv.app K := by
    apply (cancel_mono ((SX.reductionEvaluation n).hom.app K)).1
    simp only [Category.assoc, ha, Iso.inv_hom_id_app]
  have hb' : EY.map (b.inv.app (p.obj K)) ≫
      (T₀.reductionEvaluation n).hom.app (p.obj K) =
        (SY.reductionEvaluation n).hom.app (p.obj K) := by
    rw [← hb]
    simp only [← EY.map_comp_assoc, b.inv_hom_id_app, EY.map_id, Category.id_comp]
  have hn := (nativeOpenEvaluation l E f n).hom.naturality (a.hom.app K)
  change EY.map (P.map (a.hom.app K)) ≫
      (nativeOpenEvaluation l E f n).hom.app (SX.reduction.obj K) =
    (nativeOpenEvaluation l E f n).hom.app (S₀.reduction.obj K) ≫
      q.map (EX.map (a.hom.app K)) at hn
  change EY.map (β.app K) ≫ _ = _
  dsimp only [β, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [EY.map_comp, Category.assoc]
  rw [hn, reassoc_of% (hβ₀ K n)]
  rw [reassoc_of% hb', ← q.map_comp, ha']

/-- Reduction commutes with the open factor as a map of whole strict systems,
with the scalar-adjunction mate at every finite coordinate.

Source: Stacks 03DI, 0E8I, 0941; Bhatt--Scholze 6.7.6--6.7.7;
the second arrow of the Isomorphism paragraph in the blueprint proof of
`sk-prop-scalar-six-compact-support`.
(blueprint: lem-strict-coefficient-open-reduction).

Proof: Choose flat-term K-flat representatives for the completed input. Extension by zero is exact
and preserves these representatives: it is identity on the open and zero on its complement.
Tensoring this extension with the entire quotient-ring diagram agrees with extension of the
quotient-tensor diagram. The sectionwise comparison sends each tensor generator to the same tensor
in its extension summand. It commutes with every quotient transition because reduction of the
coefficient commutes with that formula. Descend this natural map through homotopies and
quasi-isomorphisms, and use the reductionModel identifications to obtain the displayed strict-system
map. At each finite level its open-adjunction transpose is the scalar-restricted open unit. This is
precisely the mate defining openComparison. The prescribed open evaluation is normalized by that
same unit; the reduction unit normalization fixes both finiteReductionIso factors. Thus the
displayed equation follows before any total limit is taken. This argument works for every ambient
input, without a completeness hypothesis.
The zero input, empty scheme, identity morphism and n=0 (exponent one) obey the same
unit, tensor and quotient equations.
-/
theorem strictCoefficientOpenReduction (f : X ⟶ Y) [IsOpenImmersion f]
    (SX : CoefficientDerivedSystemCalculus l E X)
    (SY : CoefficientDerivedSystemCalculus l E Y) :
    ∃ β : (openExtension (completed l E) f).mapDerivedCategory ⋙ SY.reduction ⟶
        SX.reduction ⋙ ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) f,
      ∀ (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ),
        (coefficientSequenceDerivedEvaluation l E Y n).map (β.app K) ≫
            (strictCoefficientOpenEvaluation l E f n).hom.app (SX.reduction.obj K) =
          ((SY.reductionEvaluation n).hom.app
              ((openExtension (completed l E) f).mapDerivedCategory.obj K) ≫
            (finiteReductionIso l E Y n).inv.app
              ((openExtension (completed l E) f).mapDerivedCategory.obj K)) ≫
            (openComparison (reduction l E (n + 1) (Nat.le_add_left 1 n)) f).app K ≫
            ((openExtension (finite l E (n + 1) (Nat.le_add_left 1 n)) f).mapDerivedCategory).map
              ((finiteReductionIso l E X n).hom.app K ≫
                (SX.reductionEvaluation n).inv.app K) := by
  obtain ⟨β, hβ⟩ := nativeOpenReduction l E f SX SY
  refine ⟨β, ?_⟩
  intro K n
  have := sfIntrinsicExtensionByZero_additive f
    (Padic.coefficientExtensionRing l E (n + 1))
  have := (sfIntrinsicExtensionByZero_exact f
    (Padic.coefficientExtensionRing l E (n + 1))).2.1
  have := (sfIntrinsicExtensionByZero_exact f
    (Padic.coefficientExtensionRing l E (n + 1))).2.2
  let EX := coefficientSequenceDerivedEvaluation l E X n
  let q := (sfIntrinsicExtensionByZero f
    (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory
  let d := Functor.mapDerivedCategoryNatIso (finiteOpenIso l E n f)
  have heval (N : coefficientSequenceDerived l E X) :
      (strictCoefficientOpenEvaluation l E f n).hom.app N =
        (nativeOpenEvaluation l E f n).hom.app N ≫ d.inv.app (EX.obj N) := by
    rfl
  rw [heval, ← Category.assoc, hβ K n]
  have hd := d.inv.naturality
    ((finiteReductionIso l E X n).hom.app K ≫ (SX.reductionEvaluation n).inv.app K)
  simp only [IntegralSystemRealization.openFiniteReduction, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [Category.assoc]
  rw [← q.map_comp_assoc]
  erw [hd]
  erw [Iso.hom_inv_id_app_assoc]

end WeilConjectures
