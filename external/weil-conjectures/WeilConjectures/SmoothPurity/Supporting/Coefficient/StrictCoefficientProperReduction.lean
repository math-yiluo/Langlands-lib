/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeSystemEvaluation

import WeilConjectures.SixFunctors.IntegralSystemRealization.Reduction.IntegralReductionPullbackModel
import WeilConjectures.SixFunctors.IntegralSystemRealization.Proper.IntegralProperFiniteProjection
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperationModels
import WeilConjectures.SmoothPurity.Supporting.NativeProperDerivedPresentation

/-! # Strict coefficient reduction for proper image

Source: Stacks 07A6, 0941; Bhatt--Scholze 6.7.6--6.7.7.
(blueprint: lem-strict-coefficient-proper-reduction). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open PurCompactSupport

section CategoricalComparison

private def comparisonFromLimit
    {A B S T : Type*} [Category A] [Category B] [Category S] [Category T]
    {r : A ⥤ S} {L : S ⥤ A} {s : B ⥤ T} {M : T ⥤ B}
    (a : r ⊣ L) (b : s ⊣ M) (p : A ⥤ B) (P : S ⥤ T)
    (t : P ⋙ M ≅ L ⋙ p) : p ⋙ s ⟶ r ⋙ P :=
  let α : p ⟶ r ⋙ P ⋙ M :=
    Functor.whiskerRight a.unit p ≫ Functor.whiskerLeft r t.inv
  Functor.whiskerRight α s ≫ Functor.whiskerLeft (r ⋙ P) b.counit

private theorem comparisonFromLimit_finite
    {A B S T C D : Type*}
    [Category A] [Category B] [Category S] [Category T] [Category C] [Category D]
    {r : A ⥤ S} {L : S ⥤ A} {s : B ⥤ T} {M : T ⥤ B}
    (a : r ⊣ L) (b : s ⊣ M) (p : A ⥤ B) (P : S ⥤ T)
    (t : P ⋙ M ≅ L ⋙ p)
    (F : A ⥤ C) (H : S ⥤ C) (G : B ⥤ D) (I : T ⥤ D) (q : C ⥤ D)
    (ρ : r ⋙ H ≅ F) (σ : s ⋙ I ≅ G)
    (χ : p ⋙ G ⟶ F ⋙ q) (e : P ⋙ I ⟶ H ⋙ q)
    (ht : ∀ N : S,
      G.map (t.hom.app N) ≫ χ.app (L.obj N) ≫
          q.map (ρ.inv.app (L.obj N) ≫ H.map (a.counit.app N)) =
        σ.inv.app (M.obj (P.obj N)) ≫ I.map (b.counit.app (P.obj N)) ≫ e.app N)
    (K : A) :
    I.map ((comparisonFromLimit a b p P t).app K) ≫ e.app (r.obj K) =
      σ.hom.app (p.obj K) ≫ χ.app K ≫ q.map (ρ.inv.app K) := by
  let α := p.map (a.unit.app K) ≫ t.inv.app (r.obj K)
  have hσ := σ.hom.naturality α
  dsimp only [Functor.comp_map] at hσ
  change I.map (s.map α) ≫ σ.hom.app _ = σ.hom.app _ ≫ G.map α at hσ
  have hβ : I.map ((comparisonFromLimit a b p P t).app K) =
      σ.hom.app (p.obj K) ≫ G.map α ≫
        σ.inv.app (M.obj (P.obj (r.obj K))) ≫
          I.map (b.counit.app (P.obj (r.obj K))) := by
    dsimp only [comparisonFromLimit, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    rw [Functor.map_comp]
    rw [← reassoc_of% hσ]
    simp only [Iso.hom_inv_id_app_assoc]
    rfl
  have htriangle : F.map (a.unit.app K) ≫
      ρ.inv.app (L.obj (r.obj K)) ≫ H.map (a.counit.app (r.obj K)) =
        ρ.inv.app K := by
    have hρ := ρ.inv.naturality (a.unit.app K)
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hρ
    rw [← Category.assoc, hρ, Category.assoc]
    change ρ.inv.app K ≫ H.map (r.map (a.unit.app K)) ≫
      H.map (a.counit.app (r.obj K)) = _
    rw [← H.map_comp, a.left_triangle_components, H.map_id]
    exact Category.comp_id (ρ.inv.app K)
  rw [hβ]
  simp only [α, Functor.map_comp, Category.assoc]
  rw [← ht (r.obj K)]
  rw [← G.map_comp_assoc (t.inv.app (r.obj K)) (t.hom.app (r.obj K)),
    t.inv_hom_id_app, G.map_id, Category.id_comp]
  have hχ := χ.naturality (a.unit.app K)
  dsimp only [Functor.comp_map] at hχ
  rw [reassoc_of% hχ]
  rw [← q.map_comp, htriangle]

private theorem normalizedLeftAdjointUniq
    {A S C : Type*} [Category A] [Category S] [Category C]
    {r s : A ⥤ S} {L : S ⥤ A} (a : r ⊣ L) (b : s ⊣ L)
    (E : S ⥤ C) {F : A ⥤ C} {U : C ⥤ A} (c : F ⊣ U)
    (π : L ⟶ E ⋙ U) (ρ : r ⋙ E ≅ F) (σ : s ⋙ E ≅ F)
    (ha : ∀ K, a.unit.app K ≫ π.app (r.obj K) =
      c.unit.app K ≫ U.map (ρ.inv.app K))
    (hb : ∀ K, b.unit.app K ≫ π.app (s.obj K) =
      c.unit.app K ≫ U.map (σ.inv.app K)) (K : A) :
    E.map ((a.leftAdjointUniq b).hom.app K) ≫ σ.hom.app K = ρ.hom.app K := by
  have h : ρ.inv.app K ≫ E.map ((a.leftAdjointUniq b).hom.app K) =
      σ.inv.app K := by
    apply (c.homEquiv _ _).injective
    simp only [Adjunction.homEquiv_unit, U.map_comp]
    rw [← Category.assoc, ← ha K]
    have hπ := π.naturality ((a.leftAdjointUniq b).hom.app K)
    dsimp only [Functor.comp_map] at hπ
    rw [Category.assoc, ← hπ]
    rw [← Category.assoc, a.unit_leftAdjointUniq_hom_app b K]
    exact hb K
  apply (cancel_epi (ρ.inv.app K)).1
  simp only [← Category.assoc, h, Iso.inv_hom_id_app]

end CategoricalComparison

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {X Y : Scheme.{u}}

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
  exact normalizedLeftAdjointUniq S.adjunction T.adjunction
    (coefficientSequenceDerivedEvaluation l E W n) (coefficientFiniteAdjunction l E W n)
    (coefficientSequenceProjection l E W n) (S.reductionEvaluation n)
    (T.reductionEvaluation n) (fun K ↦ S.unit_projection K n)
    (fun K ↦ T.unit_projection K n) K

private theorem canonicalProperReduction
    (o : IntegralSystemRealization.Operations l E)
    (model : IntegralSystemRealization.RealizationModel l E o) (f : X ⟶ Y) :
    ∃ β : push (completed l E) f ⋙ (pullbackTensorCalculus l E Y).reduction ⟶
        (pullbackTensorCalculus l E X).reduction ⋙
          IntegralSystemRealization.Operations.push l E o f,
      ∀ (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ),
        (coefficientSequenceDerivedEvaluation l E Y n).map (β.app K) ≫
            ((o.evaluation f).evaluation n).hom.app
              ((pullbackTensorCalculus l E X).reduction.obj K) =
          ((pullbackTensorCalculus l E Y).reductionEvaluation n).hom.app
              ((push (completed l E) f).obj K) ≫
            (IntegralSystemRealization.properFiniteReduction l E f n).app K ≫
            (proEtaleConstantDerivedDirectImage f
              (Padic.coefficientExtensionRing l E (n + 1))).map
                (((pullbackTensorCalculus l E X).reductionEvaluation n).inv.app K) := by
  let SX := pullbackTensorCalculus l E X
  let SY := pullbackTensorCalculus l E Y
  let p : DerivedCategory (scalarReductionSource l E X) ⥤
      DerivedCategory (scalarReductionSource l E Y) := push (completed l E) f
  let P := IntegralSystemRealization.Operations.push l E o f
  let t := model.push l E f
  refine ⟨comparisonFromLimit SX.adjunction SY.adjunction p P t, ?_⟩
  intro K n
  exact comparisonFromLimit_finite SX.adjunction SY.adjunction p P t
    (scalarReductionDerivedExtension l E X n)
    (coefficientSequenceDerivedEvaluation l E X n)
    (scalarReductionDerivedExtension l E Y n)
    (coefficientSequenceDerivedEvaluation l E Y n)
    (proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (n + 1)))
    (SX.reductionEvaluation n) (SY.reductionEvaluation n)
    (IntegralSystemRealization.properFiniteReduction l E f n)
    ((o.evaluation f).evaluation n).hom
    (fun N ↦ IntegralSystemRealization.integralProperFiniteProjection l E o model f N n) K

private theorem nativeProperReduction (f : X ⟶ Y)
    (SX : CoefficientDerivedSystemCalculus l E X)
    (SY : CoefficientDerivedSystemCalculus l E Y) :
    ∃ β : push (completed l E) f ⋙ SY.reduction ⟶
        SX.reduction ⋙ ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) f,
      ∀ (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ),
        (coefficientSequenceDerivedEvaluation l E Y n).map (β.app K) ≫
            (nativeProperConstantEvaluation l E f n).hom.app (SX.reduction.obj K) =
          (SY.reductionEvaluation n).hom.app ((push (completed l E) f).obj K) ≫
            (IntegralSystemRealization.properFiniteReduction l E f n).app K ≫
            (proEtaleConstantDerivedDirectImage f
              (Padic.coefficientExtensionRing l E (n + 1))).map
                ((SX.reductionEvaluation n).inv.app K) := by
  obtain ⟨o, _, _, _⟩ := IntegralSystemRealization.integralSystemOperationModels l E
  obtain ⟨model⟩ := IntegralSystemRealization.integralReductionPullbackModel l E o
  obtain ⟨β₀, hβ₀⟩ := canonicalProperReduction l E o model f
  obtain ⟨e, he⟩ := nativeProperDerivedPresentation l E o f
  let S₀ := pullbackTensorCalculus l E X
  let T₀ := pullbackTensorCalculus l E Y
  let a := S₀.adjunction.leftAdjointUniq SX.adjunction
  let b := T₀.adjunction.leftAdjointUniq SY.adjunction
  let p : DerivedCategory (scalarReductionSource l E X) ⥤
      DerivedCategory (scalarReductionSource l E Y) := push (completed l E) f
  let P := ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) f
  let β : p ⋙ SY.reduction ⟶ SX.reduction ⋙ P :=
    Functor.whiskerLeft p b.inv ≫ β₀ ≫
      Functor.whiskerLeft S₀.reduction e.hom ≫ Functor.whiskerRight a.hom P
  refine ⟨β, ?_⟩
  intro K n
  let EX := coefficientSequenceDerivedEvaluation l E X n
  let EY := coefficientSequenceDerivedEvaluation l E Y n
  let q := proEtaleConstantDerivedDirectImage f
    (Padic.coefficientExtensionRing l E (n + 1))
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
  have hn := (nativeProperConstantEvaluation l E f n).hom.naturality (a.hom.app K)
  change EY.map (P.map (a.hom.app K)) ≫
      (nativeProperConstantEvaluation l E f n).hom.app (SX.reduction.obj K) =
    (nativeProperConstantEvaluation l E f n).hom.app (S₀.reduction.obj K) ≫
      q.map (EX.map (a.hom.app K)) at hn
  change EY.map (β.app K) ≫ _ = _
  dsimp only [β, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [EY.map_comp, Category.assoc]
  rw [hn, reassoc_of% (he (S₀.reduction.obj K) n)]
  rw [reassoc_of% (hβ₀ K n)]
  rw [reassoc_of% hb', ← q.map_comp, ha']

/-- Native evaluation in the finite ringed proper-image presentation.
Source: Stacks 03DI, 0D6E (blueprint: lem-strict-coefficient-proper-reduction). -/
def strictCoefficientProperEvaluation (f : X ⟶ Y) (n : ℕ) :
    ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f ⋙
      coefficientSequenceDerivedEvaluation l E Y n ≅
    coefficientSequenceDerivedEvaluation l E X n ⋙
      push (finite l E (n + 1) (Nat.le_add_left 1 n)) f := by
  have := proEtaleConstantModuleDirectImage_additive f
    (Padic.coefficientExtensionRing l E (n + 1))
  let e := ProEtale.VaryingRing.evalP (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) f n ≪≫
    Functor.isoWhiskerLeft _ (Functor.rightDerivedFunctorNatIso
      (compactSupportDirectModel f (Padic.coefficientExtensionRing l E (n + 1))))
  exact e ≪≫ Functor.isoWhiskerLeft _
    (Functor.rightDerivedFunctorNatIso (eqToIso (finiteDirectImage_eq l E n f))).symm

/-- Reduction commutes with the proper factor as a map of whole strict systems,
with the scalar-adjunction mate at every finite coordinate.

Source: Stacks 07A6, 0B56, 0941; Bhatt--Scholze 6.7.6--6.7.7;
the first arrow of the Isomorphism paragraph in the blueprint proof of
`sk-prop-scalar-six-compact-support`.
(blueprint: lem-strict-coefficient-proper-reduction).

Proof: Use the canonical completed-to-quotient tensor/pullback square on the sequence site. Its
inverse, transposed under the geometric pullback/direct-image adjunctions, defines the displayed map
on the entire derived system. Compute using flat-term K-flat representatives for tensor and
K-injectives for direct image; the canonical restriction/direct-image comparison is normalized on
these replacements. Evaluation is exact, and its direct-image comparison is the mate of its pullback
comparison. Pasting these adjunction squares identifies evaluation of the constructed mate with
properComparison. The reductionModel and unit_projection equations fix the endpoint coordinate
changes as reductionEvaluation followed by finiteReductionIso inverse. The adjunction triangle
identities give the displayed equality. No isomorphism assertion for the proper scalar comparison is
needed, and no equality is inferred from faithfulness of finite evaluation.
The zero input, empty scheme, identity morphism and n=0 (exponent one) obey the same
unit, tensor and quotient equations.
-/
theorem strictCoefficientProperReduction (f : X ⟶ Y)
    (SX : CoefficientDerivedSystemCalculus l E X)
    (SY : CoefficientDerivedSystemCalculus l E Y) :
    ∃ β : push (completed l E) f ⋙ SY.reduction ⟶
        SX.reduction ⋙ ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) f,
      ∀ (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ),
        (coefficientSequenceDerivedEvaluation l E Y n).map (β.app K) ≫
            (strictCoefficientProperEvaluation l E f n).hom.app (SX.reduction.obj K) =
          ((SY.reductionEvaluation n).hom.app ((push (completed l E) f).obj K) ≫
              (finiteReductionIso l E Y n).inv.app ((push (completed l E) f).obj K)) ≫
            (properComparison (reduction l E (n + 1) (Nat.le_add_left 1 n)) f).app K ≫
            (push (finite l E (n + 1) (Nat.le_add_left 1 n)) f).map
              ((finiteReductionIso l E X n).hom.app K ≫
                (SX.reductionEvaluation n).inv.app K) := by
  obtain ⟨β, hβ⟩ := nativeProperReduction l E f SX SY
  refine ⟨β, ?_⟩
  intro K n
  have := proEtaleConstantModuleDirectImage_additive f
    (Padic.coefficientExtensionRing l E (n + 1))
  let EX := coefficientSequenceDerivedEvaluation l E X n
  let q := proEtaleConstantDerivedDirectImage f
    (Padic.coefficientExtensionRing l E (n + 1))
  let d := Functor.rightDerivedFunctorNatIso (eqToIso (finiteDirectImage_eq l E n f))
  have heval (N : coefficientSequenceDerived l E X) :
      (strictCoefficientProperEvaluation l E f n).hom.app N =
        (nativeProperConstantEvaluation l E f n).hom.app N ≫ d.inv.app (EX.obj N) := by
    rfl
  rw [heval, ← Category.assoc, hβ K n]
  have hd := d.inv.naturality
    ((finiteReductionIso l E X n).hom.app K ≫ (SX.reductionEvaluation n).inv.app K)
  simp only [IntegralSystemRealization.properFiniteReduction, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [Category.assoc]
  rw [← q.map_comp_assoc]
  erw [hd]
  erw [Iso.hom_inv_id_app_assoc]

end WeilConjectures
