/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels

import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.TraceFormula.Coherent.CoherentQuotientOrdinaryLift

/-! # Successor compatibility of normalized ordinary pullback comparisons

Source: Stacks 03D2, 0941 and 099N(5), strict quotient-system transitions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local irreducible] Functor.leftAdjoint limit constantSheaf
  HasDerivedCategory.standard coefficientSequenceRestriction scalarReductionExtension
  completedIntegralCommRingProjectionUnrestricted
  coefficientSequenceCommRingSheaf
  integralComparisonSequenceRingMap scalarReductionExistence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

namespace OrdinarySuccessorProof

section UnderlyingMaps
universe a b c d r
variable {C : Type a} [Category.{b} C] {R : Cᵒᵖ ⥤ RingCat.{r}}

private def moduleMap (M : PresheafOfModules.{r} R) {U V : Cᵒᵖ} (h : U ⟶ V) :
    M.obj U → M.obj V := fun x ↦ M.presheaf.map h x

private theorem moduleMap_heq (M : PresheafOfModules.{r} R)
    {U V : Cᵒᵖ} (h : U ⟶ V) :
    HEq (fun x ↦ M.map h x) (moduleMap M h) := by rfl

private theorem moduleMap_naturality {M N : PresheafOfModules.{r} R} (f : M ⟶ N)
    {U V : Cᵒᵖ} (h : U ⟶ V) (x : M.obj U) :
    moduleMap N h (f.app U x) = f.app V (moduleMap M h x) := by
  exact (PresheafOfModules.naturality_apply f h x).symm

private theorem moduleMap_pushforward
    {D : Type c} [Category.{d} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K]
    {S : Sheaf J RingCat.{r}} {T : Sheaf K RingCat.{r}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj T)
    (M : SheafOfModules.{r} T) {U V : Cᵒᵖ} (h : U ⟶ V)
    (x : M.val.obj (F.op.obj U)) :
    moduleMap ((SheafOfModules.pushforward φ).obj M).val h x =
      moduleMap M.val (F.op.map h) x := by rfl

end UnderlyingMaps

section PullbackGeneration
universe a b c d r
variable {C : Type a} [Category.{b} C] {D : Type c} [Category.{d} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : C ⥤ D) [F.IsContinuous J K]
  {S : Sheaf J RingCat.{r}} {R R₀ R₁ : Sheaf K RingCat.{r}}
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R₀)
  (L : SheafOfModules.{r} S ⥤ SheafOfModules.{r} R₀)
  (adj : L ⊣ SheafOfModules.pushforward φ)
  (π : R ⟶ R₀) (β : R ⟶ R₁) (q : R₀ ⟶ R₁) (hq : π ≫ q = β)
  [Presheaf.IsLocallySurjective K π.hom]

include q hq in
private theorem restrictedPullback_hom_ext
    (M : SheafOfModules.{r} S) (N : SheafOfModules.{r} R₁)
    (T : Cᵒᵖ → Type r) (s : ∀ U, T U → M.val.obj U)
    (hgen : ∀ (B : SheafOfModules.{r} S) (c d : M ⟶ B),
      (∀ U x, c.val.app U (s U x) = d.val.app U (s U x)) → c = d)
    (a b : (SheafOfModules.restrictScalars π).obj (L.obj M) ⟶
      (SheafOfModules.restrictScalars β).obj N)
    (hab : ∀ U x,
      a.val.app (F.op.obj U) ((adj.unit.app M).val.app U (s U x)) =
        b.val.app (F.op.obj U) ((adj.unit.app M).val.app U (s U x))) : a = b := by
  let lift := SheafOfModules.IntegralScalarProof.liftMap π β q hq (L.obj M) N
  have he : lift a = lift b := by
    apply (adj.homEquiv _ _).injective
    apply hgen
    intro U x
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    exact hab U x
  ext U x
  exact congrArg (fun k ↦ k.val.app U x) he

end PullbackGeneration

attribute [local irreducible] moduleMap

private theorem heq_apply {A A' : Type v} {B B' : Type w} (hB : B = B')
    (f : A → B) (g : A' → B') (h : HEq f g)
    {x : A} {y : A'} (hxy : HEq x y) : HEq (f x) (g y) := by
  cases hB
  cases hxy
  cases h
  rfl

private def restrictedArrow {X : Scheme.{t}}
    (N : coefficientSequenceModules l E X) {m n : ℕ} (h : n ≤ m)
    (U : X.ProEtᵒᵖ) :
    (((coefficientSequenceRestriction l E X).obj N).obj (op m)).val.obj U →
      (((coefficientSequenceRestriction l E X).obj N).obj (op n)).val.obj U :=
  fun x ↦ ((((coefficientSequenceRestriction l E X).obj N).map
    (homOfLE h).op).val.app U) x

private def sequenceArrow {X : Scheme.{t}}
    (N : coefficientSequenceModules l E X) {m n : ℕ} (h : n ≤ m)
    (U : X.ProEtᵒᵖ) : N.val.obj (op (m, U.unop)) → N.val.obj (op (n, U.unop)) :=
  moduleMap N.val (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op

attribute [local irreducible] restrictedArrow sequenceArrow

private theorem restriction_horizontal_heq {X : Scheme.{t}}
    (N : coefficientSequenceModules l E X) {m n : ℕ} (h : n ≤ m)
    (U : X.ProEtᵒᵖ) :
    HEq (restrictedArrow l E N h U) (sequenceArrow l E N h U) := by
  unfold restrictedArrow sequenceArrow coefficientSequenceRestriction
  exact ((coefficientSequenceRestriction_exists l E X).exists.choose_spec.2.1
    N m n h U).trans (moduleMap_heq N.val _)

private theorem restriction_horizontal {X : Scheme.{t}}
    (N : coefficientSequenceModules l E X) {m n : ℕ} (h : n ≤ m)
    (U : X.ProEtᵒᵖ) (x : N.val.obj (op (m, U.unop))) :
    restrictedArrow l E N h U (integralComparisonRestrictedSection l E X N m U x) =
      integralComparisonRestrictedSection l E X N n U (sequenceArrow l E N h U x) := by
  apply eq_of_heq
  exact (heq_apply (integralComparisonRestrictedSectionType l E X N n U)
    _ _ (restriction_horizontal_heq l E N h U) (cast_heq _ x)).trans
      (cast_heq _ _).symm

private theorem restrictionEvaluation_section {X : Scheme.{t}}
    (N : coefficientSequenceModules l E X) (n : ℕ) (U : X.ProEtᵒᵖ)
    (x : N.val.obj (op (n, U.unop))) :
    (((eqToIso (coefficientSequenceRestriction_evaluation l E X n)).app N).hom.val.app U)
      (integralComparisonRestrictedSection l E X N n U x) =
        coefficientEvaluationSection l E X N n U x := by
  simp only [Iso.app_hom, eqToIso.hom, eqToHom_app]
  apply eq_of_heq
  have hc {A B : scalarReductionSource l E X} (h : A = B) (y : A.val.obj U) :
      HEq ((eqToHom h).val.app U y) y := by
    subst B
    rfl
  exact ((hc _ _).trans (cast_heq _ _)).trans (HEq.rfl).symm

private def moduleUnit {Y : Scheme.{t}} (M : CompletionUnit.OrdinaryModel l E Y)
    (A : scalarReductionSource l E Y) (n : ℕ) :
    A ⟶ ((coefficientSequenceRestriction l E Y).obj (M.tensor.obj A)).obj (op n) :=
  M.adjunction.unit.app A ≫
    limit.π ((coefficientSequenceRestriction l E Y).obj (M.tensor.obj A)) (op n)

private def unitSection {Y : Scheme.{t}} (M : CompletionUnit.OrdinaryModel l E Y)
    (A : scalarReductionSource l E Y) (n : ℕ) (U : Y.ProEtᵒᵖ) (x : A.val.obj U) :
    (M.tensor.obj A).val.obj (op (n, U.unop)) :=
  cast (integralComparisonRestrictedSectionType l E Y (M.tensor.obj A) n U)
    ((moduleUnit l E M A n).val.app U x)

private theorem unitSection_restricted {Y : Scheme.{t}}
    (M : CompletionUnit.OrdinaryModel l E Y) (A : scalarReductionSource l E Y)
    (n : ℕ) (U : Y.ProEtᵒᵖ) (x : A.val.obj U) :
    integralComparisonRestrictedSection l E Y (M.tensor.obj A) n U
        (unitSection l E M A n U x) = (moduleUnit l E M A n).val.app U x := by
  exact (Equiv.cast
    (integralComparisonRestrictedSectionType l E Y (M.tensor.obj A) n U)).symm_apply_apply _

private theorem moduleUnit_evaluation {Y : Scheme.{t}}
    (M : CompletionUnit.OrdinaryModel l E Y) (A : scalarReductionSource l E Y)
    (n : ℕ) (U : Y.ProEtᵒᵖ) (x : A.val.obj U) :
    ((M.evaluation n).hom.app A).val.app U
        ((((eqToIso (coefficientSequenceRestriction_evaluation l E Y n)).app
          (M.tensor.obj A)).hom.val.app U) ((moduleUnit l E M A n).val.app U x)) =
      unrestrictedIntegralTensorSection l E Y n A U 1 x := by
  exact M.unit_tensor A n U x

attribute [local irreducible] moduleUnit unitSection

private theorem unitSection_evaluation {Y : Scheme.{t}}
    (M : CompletionUnit.OrdinaryModel l E Y) (A : scalarReductionSource l E Y)
    (n : ℕ) (U : Y.ProEtᵒᵖ) (x : A.val.obj U) :
    ((M.evaluation n).hom.app A).val.app U
        (coefficientEvaluationSection l E Y (M.tensor.obj A) n U
          (unitSection l E M A n U x)) =
      unrestrictedIntegralTensorSection l E Y n A U 1 x := by
  have hs := restrictionEvaluation_section l E (M.tensor.obj A) n U
    (unitSection l E M A n U x)
  have ht := congrArg
    (((eqToIso (coefficientSequenceRestriction_evaluation l E Y n)).app
      (M.tensor.obj A)).hom.val.app U) (unitSection_restricted l E M A n U x)
  exact (congrArg (((M.evaluation n).hom.app A).val.app U) (hs.symm.trans ht)).trans
    (moduleUnit_evaluation l E M A n U x)

private theorem unitSection_horizontal {Y : Scheme.{t}}
    (M : CompletionUnit.OrdinaryModel l E Y) (A : scalarReductionSource l E Y)
    {m n : ℕ} (h : n ≤ m) (U : Y.ProEtᵒᵖ) (x : A.val.obj U) :
    moduleMap (M.tensor.obj A).val (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op
        (unitSection l E M A m U x) = unitSection l E M A n U x := by
  apply (Equiv.cast
    (integralComparisonRestrictedSectionType l E Y (M.tensor.obj A) n U).symm).injective
  change integralComparisonRestrictedSection l E Y (M.tensor.obj A) n U _ =
    integralComparisonRestrictedSection l E Y (M.tensor.obj A) n U _
  have hh := restriction_horizontal l E (M.tensor.obj A) h U
    (unitSection l E M A m U x)
  simp only [sequenceArrow] at hh
  erw [← hh, unitSection_restricted, unitSection_restricted]
  have hu : moduleUnit l E M A m ≫
      ((coefficientSequenceRestriction l E Y).obj (M.tensor.obj A)).map
        (homOfLE h).op = moduleUnit l E M A n := by
    simp only [moduleUnit, Category.assoc, limit.w]
  simpa only [restrictedArrow, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ConcreteCategory.comp_apply] using congrArg (fun a ↦ a.val.app U x) hu

private theorem directImage_moduleMap {X Y : Scheme.{t}} (f : X ⟶ Y)
    (N : coefficientSequenceModules l E X)
    {U V : (ℕ × Y.ProEt)ᵒᵖ} (h : U ⟶ V)
    (x : N.val.obj ((integralComparisonSequenceBaseChange f).op.obj U)) :
    moduleMap ((integralComparisonSequenceDirectImage l E f).obj N).val h x =
      moduleMap N.val ((integralComparisonSequenceBaseChange f).op.map h) x := by
  exact moduleMap_pushforward _ N h x

private theorem sequenceGenerator_horizontal {X Y : Scheme.{t}} (f : X ⟶ Y)
    (N : coefficientSequenceModules l E Y) {m n : ℕ} (h : n ≤ m)
    (U : Y.ProEt) (x : N.val.obj (op (m, U))) :
    moduleMap ((integralComparisonSequencePullback l E f).obj N).val
        (Prod.mkHom (homOfLE h) (𝟙 ((proEtaleBaseChange f).obj U))).op
        (integralComparisonSequenceGenerator l E f N m U x) =
      integralComparisonSequenceGenerator l E f N n U
        (moduleMap N.val (Prod.mkHom (homOfLE h) (𝟙 U)).op x) := by
  have H := moduleMap_naturality
    ((Adjunction.ofIsRightAdjoint
      (integralComparisonSequenceDirectImage l E f)).unit.app N).val
      (Prod.mkHom (homOfLE h) (𝟙 U)).op x
  dsimp only [Functor.comp_obj, Functor.id_obj] at H
  rw [directImage_moduleMap] at H
  have hh : (integralComparisonSequenceBaseChange f).map
      (Prod.mkHom (homOfLE h) (𝟙 U)) =
      Prod.mkHom (homOfLE h) (𝟙 ((proEtaleBaseChange f).obj U)) := by
    ext <;> simp [integralComparisonSequenceBaseChange]
  change moduleMap ((integralComparisonSequencePullback l E f).obj N).val
    ((integralComparisonSequenceBaseChange f).map
      (Prod.mkHom (homOfLE h) (𝟙 U))).op _ = _ at H
  rw [hh] at H
  exact H

private theorem reduction_hom_ext {Y : Scheme.{t}} (n : ℕ)
    (A : scalarReductionSource l E Y) (B : scalarReductionTarget l E Y n)
    (a b : (scalarReductionExtension l E Y n).obj A ⟶ B)
    (h : ∀ (U : Y.ProEtᵒᵖ) (x : A.val.obj U),
      a.val.app U (unrestrictedIntegralTensorSection l E Y n A U 1 x) =
      b.val.app U (unrestrictedIntegralTensorSection l E Y n A U 1 x)) : a = b := by
  let adj := (scalarReductionExtension_adjunction l E Y n).choose
  apply (adj.homEquiv A B).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext U x
  change a.val.app U ((adj.unit.app A).val.app U x) =
    b.val.app U ((adj.unit.app A).val.app U x)
  dsimp only [adj]
  rw [scalarUnit_tensor]
  exact h U x

private abbrev finiteRestriction (X : Scheme.{t}) (n : ℕ) :=
  SheafOfModules.restrictScalars
    ((integralOperationsForgetSheaf (ProEt.topology X)).map
      (completedIntegralCommRingProjectionUnrestricted l E X n))

private theorem pullback_tensor_hom_ext {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ)
    (A : scalarReductionSource l E Y)
    (N : integralOperationsFiniteModules l E X n)
    (a b : (finiteRestriction l E X (n + 1)).obj
        ((integralOperationsLevelPullback l E f (n + 1)).obj
          ((scalarReductionExtension l E Y (n + 1)).obj A)) ⟶
      (finiteRestriction l E X n).obj N)
    (hab : ∀ (U : Y.ProEt) (x : A.val.obj (op U)),
      a.val.app (op ((proEtaleBaseChange f).obj U))
          (integralOperationsPullbackGenerator l E f (n + 1) _ U
            (unrestrictedIntegralTensorSection l E Y (n + 1) A (op U) 1 x)) =
      b.val.app (op ((proEtaleBaseChange f).obj U))
          (integralOperationsPullbackGenerator l E f (n + 1) _ U
            (unrestrictedIntegralTensorSection l E Y (n + 1) A (op U) 1 x))) : a = b := by
  let π := (integralOperationsForgetSheaf (ProEt.topology X)).map
    (completedIntegralCommRingProjectionUnrestricted l E X (n + 1))
  let β := (integralOperationsForgetSheaf (ProEt.topology X)).map
    (completedIntegralCommRingProjectionUnrestricted l E X n)
  let q := integralCoefficientSheafTransition l E X n
  let hq := integralProjection_step l E X n
  let : Presheaf.IsLocallySurjective (ProEt.topology X) π.hom :=
    completedProjection_locallySurjective l E X (n + 1)
  refine restrictedPullback_hom_ext (proEtaleBaseChange f)
    (integralOperationsDirectRingMap l E f (n + 1))
    (integralOperationsLevelPullback l E f (n + 1))
    (integralOperationsPullbackAdjunction l E f (n + 1)) π β q hq
    ((scalarReductionExtension l E Y (n + 1)).obj A) N
    (fun U ↦ A.val.obj U)
    (fun U x ↦ unrestrictedIntegralTensorSection l E Y (n + 1) A U 1 x) ?_ a b ?_
  · intro B c d hc
    exact reduction_hom_ext l E (n + 1) A B c d hc
  · intro U x
    exact hab U.unop x

end OrdinarySuccessorProof

open OrdinarySuccessorProof

attribute [local irreducible] integralOperationsPullbackGenerator
  unrestrictedIntegralTensorSection

-- The generator-level computation through the pullback tower is expensive.
/-- Normalized level comparisons intertwine the two actual successor maps.
Source: Stacks sites-modules.tex, inverse-image adjunction (03D7), and
sites-cohomology.tex, strict sequence limits (0941), applied to the finite
quotient system of proetale.tex, 099N(5).
(blueprint: lem-trf-ordinary-quotient-pullback-successor).

Proof: conjugate the source successor by the two level comparisons. Local
surjectivity of the completed coefficient projection makes completed-linear maps
between the finite modules finite-linear. The finite inverse-image adjunction
and the scalar-reduction adjunction detect their equality on pullback images of
1 tensor x. For each x, the ordinary adjunction unit followed by the inverse-limit
projections gives compatible sequence sections. Their finite evaluations are
1 tensor x by M.unit_tensor. Naturality of the sequence inverse-image unit gives
compatible pullback generators of these sections. The normalization of e sends
them to the finite pullback generators of 1 tensor x, so the conjugated source
successor sends the higher generator to the lower one. The defining generator
equation of integralOperationsPullbackTransition and the tensor formula for
unrestrictedIntegralTransition give the same result, since coefficient reduction
preserves 1. Equality on these generators proves the conjugated square, and
cancellation proves the assertion. The argument is degreewise, includes n=0 and
zero terms, and uses no boundedness or flatness assumption. -/
theorem ordinaryQuotientPullback_successor {X Y : Scheme.{t}} (f : X ⟶ Y)
    (M : CompletionUnit.OrdinaryModel l E Y)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) :
    let T := (integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ) ⋙
      (coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.complexOfFunctorsToFunctorToComplex
    ∀ (e : ∀ n : ℕ, (T.obj ((M.quotient l E Y).obj P)).obj (op n) ≅
        ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n)),
      (∀ (n : ℕ) (i : ℤ) (U : Y.ProEt)
        (x : (M.tensor.obj (P.X i)).val.obj (op (n, U))),
        (((e n).hom.f i).val.app (op ((proEtaleBaseChange f).obj U)))
          (integralComparisonRestrictedSection l E X
            ((integralComparisonSequencePullback l E f).obj (M.tensor.obj (P.X i))) n
            (op ((proEtaleBaseChange f).obj U))
            (integralComparisonSequenceGenerator l E f (M.tensor.obj (P.X i)) n U x)) =
          integralOperationsPullbackGenerator l E f n
            ((scalarReductionExtension l E Y n).obj (P.X i)) U
            (((M.evaluation n).hom.app (P.X i)).val.app (op U)
              (coefficientEvaluationSection l E Y (M.tensor.obj (P.X i)) n (op U) x))) →
      ∀ n : ℕ,
        (T.obj ((M.quotient l E Y).obj P)).map (homOfLE (Nat.le_succ n)).op ≫
            (e n).hom =
          (e (n + 1)).hom ≫
            ((integralOperationsPullbackTowerFunctor l E f).obj P).map
              (homOfLE (Nat.le_succ n)).op  := by
  intro T e he n
  apply (cancel_epi (e (n + 1)).inv).mp
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  apply HomologicalComplex.hom_ext
  intro i
  apply pullback_tensor_hom_ext l E f n (P.X i)
  intro U x
  let N := M.tensor.obj (P.X i)
  let g (k : ℕ) := integralComparisonRestrictedSection l E X
    ((integralComparisonSequencePullback l E f).obj N) k
    (op ((proEtaleBaseChange f).obj U))
    (integralComparisonSequenceGenerator l E f N k U
      (unitSection l E M (P.X i) k (op U) x))
  let z (k : ℕ) := integralOperationsPullbackGenerator l E f k
    ((scalarReductionExtension l E Y k).obj (P.X i)) U
    (unrestrictedIntegralTensorSection l E Y k (P.X i) (op U) 1 x)
  have hg (k : ℕ) : ((e k).hom.f i).val.app
      (op ((proEtaleBaseChange f).obj U)) (g k) = z k := by
    dsimp only [g, z, N]
    rw [he, unitSection_evaluation]
  have hinv : ((e (n + 1)).inv.f i).val.app
      (op ((proEtaleBaseChange f).obj U)) (z (n + 1)) = g (n + 1) := by
    rw [← hg]
    exact congrArg (fun a ↦ (a.f i).val.app
      (op ((proEtaleBaseChange f).obj U)) (g (n + 1))) (e (n + 1)).hom_inv_id
  have ht : (((T.obj ((M.quotient l E Y).obj P)).map
      (homOfLE (Nat.le_succ n)).op).f i).val.app
      (op ((proEtaleBaseChange f).obj U)) (g (n + 1)) = g n := by
    change ((((coefficientSequenceRestriction l E X).obj
      ((integralComparisonSequencePullback l E f).obj N)).map
        (homOfLE (Nat.le_succ n)).op).val.app _) _ = _
    change restrictedArrow l E ((integralComparisonSequencePullback l E f).obj N)
      (Nat.le_succ n) (op ((proEtaleBaseChange f).obj U)) (g (n + 1)) = g n
    dsimp only [g]
    rw [restriction_horizontal]
    dsimp only [sequenceArrow]
    rw [sequenceGenerator_horizontal, unitSection_horizontal]
  have hτ : ((((integralOperationsPullbackTowerFunctor l E f).obj P).map
      (homOfLE (Nat.le_succ n)).op).f i).val.app
      (op ((proEtaleBaseChange f).obj U)) (z (n + 1)) = z n := by
    have h := (integralOperationsPullbackTransition_existsUnique l E f n).exists.choose_spec
      P i U (unrestrictedIntegralTensorSection l E Y (n + 1) (P.X i) (op U) 1 x)
    have hr := (unrestrictedIntegralTransition_existsUnique l E Y n).exists.choose_spec
      P i (op U) 1 x
    have h1 : (integralCoefficientSheafTransition l E Y n).hom.app (op U) 1 = 1 :=
      map_one ((integralCoefficientSheafTransition l E Y n).hom.app (op U)).hom
    erw [h1] at hr
    simp only [integralOperationsPullbackTowerFunctor, Functor.flip_obj_map,
      Functor.ofOpSequence_map_homOfLE_succ]
    erw [hr] at h
    dsimp only [integralOperationsPullbackTransition, z,
      unrestrictedIntegralFiniteComplex, Functor.mapHomologicalComplex_obj_X,
      unrestrictedIntegralReductionFunctor, Functor.flip_obj_obj,
      Functor.ofOpSequence_obj] at h ⊢
    exact h
  change ((e n).hom.f i).val.app _
      ((((T.obj ((M.quotient l E Y).obj P)).map
        (homOfLE (Nat.le_succ n)).op).f i).val.app _
          (((e (n + 1)).inv.f i).val.app _ (z (n + 1)))) =
    ((((integralOperationsPullbackTowerFunctor l E f).obj P).map
      (homOfLE (Nat.le_succ n)).op).f i).val.app _ (z (n + 1))
  erw [hinv, ht, hg, hτ]

end WeilConjectures
