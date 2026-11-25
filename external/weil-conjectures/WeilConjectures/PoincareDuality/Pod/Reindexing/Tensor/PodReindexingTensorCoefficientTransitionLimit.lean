/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexCoefficientTransition

/-! # Limit square component of the normalized coefficient transition

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL, 06YY, 0941
(blueprint: lem-pod-reindexing-tensor-coefficient-transition-core-limit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem scalarLimitMate
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{u})
    (ρ : IntegralComparisonRoosModel l L W)
    (S : IntegralComparisonScalarModel l E L ι W (podReindexCalculus l E W) ρ)
    (N : coefficientSequenceDerived l E W) :
    (podReindexCalculus l L W).reduction.map (podScalarLimit l E L ι W ρ S N) ≫
        (podReindexCalculus l L W).adjunction.counit.app
          ((integralComparisonDerivedSequenceScalar l E L ι W).obj N) =
      (podScalarReduction l E L ι W ρ S).app ((coefficientSequenceLimit l E W).obj N) ≫
        (integralComparisonDerivedSequenceScalar l E L ι W).map
          ((podReindexCalculus l E W).adjunction.counit.app N) := by
  dsimp only [podScalarLimit, podScalarReduction, integralComparisonScalarCounit,
    NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (podReindexCalculus l L W).adjunction.counit.naturality
    ((integralComparisonDerivedSequenceScalar l E L ι W).map
      ((podReindexCalculus l E W).adjunction.counit.app N))
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  exact congrArg
    (fun f ↦ (podReindexCalculus l L W).reduction.map
      ((scalarCompletion l E L ι W).app ((coefficientSequenceLimit l E W).obj N)) ≫
      (podReindexCalculus l L W).reduction.map
        (S.realization.hom.app ((coefficientSequenceLimit l E W).obj N)) ≫ f) hn

/-- The normalized limit square component of a coefficient transition.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL, 06YY, 0941
(blueprint: lem-pod-reindexing-tensor-coefficient-transition-core-limit).
Proof: the scalar limit and reduction maps are mates under the reduction/limit
adjunction: expanding their common completion-realization arrow leaves exactly
naturality of the counit. Apply the target L adjunction hom equivalence to the
desired equation. The mate identity at X, naturality of scalar reduction and the
counit law for D rewrite its left side. Naturality of the system scalar/pullback
comparison permits applying hred. The mate identity at Y and naturality of D′'s
inverse reduction comparison then leave precisely the counit law for D′.
Injectivity of the adjunction hom equivalence gives the result. This calculation
works for every ambient derived system, without completeness or constructibility
assumptions on that system.
-/
theorem podReindexingTensorCoefficientTransition_limit
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hpure : ∀ (M : scalarReductionSource l E Y) (U : X.ProEt)
      (x : M.val.obj (op ((proEtaleIsoPostcompose g).obj U)))
      (a : (completedIntegralCoefficientSheafUnrestricted l L Y).obj.obj
        (op ((proEtaleIsoPostcompose g).obj U))),
      (S.ordinary.hom.app M).val.app (op U)
          (integralOrdinaryTensorSection l E L ι X
            ((isoReductionIntegralInverse l E g).obj M) (op U)
            ((isoReductionCompletedMap l L g).hom.hom.app (op U) a) x) =
        integralOrdinaryTensorSection l E L ι Y M
          (op ((proEtaleIsoPostcompose g).obj U)) a x)
    (hred : ∀ K : DerivedCategory (scalarReductionSource l E Y),
      (podScalarReduction l E L ι X D'.targetRoos S.target).app
          ((podOrdinaryReindex l E g).obj K) ≫
        (integralComparisonDerivedSequenceScalar l E L ι X).map
          (D.reduction.inv.app K) ≫
        (integralComparisonSystemScalarPullback l E L ι g).hom.app
          ((podReindexCalculus l E Y).reduction.obj K) =
      (podReindexCalculus l L X).reduction.map
          ((S.derived l E L ι g D D').hom.app K) ≫
        D'.reduction.inv.app
          ((integralOrdinaryDerivedScalar l E L ι Y).obj K) ≫
        (integralComparisonDerivedSequencePullback l L g).map
          ((podScalarReduction l E L ι Y D'.sourceRoos S.source).app K)) :
    ∀ N : coefficientSequenceDerived l E Y,
      (integralOrdinaryDerivedScalar l E L ι X).map (D.limit.hom.app N) ≫
        podScalarLimit l E L ι X D'.targetRoos S.target
          ((integralComparisonDerivedSequencePullback l E g).obj N) ≫
        (coefficientSequenceLimit l L X).map
          ((integralComparisonSystemScalarPullback l E L ι g).hom.app N) =
      (S.derived l E L ι g D D').hom.app
          ((coefficientSequenceLimit l E Y).obj N) ≫
        (podOrdinaryReindex l L g).map
          (podScalarLimit l E L ι Y D'.sourceRoos S.source N) ≫
        D'.limit.hom.app
          ((integralComparisonDerivedSequenceScalar l E L ι Y).obj N) := by
  let r := (podReindexCalculus l L X).reduction
  let rE := (podReindexCalculus l E X).reduction
  let rY := (podReindexCalculus l E Y).reduction
  let rLY := (podReindexCalculus l L Y).reduction
  let uY := coefficientSequenceLimit l E Y
  let a := integralOrdinaryDerivedScalar l E L ι X
  let b := integralOrdinaryDerivedScalar l E L ι Y
  let p := podOrdinaryReindex l E g
  let pL := podOrdinaryReindex l L g
  let q := integralComparisonDerivedSequencePullback l E g
  let qL := integralComparisonDerivedSequencePullback l L g
  let s := integralComparisonDerivedSequenceScalar l E L ι Y
  let sX := integralComparisonDerivedSequenceScalar l E L ι X
  let γX := podScalarReduction l E L ι X D'.targetRoos S.target
  let γY := podScalarReduction l E L ι Y D'.sourceRoos S.source
  let δ := (S.derived l E L ι g D D').hom
  let τ := (integralComparisonSystemScalarPullback l E L ι g).hom
  let εX := (podReindexCalculus l L X).adjunction.counit
  let εE := (podReindexCalculus l E X).adjunction.counit
  let εY := (podReindexCalculus l E Y).adjunction.counit
  let εLY := (podReindexCalculus l L Y).adjunction.counit
  intro N
  let βX := podScalarLimit l E L ι X D'.targetRoos S.target (q.obj N)
  let βY := podScalarLimit l E L ι Y D'.sourceRoos S.source N
  have hnX : r.map (a.map (D.limit.hom.app N)) ≫
      γX.app ((coefficientSequenceLimit l E X).obj (q.obj N)) =
      γX.app (p.obj (uY.obj N)) ≫ sX.map (rE.map (D.limit.hom.app N)) :=
    γX.naturality (D.limit.hom.app N)
  have hnτ : sX.map (q.map (εY.app N)) ≫ τ.app N =
      τ.app (rY.obj (uY.obj N)) ≫ qL.map (s.map (εY.app N)) :=
    τ.naturality (εY.app N)
  have hnD : r.map (pL.map βY) ≫ D'.reduction.inv.app
        ((coefficientSequenceLimit l L Y).obj (s.obj N)) =
      D'.reduction.inv.app (b.obj (uY.obj N)) ≫ qL.map (rLY.map βY) :=
    D'.reduction.inv.naturality βY
  have hcE := hD.2.2.2.2.1 N
  have hcL := hD'.2.2.2.2.1 (s.obj N)
  have hmX := scalarLimitMate l E L ι X D'.targetRoos S.target (q.obj N)
  have hmY := scalarLimitMate l E L ι Y D'.sourceRoos S.source N
  have hnε : r.map ((coefficientSequenceLimit l L X).map (τ.app N)) ≫
      εX.app (qL.obj (s.obj N)) = εX.app (sX.obj (q.obj N)) ≫ τ.app N :=
    εX.naturality (τ.app N)
  apply ((podReindexCalculus l L X).adjunction.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  change r.map (a.map (D.limit.hom.app N)) ≫ r.map βX ≫
      r.map ((coefficientSequenceLimit l L X).map (τ.app N)) ≫
        εX.app (qL.obj (s.obj N)) =
    r.map (δ.app (uY.obj N)) ≫ r.map (pL.map βY) ≫
      r.map (D'.limit.hom.app (s.obj N)) ≫ εX.app (qL.obj (s.obj N))
  calc
    _ = r.map (a.map (D.limit.hom.app N)) ≫
        γX.app ((coefficientSequenceLimit l E X).obj (q.obj N)) ≫
        sX.map (εE.app (q.obj N)) ≫ τ.app N := by
      rw [hnε, ← Category.assoc (r.map βX), hmX]
      simp only [Category.assoc]
      rfl
    _ = γX.app (p.obj (uY.obj N)) ≫
        sX.map (D.reduction.inv.app (uY.obj N)) ≫
        sX.map (q.map (εY.app N)) ≫ τ.app N := by
      rw [← Category.assoc, hnX]
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun f ↦ γX.app (p.obj (uY.obj N)) ≫ sX.map f ≫ τ.app N) hcE.symm
    _ = r.map (δ.app (uY.obj N)) ≫ D'.reduction.inv.app (b.obj (uY.obj N)) ≫
        qL.map (γY.app (uY.obj N)) ≫ qL.map (s.map (εY.app N)) := by
      rw [hnτ]
      simpa only [Category.assoc] using
        congrArg (fun f ↦ f ≫ qL.map (s.map (εY.app N))) (hred (uY.obj N))
    _ = r.map (δ.app (uY.obj N)) ≫ D'.reduction.inv.app (b.obj (uY.obj N)) ≫
        qL.map (rLY.map βY) ≫ qL.map (εLY.app (s.obj N)) := by
      rw [← qL.map_comp, ← hmY, qL.map_comp]
    _ = _ := by
      rw [← Category.assoc (D'.reduction.inv.app _), ← hnD]
      simpa only [Category.assoc] using
        congrArg (fun f ↦ r.map (δ.app (uY.obj N)) ≫ r.map (pL.map βY) ≫ f) hcL

end WeilConjectures
