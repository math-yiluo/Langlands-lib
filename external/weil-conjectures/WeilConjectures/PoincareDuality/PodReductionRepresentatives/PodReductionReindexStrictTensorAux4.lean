/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReductionRepresentatives.PodReductionReindexStrictTensorAux3

/-! # Naturality of reduced unit sections and transport along the pro-etale equivalence

Source: Stacks 03D2, 06YY, 09A5 and 0941.
(blueprint: lem-pod-reduction-reindex-strict-tensor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodReductionRepresentatives
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The sequence inverse image of a map sends the unit section of `s` to the unit section of
the image of `s`.
Source: Stacks 03D2. -/
theorem inverseImage_map_unit {X Y : Scheme.{u}} (g : X ⟶ Y)
    {M M' : coefficientSequenceModules l E Y} (φ : M ⟶ M') (V : ℕ × Y.ProEt)
    (s : M.val.obj (op V)) :
    ((integralComparisonSequencePullback l E g).map φ).val.app
        (op ((pullbackTensorSequenceBase g).obj V))
      (((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E g)).unit.app
        M).val.app (op V) s) =
      ((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E g)).unit.app
        M').val.app (op V) (φ.val.app (op V) s) :=
  (congrArg (fun f ↦ f.val.app (op V) s)
    ((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E g)).unit.naturality
      φ)).symm

/-- Ordinary reduction of a map acts on reduced unit sections through the map.
Source: Stacks 06YY and 0941. -/
theorem reduction_map_unitSection (W : Scheme.{u}) (n : ℕ)
    {M M' : integralTowerModules l E W} (φ : M ⟶ M') (V : W.ProEt) (z : M.val.obj (op V)) :
    ((pullbackTensorOrdinaryReduction l E W).map φ).val.app (op (n, V))
      (((pullbackTensorReductionEvaluation l E W n).hom.app M).val.app (op V)
        (unrestrictedIntegralTensorSection l E W n M (op V) 1 z)) =
      ((pullbackTensorReductionEvaluation l E W n).hom.app M').val.app (op V)
        (unrestrictedIntegralTensorSection l E W n M' (op V) 1 (φ.val.app (op V) z)) := by
  have h1 := congrArg (fun f ↦ f.val.app (op V)
    (unrestrictedIntegralTensorSection l E W n M (op V) 1 z))
    ((pullbackTensorReductionEvaluation l E W n).hom.naturality φ)
  have h2 := congrArg (fun f ↦ f.val.app (op V) z)
    ((pullbackTensorFiniteAdjunction l E W n).unit.naturality φ)
  have h3 : ((unrestrictedIntegralReductionFunctor l E W n).map φ).val.app (op V)
      (unrestrictedIntegralTensorSection l E W n M (op V) 1 z) =
      unrestrictedIntegralTensorSection l E W n M' (op V) 1 (φ.val.app (op V) z) := by
    rw [← finiteAdjunction_unit_apply, ← finiteAdjunction_unit_apply]
    exact h2.symm
  exact h1.symm.trans
    (congrArg (((pullbackTensorReductionEvaluation l E W n).hom.app M').val.app (op V)) h3)

-- Fix the target section type before specializing evaluation to a reduction object.
private def sequenceEvaluation_hom_apply (W : Scheme.{u}) (n : ℕ)
    {M : normalizedDVRModules l E W n} {N : coefficientSequenceModules l E W}
    (f : M ⟶ (coefficientSequenceEvaluation l E W n).obj N) (V : W.ProEt)
    (z : M.val.obj (op V)) : N.val.obj (op (n, V)) :=
  f.val.app (op V) z

private theorem sequenceEvaluation_map_apply (W : Scheme.{u}) (n : ℕ)
    (M : coefficientSequenceModules l E W) {V V' : W.ProEt} (i : V' ⟶ V)
    (z : ((coefficientSequenceEvaluation l E W n).obj M).val.obj (op V)) :
    ((coefficientSequenceEvaluation l E W n).obj M).val.map i.op z =
      M.val.map (CategoryTheory.Prod.mkHom (𝟙 n) i).op z := rfl

/-- Ordinary reduction is compatible with restriction of reduced unit sections.
Source: Stacks 06YY and 0941. -/
theorem reduction_restrict_unitSection (W : Scheme.{u}) (n : ℕ)
    (M : integralTowerModules l E W) {V V' : W.ProEt} (i : V' ⟶ V) (z : M.val.obj (op V)) :
    ((pullbackTensorOrdinaryReduction l E W).obj M).val.map
        (CategoryTheory.Prod.mkHom (𝟙 n) i).op
      (((pullbackTensorReductionEvaluation l E W n).hom.app M).val.app (op V)
        (unrestrictedIntegralTensorSection l E W n M (op V) 1 z)) =
      ((pullbackTensorReductionEvaluation l E W n).hom.app M).val.app (op V')
        (unrestrictedIntegralTensorSection l E W n M (op V') 1 (M.val.map i.op z)) := by
  have h1 := PresheafOfModules.naturality_apply
    ((pullbackTensorReductionEvaluation l E W n).hom.app M).val i.op
    (unrestrictedIntegralTensorSection l E W n M (op V) 1 z)
  have h2 := PresheafOfModules.naturality_apply
    ((pullbackTensorFiniteAdjunction l E W n).unit.app M).val i.op z
  have h3 : ((unrestrictedIntegralReductionFunctor l E W n).obj M).val.map i.op
      (unrestrictedIntegralTensorSection l E W n M (op V) 1 z) =
      unrestrictedIntegralTensorSection l E W n M (op V') 1 (M.val.map i.op z) := by
    rw [← finiteAdjunction_unit_apply, ← finiteAdjunction_unit_apply]
    exact h2.symm
  have h4 := congrArg
    (((pullbackTensorReductionEvaluation l E W n).hom.app M).val.app (op V')) h3
  have h0 := sequenceEvaluation_map_apply l E W n
    ((pullbackTensorOrdinaryReduction l E W).obj M) i
    (((pullbackTensorReductionEvaluation l E W n).hom.app M).val.app (op V)
      (unrestrictedIntegralTensorSection l E W n M (op V) 1 z))
  -- Reduce carriers first so that composing equalities does not compare transported scalar actions.
  dsimp only [Functor.comp_obj, coefficientSequenceEvaluation, SheafOfModules.pushforward,
    PresheafOfModules.pushforward, PresheafOfModules.pushforward₀,
    PresheafOfModules.pushforward₀Obj, PresheafOfModules.restrictScalars,
    PresheafOfModules.restrictScalarsObj, ModuleCat.restrictScalars,
    ModuleCat.RestrictScalars.obj'] at h0 h1 h4 ⊢
  exact h0.symm.trans (h1.symm.trans h4)


/-- Two maps out of the reduction of a total tensor degree agree once they agree on reduced
pure tensors over every object postcomposed along an isomorphism of schemes.
Source: Stacks 03EK, 06YY, 09A5 and 0941. -/
theorem reduction_total_hom_ext_postcompose {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (P Q : CochainComplex (integralTowerModules l E Y) ℤ) (k : ℤ)
    {N : coefficientSequenceModules l E Y}
    {h₁ h₂ : (pullbackTensorOrdinaryReduction l E Y).obj
      (((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology Y)
        (completedIntegralCommRingSheafUnrestricted l E Y)).obj (P, Q)).X k) ⟶ N}
    (h : ∀ (n : ℕ) (p q : ℤ) (hpq : p + q = k) (U : X.ProEt)
      (x : (P.X p).val.obj (op ((proEtaleIsoPostcompose g).obj U)))
      (y : (Q.X q).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
      h₁.val.app (op (n, (proEtaleIsoPostcompose g).obj U))
        (((pullbackTensorReductionEvaluation l E Y n).hom.app _).val.app
          (op ((proEtaleIsoPostcompose g).obj U))
          (unrestrictedIntegralTensorSection l E Y n _ (op ((proEtaleIsoPostcompose g).obj U)) 1
            (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y)
              (completedIntegralCommRingSheafUnrestricted l E Y) P Q p q k hpq
              (op ((proEtaleIsoPostcompose g).obj U)) x y))) =
      h₂.val.app (op (n, (proEtaleIsoPostcompose g).obj U))
        (((pullbackTensorReductionEvaluation l E Y n).hom.app _).val.app
          (op ((proEtaleIsoPostcompose g).obj U))
          (unrestrictedIntegralTensorSection l E Y n _ (op ((proEtaleIsoPostcompose g).obj U)) 1
            (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y)
              (completedIntegralCommRingSheafUnrestricted l E Y) P Q p q k hpq
              (op ((proEtaleIsoPostcompose g).obj U)) x y)))) :
    h₁ = h₂ := by
  apply reduction_total_hom_ext l E Y P Q k
  intro n p q hpq V x y
  have : (proEtaleIsoPostcompose g).IsEquivalence := (proEtaleIsoPostcompose_equivalence g).1
  let U := (proEtaleIsoPostcompose g).objPreimage V
  let i : (proEtaleIsoPostcompose g).obj U ≅ V := (proEtaleIsoPostcompose g).objObjPreimageIso V
  have hx : (P.X p).val.map i.inv.op ((P.X p).val.map i.hom.op x) = x := by
    rw [← PresheafOfModules.map_comp_apply, ← op_comp, i.inv_hom_id, op_id,
      PresheafOfModules.map_id]
    rfl
  have hy : (Q.X q).val.map i.inv.op ((Q.X q).val.map i.hom.op y) = y := by
    rw [← PresheafOfModules.map_comp_apply, ← op_comp, i.inv_hom_id, op_id,
      PresheafOfModules.map_id]
    rfl
  let T : integralTowerModules l E Y :=
    (((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology Y)
      (completedIntegralCommRingSheafUnrestricted l E Y)).obj (P, Q)).X k)
  let unitAt (V : Y.ProEt) (z : T.val.obj (op V)) :
      ((pullbackTensorOrdinaryReduction l E Y).obj T).val.obj (op (n, V)) :=
    sequenceEvaluation_hom_apply l E Y n
      ((pullbackTensorReductionEvaluation l E Y n).hom.app T) V
      (unrestrictedIntegralTensorSection l E Y n T (op V) 1 z)
  let z := coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y)
    (completedIntegralCommRingSheafUnrestricted l E Y) P Q p q k hpq
    (op ((proEtaleIsoPostcompose g).obj U))
    ((P.X p).val.map i.hom.op x) ((Q.X q).val.map i.hom.op y)
  have ht := coefficientTensorGenerator_restrict (ProEt.topology Y)
    (completedIntegralCommRingSheafUnrestricted l E Y) P Q p q k hpq i.inv.op
    ((P.X p).val.map i.hom.op x) ((Q.X q).val.map i.hom.op y)
  rw [hx, hy] at ht
  have hr := reduction_restrict_unitSection l E Y n T i.inv z
  have hs := hr.trans (congrArg (unitAt V) ht)
  have key (f : (pullbackTensorOrdinaryReduction l E Y).obj T ⟶ N) :=
    (PresheafOfModules.naturality_apply f.val
      (CategoryTheory.Prod.mkHom (𝟙 n) i.inv).op (unitAt _ z)).symm.trans
      (congrArg (f.val.app (op (n, V))) hs)
  exact (key h₁).symm.trans ((congrArg (N.val.map (CategoryTheory.Prod.mkHom (𝟙 n) i.inv).op)
    (h n p q hpq U _ _)).trans (key h₂))


end WeilConjectures.PodReductionRepresentatives
