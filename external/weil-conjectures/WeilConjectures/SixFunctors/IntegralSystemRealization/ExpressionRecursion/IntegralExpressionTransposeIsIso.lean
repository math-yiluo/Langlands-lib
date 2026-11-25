/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.ExpressionRecursion.IntegralExpressionRecursionData
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated

/-! # Invertibility of the expression coefficient transpose -/

@[expose] public noncomputable section

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField
  WeilConjectures.integralDerivedPullback WeilConjectures.integralCompletedTensor
  WeilConjectures.pullbackTensorCalculus
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization.ExpressionRecursion
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem normalized_of_iso {V : Scheme.{u}}
    {A B : coefficientSequenceDerived.{u, u} l E V} (e : A ≅ B)
    (hA : IsNormalizedCoefficientSequence l E V A) :
    IsNormalizedCoefficientSequence l E V B := by
  intro m n h P
  let F := coefficientSequenceDerivedEvaluation.{u, u} l E V m
  let G := coefficientSequenceDerivedEvaluation.{u, u} l E V n
  let U := normalizedDVRRes l E V h
  let τ := coefficientSequenceDerivedTransition.{u, u} l E V h
  constructor
  · intro f g hfg
    apply (cancel_epi (G.map e.hom)).1
    apply (hA h P).1
    simp only [Functor.map_comp]
    change τ.app A ≫ (G ⋙ U).map e.hom ≫ U.map f =
      τ.app A ≫ (G ⋙ U).map e.hom ≫ U.map g
    change τ.app B ≫ U.map f = τ.app B ≫ U.map g at hfg
    rw [← τ.naturality_assoc e.hom, ← τ.naturality_assoc e.hom, hfg]
  · intro f
    obtain ⟨g, hg⟩ := (hA h P).2 (F.map e.hom ≫ f)
    refine ⟨G.map e.inv ≫ g, ?_⟩
    apply (cancel_epi (F.map e.hom)).1
    rw [← Category.assoc, τ.naturality e.hom]
    simp only [Functor.comp_map, Category.assoc, Functor.map_comp]
    rw [← U.map_comp_assoc, ← G.map_comp, Iso.hom_inv_id, G.map_id, U.map_id,
      Category.id_comp]
    exact hg

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem bounds_of_iso {W : Scheme.{u}} {M N : System l E W}
    (e : M ≅ N) (hM : LevelBounds l E W M) : LevelBounds l E W N := by
  obtain ⟨a, b, c, d, hab, hcd, hlevels⟩ := hM
  refine ⟨a, b, c, d, hab, hcd, fun n ↦ ?_⟩
  let Rn := Padic.coefficientExtensionRing l E (n + 1)
  let A : proEtaleDerivedCategory W Rn :=
    (coefficientSequenceDerivedEvaluation l E W n).obj M
  let B : proEtaleDerivedCategory W Rn :=
    (coefficientSequenceDerivedEvaluation l E W n).obj N
  let q : A ≅ B := (coefficientSequenceDerivedEvaluation l E W n).mapIso e
  let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W) :=
    (proEtale_bounded_constructible_isTriangulated W Rn).1
  have hc : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W B :=
    (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W).prop_of_iso
      q (hlevels n).1
  have hb : proEtaleCohomologicalSupport (Y := W) (A := Rn) B ⊆ Set.Icc a b := by
    intro i hi
    apply (hlevels n).2.1
    intro hz
    exact hi (hz.of_iso ((DerivedCategory.homologyFunctor
      (proEtaleRingModules W (proEtaleConstantRing W Rn)) i).mapIso q).symm)
  have ht : HasProEtaleTorAmplitude W Rn B c d := by
    refine ⟨(hlevels n).2.2.1, ?_⟩
    rintro L P ⟨r⟩ f hf hP A i hi
    exact (hlevels n).2.2.2 L P ⟨r ≪≫ q.symm⟩ f hf hP A i hi
  exact ⟨hc, hb, ht⟩

private theorem origins_of_iso {W : Scheme.{u}} {M N : System l E W}
    (e : M ≅ N) (q : Origins l E W M) : Nonempty (Origins l E W N) := by
  refine ⟨{
    level := q.level
    origin := q.origin
    etaleTransition := q.etaleTransition
    fixedTransition := q.fixedTransition
    originSquare := q.originSquare
    evaluation := fun n ↦ q.evaluation n ≪≫
      (coefficientSequenceDerivedEvaluation.{u, u} l E W n).mapIso e
    transitionSquare := ?_ }⟩
  intro n
  erw [q.transitionSquare]
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp, Category.assoc]
  rw [(coefficientSequenceDerivedTransition.{u, u} l E W (Nat.le_succ n)).naturality_assoc e.hom]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc, ← Functor.map_comp,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]

private theorem good_of_iso {W : Scheme.{u}} {M N : System l E W}
    (e : M ≅ N) (hM : Good l E W M) : Good l E W N := by
  refine ⟨normalized_of_iso l E e hM.1, bounds_of_iso l E e hM.2.1, ?_⟩
  obtain ⟨q⟩ := hM.2.2
  exact origins_of_iso l E e q

end WeilConjectures.IntegralSystemRealization.ExpressionRecursion
