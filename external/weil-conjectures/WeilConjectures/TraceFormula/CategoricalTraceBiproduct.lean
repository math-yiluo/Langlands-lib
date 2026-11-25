/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import WeilConjectures.Algebra.Homology.Monoidal.Supertrace
public import WeilConjectures.TraceFormula.CategoricalTrace

/-!

# The categorical trace on a finite biproduct

Let `C` be a braided monoidal preadditive category in which the tensor product is additive in
each variable. The categorical trace of an endomorphism `T` of a finite biproduct `⨁ᵢ Vᵢ` of
dualizable objects is the sum of the traces of its diagonal blocks `ιᵢ ≫ T ≫ πᵢ`
(`CategoryTheory.traceOrZero_eq_sum_of_isBilimit`). In particular, if `T` permutes the
summands, only the summands fixed by the permutation contribute.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Preadditive C]
  [MonoidalPreadditive C]

namespace Limits.Bicone

variable {ι : Type*} {V W : ι → C} [∀ i, ExactPairing (V i) (W i)]

/-- The coevaluation `𝟙_ C ⟶ (⨁ᵢ Vᵢ) ⊗ (⨁ᵢ Wᵢ)`, the sum of the coevaluations of the exact
pairings `Vᵢ ⊗ Wᵢ`. -/
noncomputable def coevaluation [Fintype ι] (b : Bicone V) (c : Bicone W) : 𝟙_ C ⟶ b.pt ⊗ c.pt :=
  ∑ i, η_ (V i) (W i) ≫ (b.ι i ⊗ₘ c.ι i)

/-- The evaluation `(⨁ᵢ Wᵢ) ⊗ (⨁ᵢ Vᵢ) ⟶ 𝟙_ C`, the sum of the evaluations of the exact
pairings `Vᵢ ⊗ Wᵢ`. -/
noncomputable def evaluation [Fintype ι] (b : Bicone V) (c : Bicone W) : c.pt ⊗ b.pt ⟶ 𝟙_ C :=
  ∑ i, (c.π i ⊗ₘ b.π i) ≫ ε_ (V i) (W i)

omit [BraidedCategory C] [MonoidalPreadditive C] in
/-- The `(i, j)` summand of the zigzag `η ▷ X ≫ α ≫ X ◁ ε` for `X = ⨁ᵢ Vᵢ` factors through the
zigzag of the pairing `Vᵢ ⊗ Wᵢ`, with `c.ι i ≫ c.π j` inserted. -/
theorem coevaluation_evaluation_term (b : Bicone V) (c : Bicone W) (i j : ι) :
    η_ (V i) (W i) ▷ b.pt ≫ (b.ι i ⊗ₘ c.ι i) ▷ b.pt ≫ (α_ _ _ _).hom ≫
      b.pt ◁ (c.π j ⊗ₘ b.π j) ≫ b.pt ◁ ε_ (V j) (W j) =
    _ ◁ b.π j ≫ η_ (V i) (W i) ▷ V j ≫ (α_ _ _ _).hom ≫ V i ◁ ((c.ι i ≫ c.π j) ▷ V j) ≫
      V i ◁ ε_ (V j) (W j) ≫ b.ι i ▷ 𝟙_ C := by
  simp only [tensorHom_def', whiskerLeft_comp, comp_whiskerRight, Category.assoc]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc (b.ι i),
    ← whisker_exchange_assoc (b.ι i), ← whisker_exchange (b.ι i),
    associator_naturality_middle_assoc, ← whiskerLeft_comp_assoc, ← whisker_exchange,
    whiskerLeft_comp_assoc, ← associator_naturality_right_assoc,
    ← whisker_exchange_assoc (η_ (V i) (W i))]

omit [BraidedCategory C] [MonoidalPreadditive C] in
/-- The `(i, j)` summand of the zigzag `Y ◁ η ≫ α⁻¹ ≫ ε ▷ Y` for `Y = ⨁ᵢ Wᵢ` factors through
the zigzag of the pairing `Vᵢ ⊗ Wᵢ`, with `b.ι i ≫ b.π j` inserted. -/
theorem evaluation_coevaluation_term (b : Bicone V) (c : Bicone W) (i j : ι) :
    c.pt ◁ η_ (V i) (W i) ≫ c.pt ◁ (b.ι i ⊗ₘ c.ι i) ≫ (α_ _ _ _).inv ≫
      (c.π j ⊗ₘ b.π j) ▷ c.pt ≫ ε_ (V j) (W j) ▷ c.pt =
    c.π j ▷ 𝟙_ C ≫ W j ◁ η_ (V i) (W i) ≫ W j ◁ ((b.ι i ≫ b.π j) ▷ W i) ≫ (α_ _ _ _).inv ≫
      ε_ (V j) (W j) ▷ W i ≫ 𝟙_ C ◁ c.ι i := by
  simp only [tensorHom_def, whiskerLeft_comp, comp_whiskerRight, Category.assoc]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc, whisker_exchange_assoc,
    whisker_exchange, ← associator_inv_naturality_left_assoc, whisker_exchange_assoc,
    whisker_exchange_assoc, ← associator_inv_naturality_middle_assoc]

/-- The summands of a bilimit bicone of objects `Vᵢ` and those of a bilimit bicone of objects
`Wᵢ`, with exact pairings `Vᵢ ⊗ Wᵢ`, form an exact pairing `(⨁ᵢ Vᵢ) ⊗ (⨁ᵢ Wᵢ)`: a finite
biproduct of objects with right duals has as right dual the biproduct of the right duals. -/
@[instance_reducible]
noncomputable def exactPairing [Fintype ι] {b : Bicone V} (hb : b.IsBilimit) {c : Bicone W}
    (hc : c.IsBilimit) : ExactPairing b.pt c.pt where
  coevaluation' := coevaluation b c
  evaluation' := evaluation b c
  coevaluation_evaluation' := by
    simp only [coevaluation, evaluation, whiskerLeft_sum, sum_whiskerRight, Preadditive.sum_comp,
      Preadditive.comp_sum, whiskerLeft_comp, comp_whiskerRight, Category.assoc,
      evaluation_coevaluation_term]
    rw [← Category.id_comp (λ_ c.pt).inv, ← Limits.IsBilimit.total hc]
    simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j) fun i _ hij => ?_]
    · rw [← whiskerLeft_comp_assoc (W j) (b.ι j ▷ W j), ← comp_whiskerRight, bicone_ι_π_self,
        id_whiskerRight,
        whiskerLeft_id, Category.id_comp, ExactPairing.coevaluation_evaluation_assoc,
        rightUnitor_naturality_assoc, ← leftUnitor_inv_naturality]
    · rw [← whiskerLeft_comp_assoc (W j) (b.ι i ▷ W i), ← comp_whiskerRight,
        bicone_ι_π_ne _ hij]
      simp
  evaluation_coevaluation' := by
    simp only [coevaluation, evaluation, whiskerLeft_sum, sum_whiskerRight, Preadditive.sum_comp,
      Preadditive.comp_sum, whiskerLeft_comp, comp_whiskerRight, Category.assoc,
      coevaluation_evaluation_term]
    rw [← Category.id_comp (ρ_ b.pt).inv, ← Limits.IsBilimit.total hb]
    simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j) fun i _ hij => ?_]
    · rw [← whiskerLeft_comp_assoc, ← comp_whiskerRight, bicone_ι_π_self, id_whiskerRight,
        whiskerLeft_id, Category.id_comp, ExactPairing.evaluation_coevaluation_assoc,
        leftUnitor_naturality_assoc, rightUnitor_inv_naturality]
    · rw [← whiskerLeft_comp_assoc, ← comp_whiskerRight, bicone_ι_π_ne _ hij]
      simp

end Limits.Bicone

omit [BraidedCategory C] in
/-- A finite bilimit bicone of objects with right duals has a right dual, provided `C` has
finite biproducts: the biproduct of the right duals (`CategoryTheory.Limits.Bicone.exactPairing`).
-/
theorem Limits.Bicone.nonempty_hasRightDual_pt [HasFiniteBiproducts C] {ι : Type*} [Finite ι]
    {V : ι → C} {b : Bicone V} (hb : b.IsBilimit) (hV : ∀ i, Nonempty (HasRightDual (V i))) :
    Nonempty (HasRightDual b.pt) := by
  have := Fintype.ofFinite ι
  let := fun i ↦ (hV i).some
  exact ⟨{ rightDual := _, exact := exactPairing hb (biproduct.isBilimit fun i ↦ (V i)ᘁ) }⟩

/-- The zero endomorphism has trace `0`. -/
@[simp]
theorem traceOrZero_zero {V : C} : traceOrZero (0 : V ⟶ V) = 0 := by
  by_cases h : Nonempty (HasRightDual V)
  · let := h.some
    rw [traceOrZero_eq_trace]
    apply End.ext
    simp [trace]
  · rw [traceOrZero, dite_eq_right h]

/-- **The trace on a finite biproduct**: the categorical trace of an endomorphism `T` of a finite
biproduct of dualizable objects `Vᵢ` is the sum of the traces of the diagonal blocks
`ιᵢ ≫ T ≫ πᵢ`. The finite biproducts in `C` guarantee that `b.pt` has a right dual, the
biproduct of the right duals of the `Vᵢ`; without them `b.pt` need not be dualizable, and then
its categorical trace is `0` by definition. -/
theorem traceOrZero_eq_sum_of_isBilimit [HasFiniteBiproducts C] {ι : Type*} [Fintype ι]
    {V : ι → C} {b : Bicone V} (hb : b.IsBilimit) (hV : ∀ i, Nonempty (HasRightDual (V i)))
    (T : b.pt ⟶ b.pt) :
    traceOrZero T = ∑ i, traceOrZero (b.ι i ≫ T ≫ b.π i) := by
  obtain ⟨_⟩ := b.nonempty_hasRightDual_pt hb hV
  let := fun i ↦ (hV i).some
  apply End.ext
  simp only [End.sum_asHom, traceOrZero_eq_trace]
  conv_lhs => rw [← Category.comp_id T, ← Limits.IsBilimit.total hb, Preadditive.comp_sum,
    ← traceAddMonoidHom_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [traceAddMonoidHom_apply, trace_comp_idempotent]

/-- **The trace of a block-permutation endomorphism**: let `V` be the product of finitely many
dualizable objects `Wᵢ`, with projections `πᵢ`, and `T` an endomorphism of `V` such that for
each `i` either `T ≫ πᵢ = πᵢ ≫ tᵢ` (if `p i`) or `T ≫ πᵢ` factors through `πⱼ` for some `j ≠ i`.
Then the trace of `T` is the sum of the traces of the `tᵢ` with `p i`. -/
theorem traceOrZero_eq_sum_of_isLimit_fan [HasFiniteBiproducts C] {ι : Type*} [Fintype ι]
    {V : C} {W : ι → C} (π : ∀ i, V ⟶ W i) (hπ : IsLimit (Fan.mk V π))
    (hW : ∀ i, Nonempty (HasRightDual (W i))) (T : V ⟶ V) (p : ι → Prop) [DecidablePred p]
    (t : ∀ i, p i → (W i ⟶ W i)) (hp : ∀ i (h : p i), T ≫ π i = π i ≫ t i h)
    (hnp : ∀ i, ¬ p i → ∃ j, j ≠ i ∧ ∃ s : W j ⟶ W i, T ≫ π i = π j ≫ s) :
    traceOrZero T = ∑ i, if h : p i then traceOrZero (t i h) else 0 := by
  let b := Bicone.ofLimitCone hπ
  have hb : b.IsBilimit := isBilimitOfIsLimit b hπ
  rw [traceOrZero_eq_sum_of_isBilimit hb hW T]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hbπ : ∀ j, b.π j = π j := fun _ ↦ rfl
  split_ifs with h
  · rw [hbπ, hp i h, ← hbπ, bicone_ι_π_self_assoc]
  · obtain ⟨j, hji, s, hs⟩ := hnp i h
    rw [hbπ, hs, ← hbπ, bicone_ι_π_ne_assoc _ (Ne.symm hji), Limits.zero_comp,
      traceOrZero_zero]

end CategoryTheory
