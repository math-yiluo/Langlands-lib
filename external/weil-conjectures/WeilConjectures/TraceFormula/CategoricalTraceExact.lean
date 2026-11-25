/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Data.Int.Interval
public import WeilConjectures.LinearAlgebra.TraceLongExactSequence
public import WeilConjectures.TraceFormula.CategoricalTrace
public import WeilConjectures.TraceFormula.UnitBasis

/-!

# Additivity of categorical traces along long exact sequences

Let `C` be an abelian braided monoidal category whose tensor product is additive, and such that
`K = End (𝟙_ C)` is a field: every nonzero endomorphism of the unit is invertible. An object is
*finite free* (`CategoryTheory.MonoidalCategory.IsFiniteFree`) if it is a finite biproduct of
copies of the unit `𝟙_ C`. Finite free objects are dualizable, morphisms between them are matrices
over `K`, and the categorical trace of an endomorphism is the trace of its matrix.

For a bounded long exact sequence
`⋯ ⟶ Aʲ ⟶ Bʲ ⟶ Dʲ ⟶ Aʲ⁺¹ ⟶ ⋯` of finite free objects with endomorphisms commuting with all
the maps, the alternating sums of the traces satisfy `STr(B) = STr(A) + STr(D)`
(`CategoryTheory.superTrace_eq_add_of_exact`).

## Main definitions

- `CategoryTheory.MonoidalCategory.IsFiniteFree`: finite biproducts of copies of the unit.

## Main results

- `CategoryTheory.superTrace_eq_add_of_exact`: additivity of supertraces along bounded long
  exact sequences of finite free objects.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalPreadditive C] [HasFiniteBiproducts C]

/-- An object is *finite free* if it is isomorphic to a finite biproduct of copies of the
monoidal unit. -/
def MonoidalCategory.IsFiniteFree (X : C) : Prop :=
  ∃ n : ℕ, Nonempty (X ≅ ⨁ fun _ : Fin n ↦ 𝟙_ C)

omit [BraidedCategory C] [MonoidalPreadditive C] in
/-- A finite free object has a unit basis. -/
lemma MonoidalCategory.IsFiniteFree.exists_unitBasis {X : C} (hX : IsFiniteFree X) :
    ∃ n : ℕ, Nonempty (UnitBasis X (Fin n)) :=
  have ⟨n, ⟨e⟩⟩ := hX
  ⟨n, ⟨UnitBasis.ofIso e⟩⟩

/-- **Additivity of supertraces along long exact sequences.** Let `End (𝟙_ C)` be a field, and
let `⋯ ⟶ Aʲ ⟶ Bʲ ⟶ Dʲ ⟶ Aʲ⁺¹ ⟶ ⋯` be a long exact sequence of finite free objects, zero outside a
finite range of degrees, with endomorphisms `φ_A`, `φ_B`, `φ_D` commuting with all the maps.
Then `∑ⱼ (-1)ʲ Tr(φ_Bʲ) = ∑ⱼ (-1)ʲ Tr(φ_Aʲ) + ∑ⱼ (-1)ʲ Tr(φ_Dʲ)`. -/
theorem superTrace_eq_add_of_exact (hK : ∀ t : End (𝟙_ C), t ≠ 0 → IsIso t.asHom)
    (h₁ : (1 : End (𝟙_ C)) ≠ 0) {A B D : ℤ → C} (φA : ∀ j, A j ⟶ A j) (φB : ∀ j, B j ⟶ B j)
    (φD : ∀ j, D j ⟶ D j) (u : ∀ j, A j ⟶ B j) (v : ∀ j, B j ⟶ D j) (w : ∀ j, D j ⟶ A (j + 1))
    (hu : ∀ j, φA j ≫ u j = u j ≫ φB j) (hv : ∀ j, φB j ≫ v j = v j ≫ φD j)
    (hw : ∀ j, φD j ≫ w j = w j ≫ φA (j + 1))
    (huv : ∀ j, u j ≫ v j = 0) (hvw : ∀ j, v j ≫ w j = 0) (hwu : ∀ j, w j ≫ u (j + 1) = 0)
    (ex₁ : ∀ j, (ShortComplex.mk _ _ (huv j)).Exact)
    (ex₂ : ∀ j, (ShortComplex.mk _ _ (hvw j)).Exact)
    (ex₃ : ∀ j, (ShortComplex.mk _ _ (hwu j)).Exact)
    (hA : ∀ j, IsFiniteFree (A j)) (hB : ∀ j, IsFiniteFree (B j)) (hD : ∀ j, IsFiniteFree (D j))
    (hbdd : ∃ a b : ℤ, ∀ j, (j < a ∨ b < j) → IsZero (A j) ∧ IsZero (B j) ∧ IsZero (D j)) :
    superTrace B φB = superTrace A φA + superTrace D φD := by
  have hKf := isField_end_tensorUnit hK h₁
  let := hKf.toField
  have hfin {X : C} (hX : IsFiniteFree X) :
      FiniteDimensional (End (𝟙_ C))ᵐᵒᵖ (𝟙_ C ⟶ X) := by
    obtain ⟨n, ⟨b⟩⟩ := hX.exists_unitBasis
    exact b.moduleFinite
  have htr {X : C} (hX : IsFiniteFree X) (φ : X ⟶ X) :
      LinearMap.trace (End (𝟙_ C))ᵐᵒᵖ (𝟙_ C ⟶ X) (Preadditive.rightCompEndOp _ φ) =
        .op (traceOrZero φ) := by
    obtain ⟨n, ⟨b⟩⟩ := hX.exists_unitBasis
    exact b.trace_rightCompEndOp φ
  have hex {X Y Z : C} (hX : IsFiniteFree X) (hY : IsFiniteFree Y) {f : X ⟶ Y} {g : Y ⟶ Z}
      {hfg : f ≫ g = 0} (hS : (ShortComplex.mk f g hfg).Exact) :
      Function.Exact (Preadditive.rightCompEndOp (𝟙_ C) f)
        (Preadditive.rightCompEndOp (𝟙_ C) g) := by
    obtain ⟨n, ⟨bX⟩⟩ := hX.exists_unitBasis
    obtain ⟨m, ⟨bY⟩⟩ := hY.exists_unitBasis
    exact bX.exact_rightCompEndOp hKf bY hS
  have hcomm {X Y : C} {φ : X ⟶ X} {ψ : Y ⟶ Y} {f : X ⟶ Y} (h : φ ≫ f = f ≫ ψ) :
      Preadditive.rightCompEndOp (𝟙_ C) f ∘ₗ Preadditive.rightCompEndOp (𝟙_ C) φ =
        Preadditive.rightCompEndOp (𝟙_ C) ψ ∘ₗ Preadditive.rightCompEndOp (𝟙_ C) f :=
    LinearMap.ext fun x ↦ by simp [h]
  have hsub {X : C} (hX : IsZero X) : Subsingleton (𝟙_ C ⟶ X) :=
    ⟨fun x y ↦ hX.eq_of_tgt x y⟩
  have := fun j ↦ hfin (hA j)
  have := fun j ↦ hfin (hB j)
  have := fun j ↦ hfin (hD j)
  obtain ⟨a, b, hab⟩ := hbdd
  -- the sequence reindexed by `n ↦ -n`, with connecting maps `D (-n) ⟶ A (-(n - 1))`
  have hidx (n : ℤ) : -n + 1 = -(n - 1) := by omega
  let δ (n : ℤ) : D (-n) ⟶ A (-(n - 1)) := w (-n) ≫ eqToHom (congrArg A (hidx n))
  have hφA {i j : ℤ} (h : i = j) :
      φA i ≫ eqToHom (congrArg A h) = eqToHom (congrArg A h) ≫ φA j := by
    subst h
    simp
  have hexδ {i j : ℤ} (h : i = j) {X : C} {f : X ⟶ A i}
      (hf : Function.Exact (Preadditive.rightCompEndOp (𝟙_ C) f)
        (Preadditive.rightCompEndOp (𝟙_ C) (u i))) :
      Function.Exact (Preadditive.rightCompEndOp (𝟙_ C) (f ≫ eqToHom (congrArg A h)))
        (Preadditive.rightCompEndOp (𝟙_ C) (u j)) := by
    subst h
    simpa using hf
  have hexδ' {W X Y Z : C} (h : Y = Z) {f : W ⟶ X} {g : X ⟶ Y}
      (hfg : Function.Exact (Preadditive.rightCompEndOp (𝟙_ C) f)
        (Preadditive.rightCompEndOp (𝟙_ C) g)) :
      Function.Exact (Preadditive.rightCompEndOp (𝟙_ C) f)
        (Preadditive.rightCompEndOp (𝟙_ C) (g ≫ eqToHom h)) := by
    subst h
    simpa using hfg
  have hδ (n : ℤ) : φD (-n) ≫ δ n = δ n ≫ φA (-(n - 1)) := by
    simp only [δ]
    rw [reassoc_of% (hw (-n)), hφA (hidx n), Category.assoc]
  set s : Finset ℤ := Finset.Icc (-b) (-a)
  have hs {n : ℤ} (hn : n ∉ s) : -n < a ∨ b < -n := by
    simp only [s, Finset.mem_Icc, not_and_or, not_le] at hn
    omega
  have key := LinearMap.sum_negOnePow_smul_trace_sub_trace_sub_trace_eq_zero
    (K := (End (𝟙_ C))ᵐᵒᵖ) (fun n ↦ 𝟙_ C ⟶ A (-n)) (fun n ↦ 𝟙_ C ⟶ B (-n))
    (fun n ↦ 𝟙_ C ⟶ D (-n)) (fun n ↦ Preadditive.rightCompEndOp _ (u (-n)))
    (fun n ↦ Preadditive.rightCompEndOp _ (v (-n))) (fun n ↦ Preadditive.rightCompEndOp _ (δ n))
    (fun n ↦ hex (hA _) (hB _) (ex₁ _)) (fun n ↦ hexδ' _ (hex (hB _) (hD _) (ex₂ _)))
    (fun n ↦ hexδ (hidx n) (hex (hD _) (hA _) (ex₃ _)))
    (fun n ↦ Preadditive.rightCompEndOp _ (φA (-n)))
    (fun n ↦ Preadditive.rightCompEndOp _ (φB (-n)))
    (fun n ↦ Preadditive.rightCompEndOp _ (φD (-n))) (fun n ↦ (hcomm (hu _)).symm)
    (fun n ↦ (hcomm (hv _)).symm) (fun n ↦ (hcomm (hδ n)).symm) s
    (fun n hn ↦ hsub (hab _ (hs hn)).1) (fun n hn ↦ hsub (hab _ (hs hn)).2.2)
  simp only [htr (hA _), htr (hB _), htr (hD _)] at key
  -- the supertraces are the sums over `s` of the reindexed traces
  have hsum {X : ℤ → C} (hX : ∀ j, IsFiniteFree (X j))
      (hX₀ : ∀ j, (j < a ∨ b < j) → IsZero (X j)) (φ : ∀ j, X j ⟶ X j) :
      superTrace X φ = ∑ n ∈ s, (n.negOnePow : ℤ) • traceOrZero (φ (-n)) := by
    have h₀ {n : ℤ} (hn : n ∉ s) : traceOrZero (φ (-n)) = 0 := by
      have := hsub (hX₀ _ (hs hn))
      apply MulOpposite.op_injective
      rw [← htr (hX _), LinearMap.trace_eq_zero_of_subsingleton, MulOpposite.op_zero]
    rw [superTrace, ← finsum_comp_equiv (Equiv.neg ℤ)]
    refine (finsum_eq_sum_of_support_subset _ fun n hn ↦ ?_).trans
      (Finset.sum_congr rfl fun n _ ↦ ?_)
    · by_contra h
      apply hn
      change ((-n).negOnePow : ℤ) • traceOrZero (φ (-n)) = 0
      rw [h₀ h, smul_zero]
    · change ((-n).negOnePow : ℤ) • traceOrZero (φ (-n)) = _
      rw [Int.negOnePow_neg]
  rw [hsum hA (fun j hj ↦ (hab j hj).1), hsum hB (fun j hj ↦ (hab j hj).2.1),
    hsum hD (fun j hj ↦ (hab j hj).2.2), ← sub_eq_zero, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply MulOpposite.op_injective
  rw [MulOpposite.op_zero, ← key, ← MulOpposite.opAddEquiv_apply, map_sum]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  simp only [MulOpposite.opAddEquiv_apply, MulOpposite.op_sub, MulOpposite.op_add,
    MulOpposite.op_smul, smul_sub]
  abel

end CategoryTheory
