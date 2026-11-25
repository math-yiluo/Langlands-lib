/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.Congruence
public import WeilConjectures.SixFunctors.ProEtale.Adic.UnitMatrix

/-!
# Matrices of locally finite functions as `GL_n(E)`-valued functions

Let `T` be a topological space. A locally finite function `T → ℚ̄_ℓ` takes, on a compact `T`,
values in a finite-dimensional `ℚ_ℓ`-subspace of `ℚ̄_ℓ`, so finitely many of them take values in
a finite extension `E` of `ℚ_ℓ`
(`PadicAlgCl.exists_finiteDimensional_forall_mem_locallyFinite`). An invertible
matrix of locally finite functions with values in `E` is then a function
`T → GL_n(E)` with continuous entries (`PadicAlgCl.glOfMatrix`); conversely a function
`T → GL_n(E)` with continuous entries is a matrix of locally finite functions
(`PadicAlgCl.matrixOfGL`), `E` being finite-dimensional.
-/

@[expose] public section

namespace PadicAlgCl

variable {l : ℕ} [Fact l.Prime] {T : Type*} [TopologicalSpace T] {n : ℕ}

/-- **Finitely many locally finite functions on a compact space take values in a finite
extension of `ℚ_ℓ`.** -/
lemma exists_finiteDimensional_forall_mem_locallyFinite [CompactSpace T]
    (s : Finset (locallyFiniteFunctions l T)) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧
      ∀ f ∈ s, ∀ t, f.1 t ∈ E := by
  classical
  let W : Submodule ℚ_[l] (PadicAlgCl l) := s.sup fun f ↦ Submodule.span ℚ_[l] (Set.range f.1)
  have : ∀ f : locallyFiniteFunctions l T,
      FiniteDimensional ℚ_[l] (Submodule.span ℚ_[l] (Set.range f.1)) := fun f ↦
    finiteDimensional_span_range_of_mem_locallyFiniteFunctions f.2
  have hW : FiniteDimensional ℚ_[l] W := inferInstance
  obtain ⟨S, hSfin, hS⟩ := Submodule.fg_def.1 (Module.Finite.iff_fg.1 hW)
  have := hSfin.to_subtype
  refine ⟨IntermediateField.adjoin ℚ_[l] S, IntermediateField.finiteDimensional_adjoin
    fun x _ ↦ Algebra.IsIntegral.isIntegral x, fun f hf t ↦ ?_⟩
  have h₁ : f.1 t ∈ W := Finset.le_sup (f := fun f : locallyFiniteFunctions l T ↦
    Submodule.span ℚ_[l] (Set.range f.1)) hf (Submodule.subset_span ⟨t, rfl⟩)
  rw [← hS] at h₁
  have h₂ : Submodule.span ℚ_[l] S ≤
      (IntermediateField.adjoin ℚ_[l] S).toSubalgebra.toSubmodule :=
    Submodule.span_le.2 fun x hx ↦ IntermediateField.subset_adjoin ℚ_[l] S hx
  exact h₂ h₁

variable {E : IntermediateField ℚ_[l] (PadicAlgCl l)}

/-- An invertible matrix of locally finite functions with values in `E` (and with inverse with
values in `E`), as a function to `GL_n(E)`. -/
noncomputable def glOfMatrix (M M' : Matrix (Fin n) (Fin n) (locallyFiniteFunctions l T))
    (hMM' : M * M' = 1) (hM'M : M' * M = 1) (hM : ∀ i j t, (M i j).1 t ∈ E)
    (hM' : ∀ i j t, (M' i j).1 t ∈ E) (t : T) : GL (Fin n) E where
  val := Matrix.of fun i j ↦ ⟨(M i j).1 t, hM i j t⟩
  inv := Matrix.of fun i j ↦ ⟨(M' i j).1 t, hM' i j t⟩
  val_inv := by
    have := congrArg (fun N ↦ N.map (locallyFiniteFunctionsEval t)) hMM'
    simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at this
    refine Matrix.ext fun i j ↦ Subtype.ext ?_
    have h := congrFun (congrFun this i) j
    simp only [Matrix.mul_apply, Matrix.map_apply, locallyFiniteFunctionsEval_apply] at h
    simp only [Matrix.mul_apply, Matrix.of_apply, IntermediateField.coe_sum,
      IntermediateField.coe_mul, h]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  inv_val := by
    have := congrArg (fun N ↦ N.map (locallyFiniteFunctionsEval t)) hM'M
    simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at this
    refine Matrix.ext fun i j ↦ Subtype.ext ?_
    have h := congrFun (congrFun this i) j
    simp only [Matrix.mul_apply, Matrix.map_apply, locallyFiniteFunctionsEval_apply] at h
    simp only [Matrix.mul_apply, Matrix.of_apply, IntermediateField.coe_sum,
      IntermediateField.coe_mul, h]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]

lemma coe_glOfMatrix_apply (M M' : Matrix (Fin n) (Fin n) (locallyFiniteFunctions l T))
    (hMM' : M * M' = 1) (hM'M : M' * M = 1) (hM : ∀ i j t, (M i j).1 t ∈ E)
    (hM' : ∀ i j t, (M' i j).1 t ∈ E) (t : T) (i j : Fin n) :
    (((glOfMatrix M M' hMM' hM'M hM hM' t : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j :
      PadicAlgCl l) = (M i j).1 t :=
  rfl

lemma coe_glOfMatrix_inv_apply (M M' : Matrix (Fin n) (Fin n) (locallyFiniteFunctions l T))
    (hMM' : M * M' = 1) (hM'M : M' * M = 1) (hM : ∀ i j t, (M i j).1 t ∈ E)
    (hM' : ∀ i j t, (M' i j).1 t ∈ E) (t : T) (i j : Fin n) :
    ((((glOfMatrix M M' hMM' hM'M hM hM' t)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j :
      PadicAlgCl l) = (M' i j).1 t :=
  rfl

lemma continuous_glOfMatrix_apply (M M' : Matrix (Fin n) (Fin n) (locallyFiniteFunctions l T))
    (hMM' : M * M' = 1) (hM'M : M' * M = 1) (hM : ∀ i j t, (M i j).1 t ∈ E)
    (hM' : ∀ i j t, (M' i j).1 t ∈ E) (i j : Fin n) :
    (Continuous fun t ↦ ((glOfMatrix M M' hMM' hM'M hM hM' t : GL (Fin n) E) :
      Matrix (Fin n) (Fin n) E) i j) ∧
    Continuous fun t ↦ (((glOfMatrix M M' hMM' hM'M hM hM' t)⁻¹ : GL (Fin n) E) :
      Matrix (Fin n) (Fin n) E) i j :=
  ⟨(M i j).1.continuous.subtype_mk _, (M' i j).1.continuous.subtype_mk _⟩

/-- The values of `glOfMatrix`, as matrices over `ℚ̄_ℓ`. -/
lemma glOfMatrix_map (M M' : Matrix (Fin n) (Fin n) (locallyFiniteFunctions l T))
    (hMM' : M * M' = 1) (hM'M : M' * M = 1) (hM : ∀ i j t, (M i j).1 t ∈ E)
    (hM' : ∀ i j t, (M' i j).1 t ∈ E) (t : T) :
    ((glOfMatrix M M' hMM' hM'M hM hM' t : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map
      (algebraMap E (PadicAlgCl l)) = M.map (locallyFiniteFunctionsEval t) :=
  Matrix.ext fun _ _ ↦ rfl

/-- The inverses of the values of `glOfMatrix`, as matrices over `ℚ̄_ℓ`. -/
lemma glOfMatrix_inv_map (M M' : Matrix (Fin n) (Fin n) (locallyFiniteFunctions l T))
    (hMM' : M * M' = 1) (hM'M : M' * M = 1) (hM : ∀ i j t, (M i j).1 t ∈ E)
    (hM' : ∀ i j t, (M' i j).1 t ∈ E) (t : T) :
    (((glOfMatrix M M' hMM' hM'M hM hM' t)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map
      (algebraMap E (PadicAlgCl l)) = M'.map (locallyFiniteFunctionsEval t) :=
  Matrix.ext fun _ _ ↦ rfl

/-- Evaluating a matrix of composed locally finite functions. -/
lemma map_locallyFiniteFunctionsComp_map_eval {T' : Type*} [TopologicalSpace T']
    (M : Matrix (Fin n) (Fin n) (locallyFiniteFunctions l T)) (c : C(T', T)) (t : T') :
    (M.map (locallyFiniteFunctionsComp l c)).map (locallyFiniteFunctionsEval t) =
      M.map (locallyFiniteFunctionsEval (c t)) :=
  Matrix.ext fun _ _ ↦ rfl

variable [FiniteDimensional ℚ_[l] E]

/-- A function with values in `E` with continuous entries is a locally finite function. -/
noncomputable def lfOfContinuous (f : T → E) (hf : Continuous f) : locallyFiniteFunctions l T :=
  ⟨⟨fun t ↦ (f t : PadicAlgCl l), continuous_subtype_val.comp hf⟩,
    mem_locallyFiniteFunctions_of_finiteDimensional (Submodule.finiteDimensional_of_le
      (S₂ := E.toSubalgebra.toSubmodule) (Submodule.span_le.2 (by
        rintro _ ⟨t, rfl⟩
        exact (f t).2)))⟩

/-- A function `T → GL_n(E)` with continuous entries, as a matrix of locally finite
functions. -/
noncomputable def matrixOfGL (σ : T → GL (Fin n) E)
    (hσ : ∀ i j, Continuous fun t ↦ (σ t : Matrix (Fin n) (Fin n) E) i j) :
    Matrix (Fin n) (Fin n) (locallyFiniteFunctions l T) :=
  Matrix.of fun i j ↦ lfOfContinuous _ (hσ i j)

lemma matrixOfGL_apply (σ : T → GL (Fin n) E)
    (hσ : ∀ i j, Continuous fun t ↦ (σ t : Matrix (Fin n) (Fin n) E) i j) (i j : Fin n)
    (t : T) : (matrixOfGL σ hσ i j).1 t = ((σ t : Matrix (Fin n) (Fin n) E) i j : PadicAlgCl l) :=
  rfl

/-- The values of `matrixOfGL`. -/
lemma matrixOfGL_map (σ : T → GL (Fin n) E)
    (hσ : ∀ i j, Continuous fun t ↦ (σ t : Matrix (Fin n) (Fin n) E) i j) (t : T) :
    (matrixOfGL σ hσ).map (locallyFiniteFunctionsEval t) =
      (σ t : Matrix (Fin n) (Fin n) E).map (algebraMap E (PadicAlgCl l)) :=
  Matrix.ext fun _ _ ↦ rfl

lemma matrixOfGL_mul (σ τ : T → GL (Fin n) E)
    (hσ : ∀ i j, Continuous fun t ↦ (σ t : Matrix (Fin n) (Fin n) E) i j)
    (hτ : ∀ i j, Continuous fun t ↦ (τ t : Matrix (Fin n) (Fin n) E) i j)
    (h : ∀ t, σ t * τ t = 1) : matrixOfGL σ hσ * matrixOfGL τ hτ = 1 := by
  refine Matrix.ext fun i j ↦ Subtype.ext (ContinuousMap.ext fun t ↦ ?_)
  have := congrArg (fun A : GL (Fin n) E ↦ ((A : Matrix (Fin n) (Fin n) E) i j : PadicAlgCl l))
    (h t)
  simp only [Units.val_mul, Matrix.mul_apply, IntermediateField.coe_sum,
    IntermediateField.coe_mul, Units.val_one] at this
  rw [Matrix.mul_apply]
  change ((∑ k, matrixOfGL σ hσ i k * matrixOfGL τ hτ k j :
    locallyFiniteFunctions l T) : C(T, PadicAlgCl l)) t = _
  rw [show ((∑ k, matrixOfGL σ hσ i k * matrixOfGL τ hτ k j : locallyFiniteFunctions l T) :
    C(T, PadicAlgCl l)) = ∑ k, ((matrixOfGL σ hσ i k : C(T, PadicAlgCl l)) *
      matrixOfGL τ hτ k j) from map_sum (locallyFiniteFunctions l T).val _ _ |>.trans
        (Finset.sum_congr rfl fun _ _ ↦ rfl)]
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.mul_apply]
  refine this.trans ?_
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply_ne hij]

end PadicAlgCl
