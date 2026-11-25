/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import WeilConjectures.Mathlib.RingTheory.PiTensorProduct

/-!
# The Amitsur complex of a faithfully flat algebra

Let `B` be a commutative `A`-algebra and `M` an `A`-module. The Amitsur complex of `B` over `A`
with coefficients in `M` is
`M ⊗_A B → M ⊗_A B ⊗_A B → M ⊗_A B ⊗_A B ⊗_A B → ⋯`, whose differential is the alternating sum of
the maps inserting `1` into one of the tensor factors of `B`. It is augmented by
`M → M ⊗_A B, m ↦ m ⊗ 1`.

If `B` is faithfully flat over `A`, the augmented Amitsur complex is exact.

## Main definitions

- `Algebra.TensorProduct.amitsurCosimplicialObject`: the cosimplicial `A`-module
  `[k] ↦ M ⊗_A B^{⊗ (k + 1)}`, with `B^{⊗ (k + 1)} = ⨂[A] _ : Fin (k + 1), B`.
- `Algebra.TensorProduct.amitsurComplex`: the Amitsur complex, as the alternating coface map
  complex of the cosimplicial `A`-module `[k] ↦ M ⊗_A B^{⊗ (k + 1)}`.
- `Algebra.TensorProduct.amitsurAugmentation`: the augmentation `M → M ⊗_A B, m ↦ m ⊗ 1`.

## Main statements

- `Module.FaithfullyFlat.exact_amitsurComplex`: the augmented Amitsur complex of a faithfully
  flat algebra is exact.

## Implementation notes

The structure maps of `amitsurCosimplicialObject` are `M ⊗ θ_*`, where for
`θ : Fin (k + 1) → Fin (m + 1)` the algebra map `θ_* : B^{⊗ (k + 1)} → B^{⊗ (m + 1)}` sends `b`
in the `i`-th factor to `b` in the `θ i`-th factor (`Algebra.TensorProduct.amitsurMap`).

Exactness is proved as in the blueprint: after tensoring with `B` on the left, the augmented
cosimplicial module acquires an extra codegeneracy
`b ⊗ m ⊗ b₀ ⊗ ⋯ ⊗ bₙ ↦ b b₀ ⊗ m ⊗ b₁ ⊗ ⋯ ⊗ bₙ`, which yields exactness of the base changed
complex (`CategoryTheory.CosimplicialObject.exact_lTensor_alternatingCofaceMapComplex_d` and
`CategoryTheory.CosimplicialObject.exact_lTensor_augmentation`); faithful flatness of `B` then
reflects exactness.
-/

@[expose] public section

universe u

open CategoryTheory TensorProduct AlgebraicTopology Simplicial

namespace LinearMap

variable {R V W U : Type*} [CommRing R] [AddCommGroup V] [AddCommGroup W] [AddCommGroup U]
  [Module R V] [Module R W] [Module R U]

/-- Let `V → W → U` be two consecutive alternating sums of maps `δ₁ i`, `δ₂ i` (as in a
cosimplicial module) whose composition vanishes. If there are maps `s₁ : W → V`, `s₂ : U → W`
with `s₂ ∘ δ₂ 0 = id` and `s₂ ∘ δ₂ (i + 1) = δ₁ i ∘ s₁`, then the sequence is exact. -/
theorem exact_sum_of_extraCodegeneracy {n : ℕ} (δ₁ : Fin (n + 2) → V →ₗ[R] W)
    (δ₂ : Fin (n + 3) → W →ₗ[R] U) (s₁ : W →ₗ[R] V) (s₂ : U →ₗ[R] W)
    (h₀ : ∀ x, s₂ (δ₂ 0 x) = x) (hs : ∀ i x, s₂ (δ₂ i.succ x) = δ₁ i (s₁ x))
    (hcomp : (∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) • δ₂ i) ∘ₗ
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • δ₁ i) = 0) :
    Function.Exact (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • δ₁ i : V →ₗ[R] W)
      (∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) • δ₂ i : W →ₗ[R] U) := by
  rw [exact_iff]
  refine le_antisymm (fun y hy ↦ ⟨s₁ y, ?_⟩) (range_le_ker_iff.mpr hcomp)
  have key := congrArg s₂ (mem_ker.mp hy)
  rw [sum_apply, map_sum, Fin.sum_univ_succ, map_zero] at key
  have h (i : Fin (n + 2)) : s₂ (((-1 : ℤ) ^ ((i.succ : Fin (n + 3)) : ℕ) • δ₂ i.succ) y) =
      -((-1 : ℤ) ^ (i : ℕ) • δ₁ i) (s₁ y) := by
    rw [smul_apply, map_zsmul, hs, Fin.val_succ, pow_succ, mul_neg_one, neg_smul, smul_apply]
  rw [Finset.sum_congr rfl fun i _ ↦ h i, Finset.sum_neg_distrib, smul_apply, map_zsmul,
    Fin.val_zero, pow_zero, one_smul, h₀, add_neg_eq_zero] at key
  rw [sum_apply, ← key]

/-- Let `ε : V → W` be a map and `δ₀ - δ₁ : W → U` a difference of maps with
`(δ₀ - δ₁) ∘ ε = 0`. If there are maps `s₀ : U → W`, `s' : W → V` with `s₀ ∘ δ₀ = id` and
`s₀ ∘ δ₁ = ε ∘ s'`, then the sequence is exact. -/
theorem exact_sum_of_extraCodegeneracy_zero (ε : V →ₗ[R] W) (δ : Fin 2 → W →ₗ[R] U)
    (s₀ : U →ₗ[R] W) (s' : W →ₗ[R] V) (h₀ : ∀ x, s₀ (δ 0 x) = x)
    (h₁ : ∀ x, s₀ (δ 1 x) = ε (s' x))
    (hcomp : (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • δ i) ∘ₗ ε = 0) :
    Function.Exact ε (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • δ i : W →ₗ[R] U) := by
  rw [exact_iff]
  refine le_antisymm (fun y hy ↦ ⟨s' y, ?_⟩) (range_le_ker_iff.mpr hcomp)
  have key := congrArg s₀ (mem_ker.mp hy)
  rw [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_zsmul,
    add_apply, neg_apply, map_add, map_neg, h₀, h₁, map_zero, add_neg_eq_zero] at key
  exact key.symm

section BaseChange

variable {S P P' Q Q' : Type*} [CommRing S] [Algebra R S] [AddCommGroup P] [Module R P]
  [AddCommGroup P'] [Module R P'] [AddCommGroup Q] [Module R Q] [AddCommGroup Q'] [Module R Q']

/-- `f.lTensor S` is `S`-linear. -/
lemma lTensor_smul_apply (f : Q →ₗ[R] Q') (a : S) (x : S ⊗[R] Q) :
    f.lTensor S (a • x) = a • f.lTensor S x := by
  rw [← baseChange_eq_lTensor, map_smul]

/-- Compatibility of `S`-linear extensions of maps `P → S ⊗[R] Q` with base changes of maps. -/
lemma liftBaseChange_lTensor_apply {σ₁ : P →ₗ[R] S ⊗[R] Q} {σ₂ : P' →ₗ[R] S ⊗[R] Q'}
    {f : P →ₗ[R] P'} {g : Q →ₗ[R] Q'} (h : ∀ p, σ₂ (f p) = g.lTensor S (σ₁ p))
    (x : S ⊗[R] P) :
    σ₂.liftBaseChange S (f.lTensor S x) = g.lTensor S (σ₁.liftBaseChange S x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a p => rw [lTensor_tmul, liftBaseChange_tmul, liftBaseChange_tmul, h, lTensor_smul_apply]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

lemma liftBaseChange_mk_one_apply (x : S ⊗[R] Q) :
    (TensorProduct.mk R S Q 1).liftBaseChange S x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a q => rw [liftBaseChange_tmul, mk_apply, smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => rw [map_add, hx, hy]

end BaseChange

end LinearMap

namespace CategoryTheory.CosimplicialObject

variable {R : Type u} [CommRing R] (X : CosimplicialObject (ModuleCat.{u} R))
  (N : Type u) [AddCommGroup N] [Module R N]

/-- The differential of the alternating coface map complex, tensored with `N`, is the alternating
sum of the cofaces tensored with `N`. -/
lemma lTensor_alternatingCofaceMapComplex_d (n : ℕ) :
    (((alternatingCofaceMapComplex _).obj X).d n (n + 1)).hom.lTensor N =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (X.δ i).hom.lTensor N := by
  have h : ((alternatingCofaceMapComplex _).obj X).d n (n + 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • X.δ i :=
    CochainComplex.of_d (fun m ↦ X.obj ⦋m⦌) (AlternatingCofaceMapComplex.objD X) n
  let Φ : (X.obj ⦋n⦌ ⟶ X.obj ⦋n + 1⦌) →+
      (N ⊗[R] X.obj ⦋n⦌ →ₗ[R] N ⊗[R] X.obj ⦋n + 1⦌) :=
    (LinearMap.lTensorHom N).toAddMonoidHom.comp ModuleCat.homAddEquiv.toAddMonoidHom
  calc _ = Φ (((alternatingCofaceMapComplex _).obj X).d n (n + 1)) := rfl
    _ = Φ (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • X.δ i) := congrArg Φ h
    _ = _ := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ ↦ map_zsmul Φ _ _

/-- Let `X` be a cosimplicial `R`-module and `N` an `R`-module. If the cosimplicial module
`N ⊗[R] X` admits an extra codegeneracy `s`, i.e. maps `s : N ⊗ X⦋n + 1⦌ → N ⊗ X⦋n⦌` with
`s ∘ δ₀ = id` and `s ∘ δᵢ₊₁ = δᵢ ∘ s`, then the alternating coface map complex of `X` becomes
exact in positive degrees after tensoring with `N`. -/
theorem exact_lTensor_alternatingCofaceMapComplex_d
    (s : ∀ n : ℕ, N ⊗[R] X.obj ⦋n + 1⦌ →ₗ[R] N ⊗[R] X.obj ⦋n⦌)
    (hs₀ : ∀ n x, s n ((X.δ 0).hom.lTensor N x) = x)
    (hs : ∀ n (i : Fin (n + 2)) x,
      s (n + 1) ((X.δ i.succ).hom.lTensor N x) = (X.δ i).hom.lTensor N (s n x)) (n : ℕ) :
    Function.Exact ((((alternatingCofaceMapComplex _).obj X).d n (n + 1)).hom.lTensor N)
      ((((alternatingCofaceMapComplex _).obj X).d (n + 1) (n + 1 + 1)).hom.lTensor N) := by
  have hcomp := congrArg (fun f ↦ f.hom.lTensor N)
    (((alternatingCofaceMapComplex _).obj X).d_comp_d n (n + 1) (n + 1 + 1))
  simp only [ModuleCat.hom_comp, LinearMap.lTensor_comp, ModuleCat.hom_zero,
    LinearMap.lTensor_zero] at hcomp
  rw [lTensor_alternatingCofaceMapComplex_d, lTensor_alternatingCofaceMapComplex_d] at hcomp ⊢
  exact LinearMap.exact_sum_of_extraCodegeneracy (fun i ↦ (X.δ i).hom.lTensor N)
    (fun i ↦ (X.δ i).hom.lTensor N) (s n) (s (n + 1)) (hs₀ (n + 1)) (hs n) hcomp

/-- Let `X` be a cosimplicial `R`-module with an augmentation `ε : M' → X⦋0⦌`, and `N` an
`R`-module. If the augmented cosimplicial module `N ⊗[R] X` admits an extra codegeneracy in
degrees `0` and `-1`, i.e. maps `s₀ : N ⊗ X⦋1⦌ → N ⊗ X⦋0⦌` and `s' : N ⊗ X⦋0⦌ → N ⊗ M'` with
`s' ∘ ε = id`, `s₀ ∘ δ₀ = id` and `s₀ ∘ δ₁ = ε ∘ s'`, then `N ⊗ M' → N ⊗ X⦋0⦌ → N ⊗ X⦋1⦌` is
exact. -/
theorem exact_lTensor_augmentation {M' : Type*} [AddCommGroup M'] [Module R M']
    (ε : M' →ₗ[R] X.obj ⦋0⦌) (hε : (X.δ 0).hom ∘ₗ ε = (X.δ 1).hom ∘ₗ ε)
    (s₀ : N ⊗[R] X.obj ⦋1⦌ →ₗ[R] N ⊗[R] X.obj ⦋0⦌) (s' : N ⊗[R] X.obj ⦋0⦌ →ₗ[R] N ⊗[R] M')
    (h₀ : ∀ x, s₀ ((X.δ 0).hom.lTensor N x) = x)
    (h₁ : ∀ x, s₀ ((X.δ 1).hom.lTensor N x) = ε.lTensor N (s' x)) :
    Function.Exact (ε.lTensor N)
      ((((alternatingCofaceMapComplex _).obj X).d 0 1).hom.lTensor N) := by
  rw [lTensor_alternatingCofaceMapComplex_d X N 0]
  refine LinearMap.exact_sum_of_extraCodegeneracy_zero _ (fun i ↦ (X.δ i).hom.lTensor N) s₀ s'
    h₀ h₁ ?_
  rw [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_zsmul,
    ← sub_eq_add_neg, LinearMap.sub_comp, ← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp, hε,
    sub_self]

end CategoryTheory.CosimplicialObject

namespace Algebra.TensorProduct

open PiTensorProduct

section Amitsur

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- The algebra homomorphism `⨂_{ι} B → ⨂_{κ} B` induced by a map `θ : ι → κ`: it sends `b` in
the `i`-th factor to `b` in the `θ i`-th factor. -/
noncomputable def amitsurMap {ι κ : Type} [Fintype ι] [DecidableEq κ] (θ : ι → κ) :
    (⨂[A] _ : ι, B) →ₐ[A] ⨂[A] _ : κ, B :=
  liftCommAlgHom fun i ↦ singleAlgHom (R := A) (A := fun _ : κ ↦ B) (θ i)

@[simp]
lemma amitsurMap_comp_singleAlgHom {ι κ : Type} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (θ : ι → κ) (i : ι) :
    (amitsurMap A B θ).comp (singleAlgHom (R := A) (A := fun _ : ι ↦ B) i) =
      singleAlgHom (R := A) (A := fun _ : κ ↦ B) (θ i) := by
  rw [amitsurMap, liftCommAlgHom_comp_singleAlgHom]

lemma amitsurMap_eq_id {ι : Type} [Fintype ι] [DecidableEq ι] (θ : ι → ι) (hθ : ∀ i, θ i = i) :
    amitsurMap A B θ = AlgHom.id A _ :=
  algHom_ext fun i ↦ by rw [AlgHom.id_comp, amitsurMap_comp_singleAlgHom, hθ]

lemma amitsurMap_comp {ι κ ν : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] [DecidableEq ν]
    (θ : ι → κ) (θ' : κ → ν) :
    amitsurMap A B (θ' ∘ θ) = (amitsurMap A B θ').comp (amitsurMap A B θ) := by
  classical
  exact algHom_ext fun i ↦ by
    rw [AlgHom.comp_assoc, amitsurMap_comp_singleAlgHom, amitsurMap_comp_singleAlgHom,
      amitsurMap_comp_singleAlgHom, Function.comp_apply]

variable (M : Type u) [AddCommGroup M] [Module A M]

/-- The cosimplicial `A`-module `⦋k⦌ ↦ M ⊗[A] B^{⊗ (k + 1)}` whose cofaces insert `1` into one of
the tensor factors of `B`. -/
noncomputable def amitsurCosimplicialObject : CosimplicialObject (ModuleCat.{u} A) where
  obj k := ModuleCat.of A (M ⊗[A] (⨂[A] _ : Fin (k.len + 1), B))
  map θ := ModuleCat.ofHom ((amitsurMap A B θ.toOrderHom).toLinearMap.lTensor M)
  map_id k := by
    ext : 1
    rw [ModuleCat.hom_ofHom, SimplexCategory.id_toOrderHom, ModuleCat.hom_id,
      amitsurMap_eq_id A B (⇑OrderHom.id) fun _ ↦ rfl, AlgHom.toLinearMap_id,
      LinearMap.lTensor_id]
  map_comp θ θ' := by
    ext : 1
    rw [ModuleCat.hom_ofHom, SimplexCategory.comp_toOrderHom, ModuleCat.hom_comp,
      ModuleCat.hom_ofHom, ModuleCat.hom_ofHom, OrderHom.comp_coe, amitsurMap_comp,
      AlgHom.comp_toLinearMap, LinearMap.lTensor_comp]

/-- The Amitsur complex `M ⊗_A B → M ⊗_A B ⊗_A B → M ⊗_A B ⊗_A B ⊗_A B → ⋯` of the `A`-algebra
`B` with coefficients in the `A`-module `M`: the alternating coface map complex of
`amitsurCosimplicialObject A B M`. -/
noncomputable def amitsurComplex : CochainComplex (ModuleCat.{u} A) ℕ :=
  (alternatingCofaceMapComplex _).obj (amitsurCosimplicialObject A B M)

/-- The augmentation `M → M ⊗[A] B, m ↦ m ⊗ 1` of the Amitsur complex. -/
noncomputable def amitsurAugmentation : M →ₗ[A] M ⊗[A] (⨂[A] _ : Fin 1, B) :=
  (TensorProduct.mk A M _).flip 1

lemma amitsurCosimplicialObject_δ_hom {n : ℕ} (i : Fin (n + 2)) :
    ((amitsurCosimplicialObject A B M).δ i).hom =
      (amitsurMap A B i.succAbove).toLinearMap.lTensor M := by
  simp [CosimplicialObject.δ, amitsurCosimplicialObject, SimplexCategory.δ]

/-- The algebra homomorphism `B^{⊗ (n + 2)} → B ⊗[A] B^{⊗ (n + 1)}` sending
`b₀ ⊗ b₁ ⊗ ⋯ ⊗ bₙ₊₁` to `b₀ ⊗ (b₁ ⊗ ⋯ ⊗ bₙ₊₁)`. -/
noncomputable def amitsurSplitFirst (n : ℕ) :
    (⨂[A] _ : Fin (n + 2), B) →ₐ[A] B ⊗[A] (⨂[A] _ : Fin (n + 1), B) :=
  liftCommAlgHom (Fin.cases includeLeft fun j ↦
    includeRight.comp (singleAlgHom (R := A) (A := fun _ ↦ B) j))

@[simp]
lemma amitsurSplitFirst_comp_singleAlgHom_zero (n : ℕ) :
    (amitsurSplitFirst A B n).comp (singleAlgHom (R := A) (A := fun _ ↦ B) 0) = includeLeft := by
  rw [amitsurSplitFirst, liftCommAlgHom_comp_singleAlgHom, Fin.cases_zero]

@[simp]
lemma amitsurSplitFirst_comp_singleAlgHom_succ (n : ℕ) (j : Fin (n + 1)) :
    (amitsurSplitFirst A B n).comp (singleAlgHom (R := A) (A := fun _ ↦ B) j.succ) =
      includeRight.comp (singleAlgHom (R := A) (A := fun _ ↦ B) j) := by
  rw [amitsurSplitFirst, liftCommAlgHom_comp_singleAlgHom, Fin.cases_succ]

lemma amitsurSplitFirst_comp_amitsurMap_succAbove_zero (n : ℕ) :
    (amitsurSplitFirst A B n).comp (amitsurMap A B (Fin.succAbove 0)) = includeRight :=
  algHom_ext fun j ↦ by
    rw [AlgHom.comp_assoc, amitsurMap_comp_singleAlgHom, Fin.succAbove_zero,
      amitsurSplitFirst_comp_singleAlgHom_succ]

lemma amitsurSplitFirst_comp_amitsurMap_succAbove_succ (n : ℕ) (i : Fin (n + 2)) :
    (amitsurSplitFirst A B (n + 1)).comp (amitsurMap A B i.succ.succAbove) =
      (map (AlgHom.id A B) (amitsurMap A B i.succAbove)).comp (amitsurSplitFirst A B n) :=
  algHom_ext fun j ↦ by
    rw [AlgHom.comp_assoc, AlgHom.comp_assoc, amitsurMap_comp_singleAlgHom]
    cases j using Fin.cases with
    | zero =>
      rw [Fin.succ_succAbove_zero, amitsurSplitFirst_comp_singleAlgHom_zero,
        amitsurSplitFirst_comp_singleAlgHom_zero, map_comp_includeLeft, AlgHom.comp_id]
    | succ j =>
      rw [Fin.succ_succAbove_succ, amitsurSplitFirst_comp_singleAlgHom_succ,
        amitsurSplitFirst_comp_singleAlgHom_succ, ← AlgHom.comp_assoc, map_comp_includeRight,
        AlgHom.comp_assoc, amitsurMap_comp_singleAlgHom]

/-- The multiplication map `B^{⊗ 1} → B`. -/
noncomputable def amitsurMulOne : (⨂[A] _ : Fin 1, B) →ₐ[A] B :=
  liftCommAlgHom fun _ ↦ AlgHom.id A B

lemma amitsurSplitFirst_comp_amitsurMap_succAbove_one :
    (amitsurSplitFirst A B 0).comp (amitsurMap A B (Fin.succAbove 1)) =
      includeLeft.comp (amitsurMulOne A B) :=
  algHom_ext fun j ↦ by
    rw [AlgHom.comp_assoc, AlgHom.comp_assoc, amitsurMap_comp_singleAlgHom, Fin.fin_one_eq_zero j,
      amitsurMulOne, liftCommAlgHom_comp_singleAlgHom, AlgHom.comp_id]
    exact amitsurSplitFirst_comp_singleAlgHom_zero A B 0

variable (M : Type u) [AddCommGroup M] [Module A M]

/-- The map `M ⊗ B^{⊗ (n + 2)} → B ⊗ (M ⊗ B^{⊗ (n + 1)})`,
`m ⊗ b₀ ⊗ ⋯ ⊗ bₙ₊₁ ↦ b₀ ⊗ m ⊗ b₁ ⊗ ⋯ ⊗ bₙ₊₁`. -/
noncomputable def amitsurSplitFirstAux (n : ℕ) :
    M ⊗[A] (⨂[A] _ : Fin (n + 2), B) →ₗ[A] B ⊗[A] (M ⊗[A] (⨂[A] _ : Fin (n + 1), B)) :=
  (_root_.TensorProduct.leftComm A M B _).toLinearMap ∘ₗ
    (amitsurSplitFirst A B n).toLinearMap.lTensor M

/-- The contracting homotopy `B ⊗ M ⊗ B^{⊗ (n + 2)} → B ⊗ M ⊗ B^{⊗ (n + 1)}` of the Amitsur
complex tensored with `B`, `b ⊗ m ⊗ b₀ ⊗ ⋯ ⊗ bₙ₊₁ ↦ b b₀ ⊗ m ⊗ b₁ ⊗ ⋯ ⊗ bₙ₊₁`. -/
noncomputable def amitsurCodegeneracy (n : ℕ) :
    B ⊗[A] (M ⊗[A] (⨂[A] _ : Fin (n + 2), B)) →ₗ[A]
      B ⊗[A] (M ⊗[A] (⨂[A] _ : Fin (n + 1), B)) :=
  ((amitsurSplitFirstAux A B M n).liftBaseChange B).restrictScalars A

/-- The contracting homotopy `B ⊗ M ⊗ B → B ⊗ M`, `b ⊗ m ⊗ b₀ ↦ b b₀ ⊗ m` of the augmented
Amitsur complex tensored with `B`, in degree `0`. -/
noncomputable def amitsurCodegeneracyAugmentation :
    B ⊗[A] (M ⊗[A] (⨂[A] _ : Fin 1, B)) →ₗ[A] B ⊗[A] M :=
  (((_root_.TensorProduct.comm A M B).toLinearMap ∘ₗ
    (amitsurMulOne A B).toLinearMap.lTensor M).liftBaseChange B).restrictScalars A

lemma amitsurSplitFirstAux_tmul (n : ℕ) (m : M) (t : ⨂[A] _ : Fin (n + 2), B) :
    amitsurSplitFirstAux A B M n (m ⊗ₜ t) =
      _root_.TensorProduct.leftComm A M B _ (m ⊗ₜ amitsurSplitFirst A B n t) :=
  rfl

lemma amitsurCodegeneracy_δ_zero (n : ℕ)
    (x : B ⊗[A] (M ⊗[A] (⨂[A] _ : Fin (n + 1), B))) :
    amitsurCodegeneracy A B M n
      (((amitsurMap A B (Fin.succAbove 0)).toLinearMap.lTensor M).lTensor B x) = x := by
  rw [amitsurCodegeneracy, LinearMap.restrictScalars_apply,
    LinearMap.liftBaseChange_lTensor_apply (σ₁ := _root_.TensorProduct.mk A B _ 1)
      (g := LinearMap.id), LinearMap.lTensor_id, LinearMap.id_apply,
    LinearMap.liftBaseChange_mk_one_apply]
  intro p
  rw [LinearMap.lTensor_id, LinearMap.id_apply, mk_apply]
  induction p using TensorProduct.inductionOn with
  | tmul m t =>
    rw [LinearMap.lTensor_tmul, amitsurSplitFirstAux_tmul, AlgHom.toLinearMap_apply,
      ← AlgHom.comp_apply, amitsurSplitFirst_comp_amitsurMap_succAbove_zero, includeRight_apply,
      _root_.TensorProduct.leftComm_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, tmul_add]

lemma amitsurCodegeneracy_δ_succ (n : ℕ) (i : Fin (n + 2))
    (x : B ⊗[A] (M ⊗[A] (⨂[A] _ : Fin (n + 2), B))) :
    amitsurCodegeneracy A B M (n + 1)
      (((amitsurMap A B i.succ.succAbove).toLinearMap.lTensor M).lTensor B x) =
      ((amitsurMap A B i.succAbove).toLinearMap.lTensor M).lTensor B
        (amitsurCodegeneracy A B M n x) := by
  rw [amitsurCodegeneracy, amitsurCodegeneracy, LinearMap.restrictScalars_apply,
    LinearMap.restrictScalars_apply]
  refine LinearMap.liftBaseChange_lTensor_apply (fun p ↦ ?_) x
  induction p using TensorProduct.inductionOn with
  | tmul m t =>
    rw [LinearMap.lTensor_tmul, amitsurSplitFirstAux_tmul, amitsurSplitFirstAux_tmul,
      AlgHom.toLinearMap_apply, ← AlgHom.comp_apply,
      amitsurSplitFirst_comp_amitsurMap_succAbove_succ, AlgHom.comp_apply]
    induction amitsurSplitFirst A B n t using TensorProduct.inductionOn with
    | tmul b t' =>
      rw [map_tmul, _root_.TensorProduct.leftComm_tmul, _root_.TensorProduct.leftComm_tmul,
        LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, AlgHom.id_apply,
        AlgHom.toLinearMap_apply]
    | add z z' hz hz' => rw [map_add, tmul_add, map_add, hz, hz', tmul_add, map_add, map_add]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

lemma amitsurCodegeneracy_δ_one (x : B ⊗[A] (M ⊗[A] (⨂[A] _ : Fin 1, B))) :
    amitsurCodegeneracy A B M 0
      (((amitsurMap A B (Fin.succAbove 1)).toLinearMap.lTensor M).lTensor B x) =
      (amitsurAugmentation A B M).lTensor B (amitsurCodegeneracyAugmentation A B M x) := by
  rw [amitsurCodegeneracy, amitsurCodegeneracyAugmentation, LinearMap.restrictScalars_apply,
    LinearMap.restrictScalars_apply]
  refine LinearMap.liftBaseChange_lTensor_apply (fun p ↦ ?_) x
  induction p using TensorProduct.inductionOn with
  | tmul m t =>
    rw [LinearMap.lTensor_tmul, amitsurSplitFirstAux_tmul, AlgHom.toLinearMap_apply,
      ← AlgHom.comp_apply, amitsurSplitFirst_comp_amitsurMap_succAbove_one, AlgHom.comp_apply,
      includeLeft_apply, _root_.TensorProduct.leftComm_tmul, LinearMap.comp_apply,
      LinearMap.lTensor_tmul, LinearEquiv.coe_coe, _root_.TensorProduct.comm_tmul,
      LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

lemma amitsurCodegeneracyAugmentation_augmentation (x : B ⊗[A] M) :
    amitsurCodegeneracyAugmentation A B M ((amitsurAugmentation A B M).lTensor B x) = x := by
  rw [amitsurCodegeneracyAugmentation, LinearMap.restrictScalars_apply,
    LinearMap.liftBaseChange_lTensor_apply (σ₁ := _root_.TensorProduct.mk A B M 1)
      (g := LinearMap.id), LinearMap.lTensor_id, LinearMap.id_apply,
    LinearMap.liftBaseChange_mk_one_apply]
  intro m
  rw [LinearMap.lTensor_id, LinearMap.id_apply, mk_apply, amitsurAugmentation,
    LinearMap.flip_apply, mk_apply, LinearMap.comp_apply, LinearMap.lTensor_tmul,
    AlgHom.toLinearMap_apply, map_one, LinearEquiv.coe_coe, _root_.TensorProduct.comm_tmul]

lemma amitsurMap_comp_augmentation {n : ℕ} (θ : Fin 1 → Fin (n + 1)) :
    (amitsurMap A B θ).toLinearMap.lTensor M ∘ₗ amitsurAugmentation A B M =
      (_root_.TensorProduct.mk A M _).flip 1 :=
  LinearMap.ext fun m ↦ by simp [amitsurAugmentation]

end Amitsur

end Algebra.TensorProduct

namespace Module.FaithfullyFlat

open Algebra.TensorProduct CosimplicialObject

variable (A B M : Type u) [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module A M]

/-- The augmented Amitsur complex `0 → M → M ⊗_A B → M ⊗_A B ⊗_A B → ⋯` of a faithfully flat
`A`-algebra `B` is exact (blueprint: proposition-p-torsion-smooth-proper-curve): the augmentation
`M → M ⊗_A B` is injective, the complex is exact at `M ⊗_A B` (the kernel of the first differential
is the image of the augmentation), and the Amitsur complex `amitsurComplex A B M` is exact in all
positive degrees.

The proof follows the classical argument: after tensoring with `B`, the augmented complex admits
the contracting homotopy `b ⊗ m ⊗ b₀ ⊗ ⋯ ⊗ bₙ ↦ b b₀ ⊗ m ⊗ b₁ ⊗ ⋯ ⊗ bₙ`, so it is exact, and
exactness descends along the faithfully flat map `A → B`. -/
theorem exact_amitsurComplex [Module.FaithfullyFlat A B] :
    Function.Injective (amitsurAugmentation A B M) ∧
      Function.Exact (amitsurAugmentation A B M) ((amitsurComplex A B M).d 0 1).hom ∧
      ∀ q, (amitsurComplex A B M).ExactAt (q + 1) := by
  refine ⟨?_, ?_, fun q ↦ ?_⟩
  · rw [← lTensor_injective_iff_injective A B]
    exact Function.LeftInverse.injective (amitsurCodegeneracyAugmentation_augmentation A B M)
  · refine (lTensor_exact_iff_exact A B _ _).mp ?_
    exact exact_lTensor_augmentation (amitsurCosimplicialObject A B M) B
      (amitsurAugmentation A B M)
      ((amitsurMap_comp_augmentation A B M _).trans (amitsurMap_comp_augmentation A B M _).symm)
      (amitsurCodegeneracy A B M 0) (amitsurCodegeneracyAugmentation A B M)
      (amitsurCodegeneracy_δ_zero A B M 0) (amitsurCodegeneracy_δ_one A B M)
  · rw [HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 1 + 1) (by simp) (by simp),
      ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    refine (lTensor_exact_iff_exact A B _ _).mp ?_
    exact exact_lTensor_alternatingCofaceMapComplex_d (amitsurCosimplicialObject A B M) B
      (amitsurCodegeneracy A B M) (amitsurCodegeneracy_δ_zero A B M)
      (amitsurCodegeneracy_δ_succ A B M) q

end Module.FaithfullyFlat

end
